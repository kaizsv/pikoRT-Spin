#include "variables.pml"
#include "helper.pml"
#include "ti.pml"
#include "sched.pml"
#include "softirq.pml"
#include "mutex.pml"
#include "cond.pml"

#ifdef LTL
#include "specifications.pml"
#endif

bit data_ready, cs_c, cs_p;

#define get_pending(irq, pending) get_bit(irq - 2, pending)

inline set_pending(irq, pending)
{
    assert(PendSV < irq && irq < USER0);
    set_bit(irq - 2, pending)
}

inline clear_pending(irq, pending)
{
    assert(PendSV < irq && irq < USER0);
    clear_bit(irq - 2, pending)
}

/* return maxima exception priority from pending status. If the exception
 * has same priority, return the smaller exception number first.
 * http://infocenter.arm.com/help/index.jsp?topic=/com.arm.doc.dui0552a/BABICDEB.html
 */
inline get_max_pending(ret)
{
    assert(ret == UNKNOWN);
    /* SVC will not be pending, and pending of PendSV has no effect here */
    for (idx: 2 .. (USER0 - 1)) {
        if
        :: get_pending(idx, irq_pending) && ret == UNKNOWN ->
            ret = idx
        :: get_pending(idx, irq_pending) && (irq_prio[idx] < irq_prio[ret]) ->
            ret = idx
        :: else
        fi
    }
    idx = 0;
    /* always has a max priority exception */
    assert(ret != UNKNOWN)
}

/* similar to tail-chaining */
inline change_AT_directly(proc)
{
    assert(PendSV < proc && proc < USER0);
    assert(ghost_direct_AT < (1 << (proc - 2)));
    set_pending(proc, ghost_direct_AT);
    AT = proc
}

inline push_and_change_AT(proc)
{
    /* XXX: this might be false if SOFTIRQ is greater than 7 */
    ATTop = ATTop + 1;
    assert(ATTop < NBATSTACK);
    ATStack[ATTop] = AT;
    AT = proc
}

inline pop_ATStack_to_AT()
{
    AT = ATStack[ATTop];
    ATStack[ATTop] = UNKNOWN;
    assert(ATTop >= 0);
    ATTop = ATTop - 1
}

// XXX: We can not simulate the exception preempts itself on Spin.
//      If the coming task had been executed (in ATStack), it will be wrong.
inline inATStack(proc)
{
    FOR_ATTOP_IDX {
        if
        :: ATStack[idx] == proc -> assert(false)
        :: else
        fi
    }
    idx = 0
}

/* return true if preemption can preempt the running task, and
 * false otherwise. */
inline interrupt_policy(preempt, running, ret)
{
    if
    :: preempt == running ->
        /* XXX: The irq is triggered by the running of process. It will not
         * trigger again while the related interrupt process are running. */
        assert(PendSV < preempt && preempt < USER0);
        assert(get_pending(preempt, ghost_direct_AT));
        /* the preemption can not be self */
        assert(ret == false)
    :: running >= USER0 ->
        /* the exception always takes while user task is running
         * and there remain nothing in ATStack */
        assert(ATTop <= 0 && preempt != SVC);
        /* if PendSV preempt user task, setting the pending bit of PendSV
         * has no side-effect */
        set_pending(preempt, irq_pending);
        ret = true
    :: else ->
        /* nested interrupt: running < USER0
         * compare the priority of pending and preemtive exception */
        assert(ret == false && !get_pending(preempt, ghost_direct_AT));
        set_pending(preempt, irq_pending);
        if
        :: irq_prio[preempt] < irq_prio[running] ->
            /* preempt directly, and not from irq_pending */
            ret = true
        :: else
        fi
    fi
}

inline ITake(proc)
{
    do
    :: atomic {
        d_step { interrupt_policy(proc, AT, retPolicy) };
        if
        :: retPolicy ->
            d_step {
                inATStack(proc);
                retPolicy = false;
                clear_pending(proc, irq_pending);
                /* late arrival
                 * current process AT is changed by change_AT_directly and been
                 * preempt by higher priority exception, however, AT has not
                 * process the ITake to clear the ghost bit. Thus, can not push
                 * to the ATStack. */
                if
                :: PendSV < AT && AT < USER0 && get_pending(AT, ghost_direct_AT) ->
                    clear_pending(AT, ghost_direct_AT);
                    AT = proc
                :: else ->
                    push_and_change_AT(proc)
                fi
            }; break
        :: !retPolicy && get_pending(proc, ghost_direct_AT) ->
            /* change AT directly from IRet or irq_pending from
             * interrupt_policy, similar to tail-chaining */
            d_step {
                inATStack(proc);
                clear_pending(proc, ghost_direct_AT);
                clear_pending(proc, irq_pending)
            }; break
        :: else
        fi }
    od
}

inline PendSVTake()
{
    do
    :: atomic {
        if
        :: PendSV_pending && (AT >= USER0) ->
            d_step {
                inATStack(PendSV);
                assert(ATTop <= 0);
                push_and_change_AT(PendSV);
                PendSV_pending = 0
            }; break
        :: else
        fi }
    od
}

inline IRet()
{
    assert(retPolicy == false);
    if
    :: irq_pending != 0 ->
        /* ignore SVC and PendSV */
        get_max_pending(max_prio);
        /* interrupt_policy(max_prio, ATStack[ATTop], retPolicy) */
        if
        :: max_prio == ATStack[ATTop] -> assert(false)
        :: ATStack[ATTop] >= USER0 -> retPolicy = true
        :: irq_prio[max_prio] < irq_prio[ATStack[ATTop]] ->
            assert(!get_pending(max_prio, ghost_direct_AT)); retPolicy = true
        :: else
        fi
    :: else -> assert(max_prio == UNKNOWN)
    fi;
    if
    :: retPolicy ->
        change_AT_directly(max_prio); retPolicy = false
    :: else ->
        pop_ATStack_to_AT()
    fi;
    max_prio = UNKNOWN;
    /**
    * reset local monitor: 14.1.7. Exclusive monitor system location
    * B1.5.8 Exception return behavior
    */
    local_monitor = 0
}

inline sys_call(__svc_type, __svc_chan)
{
    d_step {
        assert(ATTop < 0 && irq_pending == 0 && ghost_direct_AT == 0);
        push_and_change_AT(SVC)
    };

    /* rendezvous chan will block the process, need to place outside d_step */
    __svc_chan ! __svc_type;
    (evalPID == AT)
}

/* -------------
 * all processes
 * ------------ */

proctype svc(chan svc_chan)
{
    byte idx, max_prio = UNKNOWN, nextUser = UNKNOWN;
    bool retPolicy, del_queue_check;
    mutex_head mutex_list;
    cond_head cond_list;
    mtype:svc_t svc_type;
    assert(evalPID == SVC);
loop:
    svc_chan ? svc_type;
    if
    :: SELE(evalPID, svc_type == SYS_MUTEX_LOCK) ->
        sys_pthread_mutex_lock(evalPID)
    :: SELE(evalPID, svc_type == SYS_MUTEX_UNLOCK) ->
        sys_pthread_mutex_unlock(evalPID)
    :: SELE(evalPID, svc_type == SYS_COND_WAIT) ->
        sys_pthread_cond_wait(evalPID)
    :: SELE(evalPID, svc_type == SYS_COND_SIGNAL) ->
        sys_pthread_cond_signal(evalPID)
    :: SELE(evalPID, svc_type == SYS_PTHREAD_YIELD) ->
        sched_enqueue(curUser, evalPID);
        sched_elect(SCHED_OPT_NONE, evalPID)
    :: SELE(evalPID, svc_type == SYS_PSEUDO_SLEEP) ->
        /* XXX: To simplify, only producer can be move out of runqueue. */
        AWAITS(evalPID, sys_pseudo_timer = 1);
        sched_dequeue(USER0 + 1, evalPID);
        sched_elect(SCHED_OPT_NONE, evalPID)
    fi;
    AWAITS(evalPID, IRet());

    goto loop
}

proctype pendsv()
{
    byte idx, max_prio = UNKNOWN, nextUser = UNKNOWN;
    bool retPolicy, del_queue_check;
    assert(evalPID == PendSV);
loop:
    PendSVTake();
    sched_elect(SCHED_OPT_TICK, evalPID);
    AWAITS(evalPID, IRet());

    goto loop
}

proctype systick()
{
    byte idx, max_prio = UNKNOWN;
    bool retPolicy, softirq_run;
    assert(PendSV < evalPID && evalPID < USER0);
loop:
    ITake(evalPID);
    tasklet_schedule(BH_SYSTICK, TIMER_SOFTIRQ_PRIO, evalPID);
    AWAITS(evalPID, PendSV_pending = 1);
iret:
    AWAITS(evalPID, IRet());

    goto loop
}

proctype interrupts()
{
    byte idx, max_prio = UNKNOWN;
    bool retPolicy;
    assert(PendSV < evalPID && evalPID < USER0);
loop:
    ITake(evalPID);
    /* using stm32_uartx_isr() as interrupt example
     * this isr will not influence the scheduling behavior
     * only updates charactor buffer and calls an empty callback func */
    skip;
iret:
    AWAITS(evalPID, IRet());

    goto loop
}

proctype consumer(chan svc_chan)
{
    bit ne;
    assert(USER0 <= evalPID && evalPID < SOFTIRQ);
loop:
    mutex_lock(mutex, cs_c, svc_chan, evalPID);
    do
    :: A_AWAITS(evalPID,
        if
        :: !data_ready ->
            cs_c = 0; sys_call(SYS_COND_WAIT, svc_chan);
            sys_call(SYS_MUTEX_LOCK, svc_chan); cs_c = 1
        :: else -> break
        fi )
    od;
cs:
    A_AWAITS(evalPID, d_step { assert(!cs_p); data_ready = 0 } );
    A_AWAITS(evalPID, assert(!cs_p); sys_call(SYS_COND_SIGNAL, svc_chan));
    mutex_unlock(mutex, cs_c, svc_chan, evalPID);

    goto loop
}

proctype producer(chan svc_chan)
{
    bit ne;
    assert(USER0 <= evalPID && evalPID < SOFTIRQ);
loop:
    A_AWAITS(evalPID, sys_call(SYS_PSEUDO_SLEEP, svc_chan));
    mutex_lock(mutex, cs_p, svc_chan, evalPID);
    do
    :: A_AWAITS(evalPID,
        if
        :: data_ready ->
            cs_p = 0; sys_call(SYS_COND_WAIT, svc_chan);
            sys_call(SYS_MUTEX_LOCK, svc_chan); cs_p = 1
        :: else -> break
        fi )
    od;
cs:
    A_AWAITS(evalPID, d_step { assert(!cs_c); data_ready = 1 } );
    A_AWAITS(evalPID, assert(!cs_c); sys_call(SYS_COND_SIGNAL, svc_chan));
    mutex_unlock(mutex, cs_p, svc_chan, evalPID);

    goto loop
}

/* softirq is in non-privileged mode */
proctype softirq(chan svc_chan)
{
    byte idx, max_prio;
    bool del_queue_check;
    mtype:tasklet_t next_tasklet = NO_BH_TASK;
    assert(evalPID == SOFTIRQ);
loop:
    tasklet_action(next_tasklet, evalPID);
    /* softirqd thread should not return */
    /* sched yield */
    A_AWAITS(evalPID, assert(next_tasklet == NO_BH_TASK); sys_call(SYS_PTHREAD_YIELD, svc_chan));

    goto loop
}

init
{
    byte idx, idx2;
    chan svc_chan = [0] of { mtype:svc_t };

    d_step {
        system_initialize();
        thread_info_initialize()
    };

    atomic {
        run svc(svc_chan);
        run pendsv();
        for (idx: 2 .. (USER0 - 1)) {
            if
            :: idx == (PendSV + 1) -> run systick()
            :: else -> run interrupts()
            fi
        }
        idx = 0;
        for (idx: USER0 .. (USER0 + NBUSERS - 1)) {
            if
            :: idx == USER0 -> run consumer(svc_chan)
            :: idx == (USER0 + 1) -> run producer(svc_chan)
            fi
        }
        idx = 0;
        run softirq(svc_chan)
    }
}
