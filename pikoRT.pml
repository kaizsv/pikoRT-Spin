#include "variables.pml"
#include "helper.pml"
#include "ti.pml"
#include "sched.pml"
#include "softirq.pml"
#include "mutex.pml"
#include "cond.pml"

#ifdef LTL
#include "pikoRT.prp"
#endif

bit data_ready, cs_c, cs_p;

inline set_pending(irq)
{
    assert(PendSV < irq && irq < USER0);
    set_bit(irq - 2, irq_pending)
}

inline clear_pending(irq)
{
    assert(PendSV < irq && irq < USER0);
    clear_bit(irq - 2, irq_pending)
}

/* return maxima exception priority from pending status. If the exception
 * has same priority, return the smaller exception number first.
 * http://infocenter.arm.com/help/index.jsp?topic=/com.arm.doc.dui0552a/BABICDEB.html
 */
inline get_max_pending(ret)
{
    ret = UNKNOWN;
    /* SVC will not be pending, and pending of PendSV has no effect here */
    for (idx: 2 .. (USER0 - 1)) {
        if
        :: get_bit(idx - 2, irq_pending) && ret == UNKNOWN ->
            ret = idx
        :: get_bit(idx - 2, irq_pending) && (irq_prio[idx] < irq_prio[ret]) ->
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
    set_bit(proc - 2, ghost_direct_AT);
    AT = proc
}

inline push_and_change_AT(proc)
{
    if
    :: PendSV < AT && AT < USER0 && get_bit(AT - 2, ghost_direct_AT) ->
        /* late arrival
         * current process AT is changed by change_AT_directly and been
         * preempt by higher priority exception, however, AT has not
         * process the ITake to clear the ghost bit. Thus, can not push
         * to the ATStack. */
        clear_bit(AT - 2, ghost_direct_AT);
        AT = proc
    :: else ->
        /* XXX: this might be false if SOFTIRQ is greater than 7 */
        ATTop = ATTop + 1;
        assert(ATTop < NBATSTACK);
        ATStack[ATTop] = AT;
        AT = proc
    fi
}

inline pop_ATStack_to_AT()
{
    AT = ATStack[ATTop];
    ATStack[ATTop] = UNKNOWN;
    assert(ATTop >= 0);
    ATTop = ATTop - 1
}

/* check if proc is active or not */
inline inATStack(proc, ret)
{
    ret = false;
    FOR_ATTOP_IDX {
        if
        :: ATStack[idx] == proc ->
            ret = true; break
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
        /* XXX
         * The limitation of this model is that, the irq is triggered by
         * the running of process. The irq will not trigger again while
         * the related interrupt process are running. */
        assert(PendSV < preempt && preempt < USER0);
        assert(get_bit(preempt - 2, ghost_direct_AT));
        /* the preemption can not be self */
        ret = false
    :: running >= USER0 ->
        /* the exception always takes while user task is running
         * and there remain nothing in ATStack */
        assert(ATTop <= 0 && preempt != SVC);
        /* if PendSV preempt user task, setting the pending bit of PendSV
         * has no side-effect */
        set_pending(preempt);
        ret = true
    :: else ->
        /* nested interrupt: running < USER0
         * compare the priority of pending and preemtive exception */
        set_pending(preempt);
        get_max_pending(max_prio);
        if
        :: irq_prio[max_prio] < irq_prio[running] ->
            /* preempt directly, and not from irq_pending */
            assert(!get_bit(preempt - 2, ghost_direct_AT) && preempt == max_prio);
            ret = true
        :: else ->
            ret = false
        fi
    fi
}

inline ITake(proc)
{
    do
    :: atomic {
        d_step {
            inATStack(proc, retInATStack);
            interrupt_policy(proc, AT, retPolicy)
        };
        if
        :: !retInATStack && retPolicy ->
            d_step {
                clear_pending(proc);
                push_and_change_AT(proc)
            }; break
        :: !retInATStack && get_bit(proc - 2, ghost_direct_AT) ->
            /* change AT directly from IRet or irq_pending from
             * interrupt_policy, similar to tail-chaining */
            d_step {
                clear_bit(proc - 2, ghost_direct_AT);
                clear_pending(proc)
            }; break
        :: else
        fi }
    od
}

inline PendSVTake()
{
    do
    :: atomic {
        d_step {
            inATStack(PendSV, retInATStack)
        };
        if
        :: PendSV_pending && !retInATStack && (AT >= USER0) ->
            d_step {
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
    if
    :: irq_pending != 0 ->
        /* ignore SVC and PendSV */
        get_max_pending(max_prio);
        assert(max_prio != PendSV);
        inATStack(max_prio, retInATStack);
        interrupt_policy(max_prio, ATStack[ATTop], retPolicy);
        if
        :: !retInATStack && retPolicy ->
            change_AT_directly(max_prio)
        :: else ->
            pop_ATStack_to_AT()
        fi
    :: else ->
        pop_ATStack_to_AT()
    fi;
    /**
    * reset local monitor: 14.1.7. Exclusive monitor system location
    * B1.5.8 Exception return behavior
    */
    local_monitor = 0
}

/* -------------
 * all processes
 * ------------ */

proctype svc()
{
    byte idx, max_prio, nextUser;
    bool retInATStack, retPolicy, del_queue_check;
    mutex_head mutex_list;
    cond_head cond_list;
    mtype:svc_t svc_type;
    assert(evalPID == SVC);
endSVC:
    svc_chan ? svc_type;
    if
    :: svc_type == SYS_MUTEX_LOCK ->
        sys_pthread_mutex_lock(evalPID)
    :: svc_type == SYS_MUTEX_UNLOCK ->
        sys_pthread_mutex_unlock(evalPID)
    :: svc_type == SYS_COND_WAIT ->
        sys_pthread_cond_wait(evalPID)
    :: svc_type == SYS_COND_SIGNAL ->
        sys_pthread_cond_signal(evalPID)
    :: svc_type == SYS_PTHREAD_YIELD ->
        sched_enqueue(curUser, evalPID);
        sched_elect(SCHED_OPT_NONE, evalPID)
    fi;
    AWAITS(evalPID, IRet());

    goto endSVC
}

proctype pendsv()
{
    byte idx, max_prio, nextUser;
    bool retInATStack, retPolicy, del_queue_check;
    assert(evalPID == PendSV);
endPendSV:
    PendSVTake();
    sched_elect(SCHED_OPT_TICK, evalPID);
    AWAITS(evalPID, IRet());

    goto endPendSV
}

proctype systick()
{
    byte idx, max_prio;
    bool retInATStack, retPolicy, softirq_run;
    assert(PendSV < evalPID && evalPID < USER0);
endSystick:
    ITake(evalPID);
    tasklet_schedule(BH_SYSTICK, TIMER_SOFTIRQ_PRIO, evalPID);
    AWAITS(evalPID, PendSV_pending = 1)
    AWAITS(evalPID, IRet());

    goto endSystick
}

proctype interrupts()
{
    byte idx, max_prio;
    bool retInATStack, retPolicy;
    assert(PendSV < evalPID && evalPID < USER0);
endInts:
    ITake(evalPID);
    /* using stm32_uartx_isr() as interrupt example
     * this isr will not influence the scheduling behavior
     * only updates charactor buffer and calls an empty callback func */
    A_AWAITS(evalPID, skip)
    AWAITS(evalPID, IRet());

    goto endInts
}

proctype consumer()
{
    bit ne;
    assert(USER0 <= evalPID && evalPID < SOFTIRQ);
wantConsumer:
    mutex_lock(mutex, evalPID);
    do
    :: A_AWAITS(evalPID,
        if
        :: !data_ready ->
            sys_call(SYS_COND_WAIT);
            sys_call(SYS_MUTEX_LOCK)
        :: else -> break
        fi )
    od;
inCS:
    A_AWAITS(evalPID, assert(!cs_p); cs_c = 1; data_ready = 0);
    A_AWAITS(evalPID, assert(!cs_p); cs_c = 0; sys_call(SYS_COND_SIGNAL));
    mutex_unlock(mutex, evalPID);

    goto wantConsumer
}

proctype producer()
{
    bit ne;
    assert(USER0 <= evalPID && evalPID < SOFTIRQ);
wantProducer:
    mutex_lock(mutex, evalPID);
    do
    :: A_AWAITS(evalPID,
        if
        :: data_ready ->
            sys_call(SYS_COND_WAIT);
            sys_call(SYS_MUTEX_LOCK)
        :: else -> break
        fi )
    od;
inCS:
    A_AWAITS(evalPID, assert(!cs_c); cs_p = 1; data_ready = 1);
    A_AWAITS(evalPID, assert(!cs_c); cs_p = 0; sys_call(SYS_COND_SIGNAL));
    mutex_unlock(mutex, evalPID);

    goto wantProducer
}

/* softirq is in non-privileged mode */
proctype softirq()
{
    byte idx, max_prio, next_tasklet = NO_BH_TASK;
    bool del_queue_check;
    assert(evalPID == SOFTIRQ);
endSoftirq:
    tasklet_action(next_tasklet, evalPID);
    /* softirqd thread should not return */
    /* sched yield */
    A_AWAITS(evalPID, assert(next_tasklet == NO_BH_TASK); sys_call(SYS_PTHREAD_YIELD));

    goto endSoftirq
}

init
{
    byte idx;

    d_step {
        system_initialize();
        thread_info_initialize();
        mutex_initialize()
    };

    atomic {
        run svc();
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
            :: idx == USER0 -> run consumer()
            :: idx == (USER0 + 1) -> run producer()
            fi
        }
        idx = 0;
        run softirq()
    }
}
