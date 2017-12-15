#include "variables.pml"
#include "helper.pml"
#include "ti.pml"
#include "sched.pml"
#include "softirq.pml"
#include "mutex.pml"

bit all_process_prepare_to_run;

inline set_pending(irq)
{
    assert(1 <= irq && irq < USER0);
    set_bit(irq, irq_pending)
}

inline clear_pending(irq)
{
    assert(1 <= irq && irq < USER0);
    clear_bit(irq, irq_pending)
}

/* return maxima priority exception from exception pending status
 * if the exception has same priority, then smaller exception number
 * return first.
 * http://infocenter.arm.com/help/index.jsp?topic=/com.arm.doc.dui0552a/BABICDEB.html
 */
inline get_max_pending(ret)
{
    d_step {
        ret = UNKNOWN;
        /* SVC will not be pending, and pending of PendSV has no effect */
        for (idx: 1 .. (USER0 - 1)) {
            if
            :: get_bit(idx, irq_pending) && (irq_prio[idx] < ret) ->
                ret = idx
            :: else -> skip
            fi
        }
        idx = 0;
        /* always has a max priority exception */
        assert(ret != UNKNOWN)
    }
}

/* similar to tail-chaining */
inline change_AT_directly(proc)
{
    assert(PendSV < proc && proc < USER0);
    assert(ghost_direct_AT <= (1 << proc));
    set_bit(proc, ghost_direct_AT);
    AT = proc
}

inline push_and_change_AT(proc)
{
    d_step {
        if
        :: !get_bit(AT, ghost_direct_AT) ->
            ATTop = ATTop + 1;
            assert(ATTop < NBALL);
            ATStack[ATTop] = AT;
            AT = proc
        :: else ->
            /* late arrival
             * current process AT is changed by change_AT_directly and been
             * preempt by higher priority exception, however, AT has not
             * process the ITake to clear the ghost bit. Thus, can not push
             * to the ATStack. */
            AT = proc
        fi
    }
}

inline pop_ATStack_to_AT()
{
    d_step {
        AT = ATStack[ATTop];
        ATStack[ATTop] = UNKNOWN;
        assert(ATTop >= 0);
        ATTop = ATTop - 1
    }
}

/* check if proc is active or not */
inline inATStack(proc, ret)
{
    d_step {
        ret = false;
        FOR_ATTOP_IDX {
            if
            :: ATStack[idx] == proc ->
                ret = true; break
            :: else -> skip
            fi
        }
        idx = 0
    }
}

/* return true if preemption can preempt the running task, and
 * false otherwise. */
inline interrupt_policy(preempt, running, ret)
{
    d_step {
        if
        :: preempt == running ->
            /* XXX
             * The limitation of this model is that, the irq is triggered by
             * the running of process. The irq will not trigger again while
             * the related interrupt process are running. */
            assert(get_bit(preempt, ghost_direct_AT) || preempt == PendSV);
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
            :: irq_prio[max_prio] < irq_prio[running] && preempt == max_prio ->
                assert(!get_bit(preempt, ghost_direct_AT));
                ret = true
            :: else ->
                ret = false
            fi
        fi
    }
}

inline ITake(proc)
{
    do
    :: atomic {
        inATStack(proc, retInATStack);
        interrupt_policy(proc, AT, retPolicy);
        if
        :: !retInATStack && retPolicy ->
            clear_pending(proc);
            push_and_change_AT(proc);
            break
        :: !retInATStack && get_bit(proc, ghost_direct_AT) ->
            /* change AT directly from IRet, similar to tail-chaining */
            clear_bit(proc, ghost_direct_AT);
            clear_pending(proc);
            break
        :: else -> skip
        fi
       }
    od
}

inline PendSVTake()
{
    do
    :: atomic {
        inATStack(PendSV, retInATStack);
        interrupt_policy(PendSV, AT, retPolicy);
        if
        :: PendSVReq && !retInATStack && retPolicy ->
            clear_pending(PendSV);
            push_and_change_AT(PendSV);
            PendSVReq = false;
            break
        :: else ->
            /* there is no need to set PendSV pending state */
            clear_pending(PendSV)
        fi
       }
    od
}

inline IRet()
{
    if
    :: irq_pending != 0 ->
        assert(!get_bit(PendSV, irq_pending));
        get_max_pending(max_prio);
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
    fi
}

/* -------------
 * all processes
 * ------------ */
//TODO: the user task will not exit in this spin model
//      there are no thread_exit abstraction.

active proctype svc()
{
    int idx, max_prio;
    bool retInATStack, retPolicy, del_queue_check;
    pid tempUser;
    assert(_pid == SVC);
    (all_process_prepare_to_run);
endSVC:
    AWAITS(_pid, ghost_svc = 1);
    AWAITS(_pid, assert(svc_type != DEFAULT_SYS));
    if
    :: svc_type == SYS_MUTEX_LOCK ->
        AWAITS(_pid, mutex = mutex + 1);
        if
        :: mutex != 0 ->
            AWAITS(_pid, ti[curUser - USER0].ti_private = mutex);
            AWAITS(_pid, ti[curUser - USER0].ti_state = THREAD_STATE_BLOCKED);
            AWAITS(_pid, mutex_add_tail(curUser));
            sched_elect(SCHED_OPT_NONE, _pid)
        :: else ->
            AWAITS(_pid, skip)
        fi
    :: svc_type == SYS_MUTEX_UNLOCK ->
        AWAITS(_pid, max_prio = UNKNOWN);
        AWAITS(_pid, mutex = mutex - 1);
        if
        :: mutex >= 0 ->
            AWAITS(_pid, find_first_blocking_task_and_del(max_prio));
            /* XXX: mutex_del(max_prio) */
            sched_enqueue(max_prio, _pid)
        :: else ->
            AWAITS(_pid, skip)
        fi;
        if
        :: get_ti_state(curUser) == THREAD_STATE_BLOCKED ->
            sched_elect(SCHED_OPT_NONE, _pid)
        :: max_prio != UNKNOWN && get_ti_prio(curUser) <= get_ti_prio(max_prio) ->
            sched_enqueue(curUser, _pid);
            sched_elect(SCHED_OPT_NONE, _pid)
        :: else ->
            AWAITS(_pid, skip)
        fi
    :: svc_type == SYS_PTHREAD_YIELD ->
        sched_enqueue(curUser, _pid);
        sched_elect(SCHED_OPT_NONE, _pid)
    fi;
    AWAITS(_pid, svc_type = DEFAULT_SYS);
    AWAITS(_pid, ghost_svc = 0; IRet());

    goto endSVC
}

active proctype pendsv()
{
    int idx, max_prio;
    bool retInATStack, retPolicy, del_queue_check;
    pid tempUser;
    assert(_pid == PendSV);
    (all_process_prepare_to_run);
endPendSV:
    sched_elect(SCHED_OPT_TICK, _pid);
    AWAITS(_pid, IRet());

    goto endPendSV
}

active [NBINTS] proctype interrupts()
{
    int idx, max_prio;
    bool retInATStack, retPolicy, ghost_softirq;
    assert(PendSV < _pid && _pid < USER0);
    (all_process_prepare_to_run);
endInts:
    ITake(_pid);
    if
    :: _pid == 2 ->
        /* the first interrupt is systick */
        /* TODO: future work for timer */
        tasklet_schedule(BH_SYSTICK, TIMER_SOFTIRQ_PRIO, _pid);
        AWAITS(_pid, PendSVReq = 1)
    :: else ->
        /* using stm32_uartx_isr() as interrupt example */
        /* this isr will not influence the scheduling behavior */
        /* only updates charactor buffer and calls an empty callback func */
        AWAITS(_pid, skip)
    fi;
    AWAITS(_pid, IRet());

    goto endInts
}

/* users are in non-privileged mode */
active [NBUSERS] proctype users()
{
    /* local monitor for r0 in mutex.pml */
    bit local_monitor;
    assert(USER0 <= _pid && _pid < SOFTIRQ);
    (all_process_prepare_to_run);
endUsers:
    if
    :: _pid == USER0 ->
        /* mutex initials at mutex_initialize */
        mutex_lock(mutex, _pid);
        mutex_unlock(mutex, _pid)
    :: else ->
        AWAITS(_pid, skip)
    fi;

    goto endUsers
}

/* softirq is in non-privileged mode */
active proctype softirq()
{
    int idx, max_prio;
    bool del_queue_check;
    byte next_task_func = NO_BH_TASK;
    assert(_pid == SOFTIRQ);
    (all_process_prepare_to_run);
endSoftirq:
    tasklet_action(_pid);
    /* softirqd thread should not return */
    AWAITS(_pid, assert(next_task_func == NO_BH_TASK));
    /* sched yield */
    AWAITS(_pid, sys_call(SYS_PTHREAD_YIELD));

    goto endSoftirq
}

init
{
    int idx, idx2, max_prio;
    bool retInATStack, retPolicy;

    d_step {
        system_initialize();
        mutex_initialize()
    };
    thread_info_initialize();
    all_process_prepare_to_run = 1;

endPendSV:
    PendSVTake();

    goto endPendSV
}
