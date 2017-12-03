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
    ret = UNKNOWN;
    /* svc will not be pending */
    for (idx: 1 .. (USER0 - 1)) {
        if
        :: get_bit(idx, irq_pending) && (irq_priority[idx] < ret) ->
            ret = idx
        :: else ->
            skip
        fi
    }
    idx = 0;
    /* always has a max priority exception */
    assert(ret != UNKNOWN)
}

inline change_AT_directly(proc)
{
    set_bit(proc, ghost_direct_AT);
    AT = proc
}

inline push_and_change_AT(proc)
{
    ATTop = ATTop + 1;
    assert(ATTop < NBALL);
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

inline inATStack(proc, ret)
{
    ret = false;
    FOR_ATTOP_IDX {
        if
        :: ATStack[idx] == proc -> ret = true; break
        :: else -> skip
        fi
    }
    idx = 0
}

inline interrupt_policy(preempt, running, ret)
{
    if
    :: (preempt == SVC || preempt == PendSV) && (running < USER0) ->
        /* SVC is triggered by svc command */
        /* PendSV is triggered by PendSVReq bit */
        assert(preempt != SVC);
        ret = false
    :: preempt == running ->
        assert(get_bit(preempt, ghost_direct_AT) || preempt == PendSV);
        /* the preemption can not be self */
        ret = false
    :: running >= USER0 ->
        /* the exception always takes while user task is running */
        /* and there remain nothing in ATStack */
        assert(ATTop <= 0 && preempt != SVC);
        /* if PendSV preempt user task, setting the pending bit of PendSV */
        /* has no side-effect */
        set_pending(preempt);
        ret = true
    :: else ->
        assert(running < USER0);
        /* nested interrupt */
        /* compare the priority of pending and preemtive exception */
        set_pending(preempt);
        get_max_pending(max_prio);
        if
        :: irq_priority[max_prio] < irq_priority[running] ->
            if
            :: preempt == max_prio ->
                ret = true
            :: else ->
                change_AT_directly(max_prio); //TODO: check
                ret = false
            fi
        :: else ->
            ret = false
        fi
    fi
}

inline ITake(proc)
{
    do
    :: atomic {
        /* check if proc is active or not */
        inATStack(proc, retInATStack);
        interrupt_policy(proc, AT, retPolicy);
        if
        :: !retInATStack && retPolicy ->
            clear_pending(proc);
            push_and_change_AT(proc);
            break
        :: !retInATStack && get_bit(proc, ghost_direct_AT) ->
            clear_bit(proc, ghost_direct_AT);
            clear_pending(proc);
            break
        :: else ->
            skip
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
            push_and_change_AT(PendSV)
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
        get_max_pending(max_prio);
        assert(PendSV < max_prio && max_prio < USER0);
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
    if
    :: svc_type = SYS_MUTEX_LOCK ->
        AWAITS(_pid, mutex = mutex + 1; assert(mutex));
        AWAITS(_pid, ti[curUser - USER0].ti_private = mutex);
        AWAITS(_pid, ti[curUser - USER0].ti_state = THREAD_STATE_BLOCKED);
        AWAITS(_pid, mutex_add_tail(curUser));
        sched_elect(SCHED_OPT_NONE, _pid);
    :: svc_type = SYS_MUTEX_UNLOCK ->
        AWAITS(_pid, mutex = mutex - 1);
        if
        :: mutex >= 0 ->
            AWAITS(_pid, find_first_blocking_task(max_prio));
            sched_enqueue(max_prio, _pid)
        :: else ->
            AWAITS(_pid, skip)
        fi;
        if
        :: ti[curUser - USER0].ti_state == THREAD_STATE_BLOCKED ->
            sched_elect(SCHED_OPT_NONE, _pid)
        :: ti[curUser-USER0].ti_priority <= ti[max_prio-USER0].ti_priority ->
            sched_enqueue(curUser, _pid);
            sched_elect(SCHED_OPT_NONE, _pid)
        :: else ->
            AWAITS(_pid, skip)
        fi
    :: svc_type = DEFAULT_SYS ->
        sched_elect(SCHED_OPT_NONE, _pid);
    fi;
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

/* irq will not always trigger while interrupts process is running*/
active [NBINTS] proctype interrupts()
{
    int idx, max_prio;
    bool retInATStack, retPolicy;
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
        // TODO: check
        AWAITS(_pid, skip)
    fi;
    AWAITS(_pid, IRet());

    goto endInts
}

/* users are in non-privileged mode */
active [NBUSERS] proctype users()
{
    int idx;
    assert(USER0 <= _pid && _pid < SOFTIRQ);
    (all_process_prepare_to_run);
endUsers:
    AWAITS(_pid, skip)

    goto endUsers
}

/* softirq is in non-privileged mode */
active proctype softirq()
{
    int idx, max_prio;
    bool del_queue_check;
    pid tempUser;
    assert(_pid == SOFTIRQ);
    (all_process_prepare_to_run);
endSoftirq:
    tasklet_action(_pid);
    if
    :: next_task_func == NO_BH_TASK ->
        /* sched yield */
        sched_enqueue(SOFTIRQ, _pid);
        sched_elect(SCHED_OPT_NONE, _pid);
    :: else ->
        /* softirqd thread should not return */
        AWAITS(_pid, assert(false))
    fi

    goto endSoftirq
}

init
{
    int idx, idx2, max_prio;
    bool retInATStack, retPolicy;

    d_step {
        system_initialize();
        thread_info_initialize();
        mutex_initialize()
    };
    all_process_prepare_to_run = 1;
    //sched_enqueue(USER0, AT);
    //sched_enqueue(SOFTIRQ);
    //push_and_change_AT(2);
    //push_and_change_AT(PendSV);
    //sched_elect(SCHED_OPT_TICK);
    //switch_to(curUser);
    //curUser = nextUser;
    //thread_restore(curUser);
    //sched_dequeue(USER0, AT);
    //sched_dequeue(5, AT);
    //sched_dequeue(6, AT);
    //tasklet_schedule(BH_SYSTICK, TIMER_SOFTIRQ_PRIO);
    //tasklet_action()
endPendSV:
    PendSVTake();

    goto endPendSV
}
