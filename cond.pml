#ifndef _COND_
#define _COND_

#include "variables.pml"
#include "ti.pml"
#include "helper.pml"
#include "sched.pml"
#include "mutex.pml"

#define NBCOND 1
typedef cond_head {
    byte queue[NBCOND] = UNKNOWN
};

inline find_other_thread(ret)
{
    assert(ret == UNKNOWN);
    for (idx: 0 .. (NBCOND - 1)) {
        if
        :: cond_list.queue[idx] != UNKNOWN &&
           get_ti_private(cond_list.queue[idx]) == THREAD_PRIVATE_COND ->
            ret = cond_list.queue[idx];
            break
        :: else
        fi
    }
    idx = 0;
}

inline sys_pthread_cond_wait(tid)
{
    AWAITS(tid, ti[curUser - USER0].ti_private = THREAD_PRIVATE_COND);
    AWAITS(tid, ti[curUser - USER0].ti_state = THREAD_STATE_BLOCKED);
    AWAITS(tid, list_add_tail(curUser, cond_list, 0, NBCOND));
    sys_pthread_mutex_unlock(tid);

    /* XXX : There might be a context switch after sys_pthread_mutex_unlock
     *       the current user might be changed here.
     *       To simulate this situation, the model will call the
     *       sys_pthread_mutex_lock in user task directly.
     * contend for the lock */
    //sys_pthread_mutex_lock(tid)
}

inline sys_pthread_cond_signal(tid)
{
    AWAITS(tid, max_prio = UNKNOWN);
    AWAITS(tid, find_other_thread(max_prio));
    if
    :: max_prio != UNKNOWN ->
        AWAITS(tid, list_del(max_prio, cond_list, 0, NBCOND));
        sched_enqueue(max_prio, tid);
        if
        :: get_ti_prio(max_prio) >= get_ti_prio(curUser) ->
            sched_enqueue(curUser, tid);
            sched_elect(SCHED_OPT_NONE, tid)
        :: else
        fi
    :: else
    fi
}

#endif /* _COND_ */
