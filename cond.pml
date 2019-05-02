#ifndef _COND_
#define _COND_

#include "variables.pml"
#include "ti.pml"
#include "helper.pml"
#include "sched.pml"
#include "mutex.pml"

#define NBCOND 2
typedef cond_head {
    byte queue[NBCOND] = UNKNOWN
};

inline find_other_thread(ret, tid)
{
    for (idx: 0 .. (NBCOND - 1)) {
        if
        :: SELE(tid, cond_list.queue[idx] != UNKNOWN &&
           get_ti_private(cond_list.queue[idx]) == THREAD_PRIVATE_COND) ->
            AWAITS(tid, ret = cond_list.queue[idx]);
            A_AWAITS(tid, break)
        :: ELSE(tid, cond_list.queue[idx] != UNKNOWN &&
           get_ti_private(cond_list.queue[idx]) == THREAD_PRIVATE_COND) ->
        fi
    }
    A_AWAITS(tid, idx = 0)
}

inline sys_pthread_cond_wait(tid)
{
    AWAITS(tid, ti[curUser - USER0].ti_private = THREAD_PRIVATE_COND);
    AWAITS(tid, ti[curUser - USER0].ti_state = THREAD_STATE_BLOCKED);
    list_add_tail(curUser, cond_list, 0, NBCOND, tid);
    sys_pthread_mutex_unlock(tid)

    /* XXX : There might be a context switch after sys_pthread_mutex_unlock
     *       the current user might be changed here.
     *       To simulate this situation, the model will call the
     *       sys_pthread_mutex_lock in user task directly.
     * contend for the lock */
    //sys_pthread_mutex_lock(tid)
}

inline sys_pthread_cond_signal(tid)
{
    AWAITS(tid, assert(max_prio == UNKNOWN));
    find_other_thread(max_prio, tid);
    if
    :: SELE(tid, max_prio != UNKNOWN) ->
        list_del(max_prio, cond_list, 0, NBCOND, tid);
        sched_enqueue(max_prio, tid);
        if
        :: SELE(tid, get_ti_prio(max_prio) >= get_ti_prio(curUser)) ->
            sched_enqueue(curUser, tid);
            sched_elect(SCHED_OPT_NONE, tid)
        :: ELSE(tid, get_ti_prio(max_prio) >= get_ti_prio(curUser))
        fi
    :: ELSE(tid, max_prio != UNKNOWN)
    fi
}

#endif /* _COND_ */
