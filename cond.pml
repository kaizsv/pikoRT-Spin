#ifndef _COND_
#define _COND_

#include "variables.pml"
#include "ti.pml"
#include "helper.pml"
#include "sched.pml"

#define NBCOND 1
typedef cond_head {
    byte queue[NBCOND] = UNKNOWN
};

inline find_other_thread(ret)
{
    assert(ret == UNKNOWN);
    for (idx: 0 .. NBCOND) {
        if
        :: get_ti_private(cond_list.queue[idx]) == THREAD_PRIVATE_COND ->
            ret = cond_list.queue[idx];
            break
        :: else
        fi
    }
    idx = 0;
}

inline sys_pthread_cond_wait()
{
    AWAITS(SVC, ti[curUser - USER0].ti_private = THREAD_PRIVATE_COND);
    AWAITS(SVC, ti[curUser - USER0].ti_state = THREAD_STATE_BLOCKED);
    AWAITS(SVC, list_add_tail(curUser, cond_list, 0, NBCOND));
    sys_pthread_mutex_lock();
    /* contend for the lock */
    sys_pthread_mutex_unlock()
}

inline sys_pthread_cond_signal()
{
    AWAITS(SVC, max_prio = UNKNOWN);
    AWAITS(SVC, find_other_thread(max_prio));
    if
    :: max_prio != UNKNOWN ->
        AWAITS(SVC, list_del(max_prio, cond_list, 0, NBCOND));
        sched_enqueue(max_prio, SVC);
        if
        :: get_ti_prio(max_prio) >= get_ti_prio(curUser) ->
            sched_enqueue(curUser, SVC);
            sched_elect(SCHED_OPT_NONE, SVC)
        :: else
        fi
    :: else
    fi
}

#endif /* _COND_ */
