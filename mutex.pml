#ifndef _MUTEX_
#define _MUTEX_

#include "variables.pml"
#include "ti.pml"
#include "sched.pml"
#include "helper.pml"

#define NBMUTEX 1
typedef mutex_head {
    byte queue[NBMUTEX] = UNKNOWN
};

/* -1: unlocked, 0: locked, positive: locked, possible waiters */
short mutex;

/* local monitor for r0 in mutex.pml */
bit local_monitor;

inline find_first_blocking_task(ret)
{
    assert(ret == UNKNOWN);
    for (idx: 0 .. (NBMUTEX - 1)) {
        if
        :: mutex_list.queue[idx] != UNKNOWN &&
           get_ti_private(mutex_list.queue[idx]) == THREAD_PRIVATE_MUTEX ->
            ret = mutex_list.queue[idx];
            break
        :: else
        fi
    }
    idx = 0;
    assert(ret != UNKNOWN)
}

inline sys_pthread_mutex_lock(tid)
{
    AWAITS(tid, assert(mutex >= -1); mutex = mutex + 1);
    if
    :: mutex > 0 ->
        AWAITS(tid, ti[curUser - USER0].ti_private = THREAD_PRIVATE_MUTEX);
        AWAITS(tid, ti[curUser - USER0].ti_state = THREAD_STATE_BLOCKED);
        AWAITS(tid, list_add_tail(curUser, mutex_list, 0, NBMUTEX));
        sched_elect(SCHED_OPT_NONE, tid)
    :: else
    fi
}

inline sys_pthread_mutex_unlock(tid)
{
    AWAITS(tid, max_prio = UNKNOWN);
    AWAITS(tid, assert(mutex > -1); mutex = mutex - 1);
    if
    :: mutex >= 0 ->
        AWAITS(tid, find_first_blocking_task(max_prio));
        AWAITS(tid, list_del(max_prio, mutex_list, 0, NBMUTEX));
        sched_enqueue(max_prio, tid)
    :: else
    fi;
    if
    :: get_ti_state(curUser) == THREAD_STATE_BLOCKED ->
        sched_elect(SCHED_OPT_NONE, tid)
    :: else ->
        if
        :: max_prio != UNKNOWN &&
           get_ti_prio(curUser) <= get_ti_prio(max_prio) ->
            sched_enqueue(curUser, tid);
            sched_elect(SCHED_OPT_NONE, tid)
        :: else
        fi
    fi
}

inline mutex_lock(__mutex, tid)
{
    do                                         // lock_0 loop
    :: AWAITS(tid, local_monitor = 1);         // ldrex r1, [r0]
       AWAITS(tid,                             // teq r1, #-1
        if
        :: __mutex != -1 -> ne = 1
        :: else -> ne = 0
        fi );
       A_AWAITS(tid,                           // bne 1f
        if
        :: ne == 1 -> goto lock_1
        :: else
        fi );
       AWAITS(tid,                             // strex r1, r2, [r0]
        if
        :: local_monitor == 1 ->               // 'strex' success
            assert(__mutex == -1);
            __mutex = 0; local_monitor = 0
        :: else -> ne = 1
        fi );
       A_AWAITS(tid,                           // teq r1, #0
        if
        :: ne != 1 -> break
        :: else                                // bne 0b
        fi )
    od;
lock_1:
    // itt ne
    // movne r1, #SYS_PTHREAD_MUTEX_LOCK
    // svcne #1
    A_AWAITS(tid,
        if
        :: ne == 1 -> sys_call(SYS_MUTEX_LOCK)
        :: else
        fi
    );
}

inline mutex_unlock(__mutex, tid)
{
    do                                         // unlock_0 loop
    :: AWAITS(tid, local_monitor = 1);         // ldrex r1, [r0]
       AWAITS(tid,                             // teq r1, #0
        if
        :: __mutex != 0 -> ne = 1
        :: else -> ne = 0
        fi );
       A_AWAITS(tid,                           // bne 1f
        if
        :: ne == 1 -> goto unlock_1
        :: else
        fi );
       AWAITS(tid,                             // strex r1, r2, [r0]
        if
        :: local_monitor == 1 ->               // 'strex' success
            assert(__mutex == 0);
            __mutex = -1; local_monitor = 0
        :: else -> ne = 1
        fi );
       A_AWAITS(tid,                           // teq r1, #0
        if
        :: ne != 1 -> break
        :: else                                // bne 0b
        fi );
    od;
unlock_1:
    // itt ne
    // movne r1, #SYS_PTHREAD_MUTEX_UNLOCK
    // svcne #1
    A_AWAITS(tid,
        if
        :: ne == 1 -> sys_call(SYS_MUTEX_UNLOCK)
        :: else
        fi
    );
}

inline mutex_initialize()
{
    mutex = -1;
}

#endif /* _MUTEX_ */
