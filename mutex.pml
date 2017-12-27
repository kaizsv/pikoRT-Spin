#ifndef _MUTEX_
#define _MUTEX_

#include "variables.pml"
#include "ti.pml"

#define NBMUTEX 1
typedef mutex_head {
    byte queue[NBMUTEX] = UNKNOWN
};

/* -1: unlocked, 0: locked, poritive: locked, possible waiters */
short mutex;

/* local monitor for r0 in mutex.pml */
bit local_monitor;

inline find_first_blocking_task(ret)
{
    assert(ret == UNKNOWN);
    for (idx: 0 .. (NBMUTEX - 1)) {
        if
        :: mutex_list.queue[idx] != UNKNOWN ->
            ret = mutex_list.queue[idx];
            break
        :: else
        fi
    }
    idx = 0;
    assert(ret != UNKNOWN)
}

/* reset local_monitor to 1 in condition statement to
 * prevent redundant skip condiditon in PROMELA model
 * (jump into d_step) */
inline mutex_lock(__mutex, tid)
{
    /* ldrex r1, [r0] */
    AWAITS(tid, local_monitor = 1);
lock_0:
    if
    :: __mutex != -1 ->
        /* bne 1f */
        /* svc to #SYS_PTHREAD_MUTEX_LOCK */
        AWAITS(tid, sys_call(SYS_MUTEX_LOCK))
    :: else ->
        /* strex r1, r2, [r0] */
        if
        :: local_monitor == 1 ->
            AWAITS(tid, __mutex = 0; local_monitor = 0)
        :: else ->
            AWAITS(tid, local_monitor = 1);
            /* bne 0b */
            goto lock_0
        fi
    fi

    /* no need to move #0 to r0 */
}

inline mutex_unlock(__mutex, tid)
{
    /* ldrex r1, [r0] */
    AWAITS(tid, local_monitor = 1);
unlock_0:
    if
    :: __mutex != 0 ->
        /* bne 1f */
        /* svc to #SYS_PTHREAD_MUTEX_UNLOCK */
        AWAITS(tid, sys_call(SYS_MUTEX_UNLOCK))
    :: else ->
        /* strex r1, r2, [r0] */
        if
        :: local_monitor == 1 ->
            AWAITS(tid, __mutex = -1; local_monitor = 0)
        :: else ->
            AWAITS(tid, local_monitor = 1);
            /* bne 0b */
            goto unlock_0
        fi
    fi

    /* no need to move #0 to r0 */
}

inline mutex_initialize()
{
    mutex = -1;
}

#endif /* _MUTEX_ */
