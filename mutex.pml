#ifndef _MUTEX_
#define _MUTEX_

#include "variables.pml"
#include "ti.pml"

#define NBMUTEX NBALL

/* -1: unlocked, 0: locked, poritive: locked, possible waiters */
int mutex;

/* local monitor for r0 in mutex.pml */
bit local_monitor;
byte mutex_head[NBMUTEX];
int mutex_top;

inline mutex_add_tail(proc)
{
    d_step {
        mutex_top = mutex_top + 1;
        /* increase NBMUTEX if fail */
        assert(mutex_top < NBMUTEX);
        mutex_head[mutex_top] = proc
    }
}

/* The inline can typically split into two inlines:
 * find_first_blocking_task and mutex_del.
 */
inline find_first_blocking_task_and_del(ret)
{
    d_step {
    assert(mutex_top >= 0 && ret == UNKNOWN);
    for (idx: 0 .. mutex_top) {
        if
        :: (mutex_head[idx] != UNKNOWN) && (ret == UNKNOWN) ->
            ret = mutex_head[idx]
        :: else ->
            if
            :: ret != UNKNOWN ->
                mutex_head[idx - 1] = mutex_head[idx];
                if
                :: idx == mutex_top ->
                    mutex_head[idx] = UNKNOWN
                :: else -> skip
                fi
            :: else -> skip
            fi
        fi
    }
    idx = 0;
    assert(ret != UNKNOWN);
    mutex_top = mutex_top - 1
    }
}

inline mutex_lock(__mutex, tid)
{
    skip;
lock_0:
    /* ldrex r1, [r0] */
    AWAITS(tid, local_monitor = 1);
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
            /* bne 0b */
            goto lock_0
        fi
    fi

    /* no need to move #0 to r0 */
}

inline mutex_unlock(__mutex, tid)
{
    skip;
unlock_0:
    /* ldrex r1, [r0] */
    AWAITS(tid, local_monitor = 1);
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
            /* bne 0b */
            goto unlock_0
        fi
    fi

    /* no need to move #0 to r0 */
}

inline mutex_initialize()
{
    mutex = -1;
    mutex_top = -1;
    for (idx: 0 .. (NBMUTEX - 1)) {
        mutex_head[idx] = UNKNOWN
    }
    idx = 0
}

#endif /* _MUTEX_ */
