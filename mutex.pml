#ifndef _MUTEX_
#define _MUTEX_

#include "variables.pml"
#include "ti.pml"

#define NBMUTEX NBALL

int mutex;

/* local monitor for r0 */
bit local_monitor;
byte mutex_head[NBMUTEX];//TODO: can be smaller
int mutex_top;

inline mutex_add_tail(proc)
{
    mutex_top = mutex_top + 1;
    assert(mutex_top < NBMUTEX);
    mutex_head[mutex_top] = proc
}

//inline mutex_del(proc)
//{
//    skip
//}

/* The inline can typically split into two inlines:
 * find_first_blocking_task and mutex_del.
 */
inline find_first_blocking_task_and_del(ret)
{
    d_step {
    assert(mutex_top >= 0 && ret == UNKNOWN);
    for (idx: 0 .. mutex_top) {
        if
        :: (get_ti_private(mutex_head[idx]) == mutex) && (ret == UNKNOWN) ->
            ret = mutex_head[idx];
        :: else ->
            if
            :: ret != UNKNOWN ->
                mutex_head[idx - 1] = mutex_head[idx]
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
        goto lock_1
    :: else ->
        AWAITS(tid, skip)
    fi;

    /* strex r1, r2, [r0] */
    if
    :: local_monitor == 1 ->
        AWAITS(tid, __mutex = 0; local_monitor = 0)
    :: else ->
        /* bne 0b */
        goto lock_0
    fi;

    /* movs r0, #0 */
    if
    :: __mutex != 0 ->
        AWAITS(tid, __mutex = 0)
    :: else ->
        goto lock_out
    fi;
lock_1:
    /* svc to #SYS_PTHREAD_MUTEX_LOCK */
    AWAITS(tid, sys_call(SYS_MUTEX_LOCK));

lock_out:
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
        goto unlock_1
    :: else ->
        AWAITS(tid, skip)
    fi;

    /* strex r1, r2, [r0] */
    if
    :: local_monitor == 1 ->
        AWAITS(tid, __mutex = -1; local_monitor = 0)
    :: else ->
        /* bne 0b */
        goto unlock_0
    fi;

    /* movs r0, #0 */
    if
    :: __mutex != 0 ->
        AWAITS(tid, __mutex = 0)
    :: else ->
        goto unlock_out
    fi;
unlock_1:
    /* svc to #SYS_PTHREAD_MUTEX_UNLOCK */
    AWAITS(tid, sys_call(SYS_MUTEX_UNLOCK));

unlock_out:
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
