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
    assert(mutex_top < NBALL);
    mutex_head[mutex_top] = proc
}

inline mutex_del(proc)
{
    skip
}

inline find_first_blocking_task(ret)
{
    ret = UNKNOWN;
    assert(mutex_top >= 0);
    for (idx: 0 .. mutex_top) {
        if
        :: (ti[mutex_head[idx]].ti_private == mutex) && (ret == UNKNOWN) ->
            ret = mutex_head[idx];
        :: ret != UNKNOWN ->
            mutex_head[idx - 1] = mutex_head[idx]
        :: else ->
            skip
        fi;
        if
        :: idx == mutex_top -> mutex_head[idx] = UNKNOWN
        :: else -> skip
        fi
    }
    idx = 0;
    assert(ret != UNKNOWN);
    mutex_top = mutex_top - 1
}

inline mutex_lock(mutex)
{
lock_0:
    /* ldrex r1, [r0] */
    local_monitor = 1;
    if
    :: mutex != -1 ->
        goto lock_1
    :: else ->
        skip
    fi;

    /* strex r1, r2, [r0] */
    if
    :: local_monitor == 1 ->
        mutex = 0;
        local_monitor = 0
    :: else ->
        goto lock_0
    fi;

    if
    :: mutex != 0 ->
        mutex = 0
    :: else ->
        goto lock_out
    fi;
lock_1:
    skip

lock_out:
}

inline mutex_unlock(mutex)
{
unlock_0:
    /* ldrex r1, [r0] */
    local_monitor = 1;
    if
    :: mutex != 0 ->
        goto unlock_1
    :: else ->
        skip
    fi;

    /* strex r1, r2, [r0] */
    if
    :: local_monitor == 1 ->
        mutex = -1;
        local_monitor = 0
    :: else ->
        goto unlock_0
    fi;

    if
    :: mutex != 0 ->
        mutex = 0
    :: else ->
        goto unlock_out
    fi;
unlock_1:
    skip

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
