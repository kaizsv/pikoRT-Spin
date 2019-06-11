#ifndef _SYSTICK_
#define _SYSTICK_

#include "variables.pml"
#include "ti.pml"

bit sys_pseudo_timer = 0;

/* TODO: the systick_bh need to handle system call sys_msleep function */
/*       to resched the specific user task after msecs. The sys_msleep */
/*       will dequeue the current task. After msecs, the systick_bh will */
/*       call the callback function to enqueue the user task. */
inline systick_bh()
{
    if
    :: sys_pseudo_timer ->
        sys_pseudo_timer = 0;
        /* sched_enqueue(producer, tid) */
        ti[USER0 + 1 - USER0].ti_state = THREAD_STATE_ACTIVED;
        ti_add_tail(USER0 + 1, sched_bm[SCHED_BITMAP_ACTIVE], get_ti_prio(USER0 + 1), NB_WAIT_TASKS);
        set_bit(get_ti_prio(USER0 + 1), sched_bm[SCHED_BITMAP_ACTIVE].map)
        assert(get_ti_state(USER0 + 1) == THREAD_STATE_ACTIVED &&
               get_bit(get_ti_prio(USER0 + 1), sched_bm[SCHED_BITMAP_ACTIVE].map) &&
               (sched_bm[SCHED_BITMAP_ACTIVE].queue[get_ti_prio(USER0 + 1) * NB_WAIT_TASKS + 0] == USER0 + 1 ||
                sched_bm[SCHED_BITMAP_ACTIVE].queue[get_ti_prio(USER0 + 1) * NB_WAIT_TASKS + 1] == USER0 + 1 ||
                sched_bm[SCHED_BITMAP_ACTIVE].queue[get_ti_prio(USER0 + 1) * NB_WAIT_TASKS + 2] == USER0 + 1));
    :: else
    fi
}

#endif /* _SYSTICK_ */
