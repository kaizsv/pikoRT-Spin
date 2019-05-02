/*
 * Global define
 */
#define SCHED_OPT_NONE 0
#define SCHED_OPT_RESTORE_ONLY 1
#define SCHED_OPT_RESET 2
#define SCHED_OPT_TICK 3

/*
 * Beacuse the maximal unsigned variable width-field is 31 in spin,
 * the minimal priority can only be 30. However, the minimal priority
 * is 31 in pikoRT source code.
 *
 * TODO: To reduce memory usage, there is only 2 priority level in this model.
 *       Increase if needed.
 */
#define NBITMAP_BIT 2
#define PRI_MAX 0
#define PRI_MIN (NBITMAP_BIT - 1)

/*
 * Local define
 */

#ifndef _SCHED_
#define _SCHED_

#include "ti.pml"
#include "variables.pml"
#include "sched_bitmap.pml"

inline sched_enqueue(new, tid)
{
    AWAITS(tid, ti[new - USER0].ti_state = THREAD_STATE_ACTIVED);
    sched_bitmap_enqueue(new, get_ti_prio(new), tid)
}

inline sched_dequeue(del, tid)
{
    if
    :: SELE(tid, get_ti_state(del) == THREAD_STATE_ACTIVED) ->
        sched_bitmap_dequeue(del, get_ti_prio(del), sched_bm[SCHED_BITMAP_ACTIVE], tid)
    :: SELE(tid, get_ti_state(del) == THREAD_STATE_EXPIRED) ->
        sched_bitmap_dequeue(del, get_ti_prio(del), sched_bm[SCHED_BITMAP_EXPIRE], tid)
    :: ELSE(tid, get_ti_state(del) == THREAD_STATE_ACTIVED || get_ti_state(del) == THREAD_STATE_EXPIRED)
    fi
}

inline sched_elect(flags, tid)
{
    sched_bitmap_elect(flags, tid);
    if
    :: SELE(tid, curUser != IDLE_THREAD) ->
        AWAITS(tid, ti[curUser - USER0].ti_state = THREAD_STATE_RUNNING)
    :: ELSE(tid, curUser != IDLE_THREAD)
    fi
}

#endif /* _SCHED_ */
