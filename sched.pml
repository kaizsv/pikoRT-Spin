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
 */
#define PRI_MAX 0
#define PRI_MIN 30

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
    :: ti[del - USER0].ti_state == THREAD_STATE_ACTIVED ->
        sched_bitmap_dequeue(del, get_ti_prio(del), sched._bm[SCHED_BITMAP_ACTIVE], tid)
    :: ti[del - USER0].ti_state == THREAD_STATE_EXPIRED ->
        sched_bitmap_dequeue(del, get_ti_prio(del), sched._bm[SCHED_BITMAP_EXPIRE], tid)
    :: else ->
        AWAITS(tid, assert(false))
    fi
}

inline sched_elect(flags, tid)
{
    //TODO: need to check
    sched_bitmap_elect(flags, tid)
    AWAITS(tid, ti[curUser - USER0].ti_state = THREAD_STATE_RUNNING);
}

#endif /* _SCHED_ */
