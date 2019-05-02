/*
 * Global define
 */

#define THREAD_STATE_NEW 2
#define THREAD_STATE_READY1 0
#define THREAD_STATE_READY2 1
#define THREAD_STATE_RUNNING 3
#define THREAD_STATE_TERMINATED 4
#define THREAD_STATE_BLOCKED 5

#define THREAD_STATE_ACTIVED (THREAD_STATE_READY1 | SCHED_STATE_MAP)
#define THREAD_STATE_EXPIRED (THREAD_STATE_READY2 ^ SCHED_STATE_MAP)

#define THREAD_PRIVATE_MUTEX 0
#define THREAD_PRIVATE_COND 1

#define get_ti_private(proc) ti[proc - USER0].ti_private
#define get_ti_prio(proc) ti[proc - USER0].ti_priority
#define get_ti_state(proc) ti[proc - USER0].ti_state

/*
 * Local define
 */

#ifndef _THREAD_INFO_
#define _THREAD_INFO_

#include "variables.pml"
#include "sched.pml"

typedef thread_info {
    bit ti_private
    byte ti_priority = PRI_MIN
    byte ti_state = THREAD_STATE_NEW
};
thread_info ti[NBUSERS + 1];

inline ti_add_tail(new, bm, prio, size)
{
    assert(prio < NBITMAP_BIT);
    for (idx: 0 .. (size - 1)) {
        if
        :: bm.queue[prio * size + idx] == UNKNOWN ->
            bm.queue[prio * size + idx] = new; break
        :: else -> /* increase size if fail */
            assert(idx < (size - 1) && bm.queue[prio * size + idx] != new)
        fi
    }
    idx = 0
}

inline thread_info_initialize()
{
    /* The USER0 is the user's entry-point to the system. It is not
     * added to the runqueue because it has been implicityl "elecetd"
     * when initialize return
     */

    /* Other user tasks */
    for (idx2: (USER0 + 1) .. (SOFTIRQ - 1)) {
        /* sched_enqueue(idx2, AT): prevent nested d_step */
        ti[idx2 - USER0].ti_state = THREAD_STATE_ACTIVED;
        ti_add_tail(idx2, sched_bm[SCHED_BITMAP_ACTIVE], get_ti_prio(idx2), NB_WAIT_TASKS);
        set_bit(get_ti_prio(idx2), sched_bm[SCHED_BITMAP_ACTIVE].map)
    }
    idx2 = 0;

    ti[SOFTIRQ - USER0].ti_priority = PRI_MAX
}

#endif /* _THREAD_INFO_ */
