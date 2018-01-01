/*
 * Global define
 */

#define THREAD_STATE_NEW 2
#define THREAD_STATE_READY1 0
#define THREAD_STATE_READY2 1
#define THREAD_STATE_RUNNING 3
#define THREAD_STATE_TERMINATED 4
#define THREAD_STATE_BLOCKED 5

#define THREAD_STATE_ACTIVED (THREAD_SCHED_STATE_SWAP | THREAD_STATE_READY1)
#define THREAD_STATE_EXPIRED (THREAD_SCHED_STATE_SWAP ^ THREAD_STATE_READY2)

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
#include "sched_bitmap.pml"

typedef thread_info {
    bit ti_private
    byte ti_priority
    byte ti_state
};

/* ACTIVED: 0
 * EXPIRED: 1
 */
bit THREAD_SCHED_STATE_SWAP;
thread_info ti[NBUSERS + 1];

inline swap_sched_state_map()
{
    THREAD_SCHED_STATE_SWAP = THREAD_SCHED_STATE_SWAP ^ 1
}

inline thread_info_initialize()
{
    THREAD_SCHED_STATE_SWAP = 0;

    /* The USER0 is the user's entry-point to the system. It is not
     * added to the runqueue because it has been implicityl "elecetd"
     * when initialize return
     */
    ti[USER0 - USER0].ti_priority = PRI_MIN;
    ti[USER0 - USER0].ti_state = THREAD_STATE_NEW;

    /* using max_prio to prevent idx being changed in sched_enqueue */
//    for (idx2: (USER0 + 1) .. (SOFTIRQ - 1)) {
        assert(NBUSERS == 2); // XXX: replace 5 with idx2 if assert fails.
        ti[5 - USER0].ti_priority = PRI_MIN;

        /* sched_enqueue(idx2, AT): prevent nested d_step */
        ti[5 - USER0].ti_state = THREAD_STATE_ACTIVED;
        add_tail(5, sched_bm[SCHED_BITMAP_ACTIVE], get_ti_prio(5), NB_WAIT_TASKS);
        set_bit(get_ti_prio(5), sched_bm[SCHED_BITMAP_ACTIVE].map)
//    }
//    idx2 = 0;

    ti[SOFTIRQ - USER0].ti_priority = PRI_MAX;
    ti[SOFTIRQ - USER0].ti_state = THREAD_STATE_NEW
}

#endif /* _THREAD_INFO_ */
