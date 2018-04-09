/*
 * Global define
 */

#define THREAD_STATE_NEW 2
#define THREAD_STATE_READY1 0
#define THREAD_STATE_READY2 1
#define THREAD_STATE_RUNNING 3
#define THREAD_STATE_TERMINATED 4
#define THREAD_STATE_BLOCKED 5

/**
* Because we use bitwise operation to simulate the exchange of active and
* expire runqueue, we don't need to swap the thread state again. Moreover,
* we shift the order of the READY1 and READY2 thread state to meet with the
* SCHED_STATE_MAP in sched_bitmap.
*/
#define THREAD_STATE_ACTIVED THREAD_STATE_READY1
#define THREAD_STATE_EXPIRED THREAD_STATE_READY2

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
thread_info ti[NBUSERS + 1];

inline thread_info_initialize()
{
    /* The USER0 is the user's entry-point to the system. It is not
     * added to the runqueue because it has been implicityl "elecetd"
     * when initialize return
     */
    ti[USER0 - USER0].ti_priority = PRI_MIN;
    ti[USER0 - USER0].ti_state = THREAD_STATE_NEW;

    /**
    * Use global var 'mutex' to reduce the usage of another local var
    */
    for (mutex: (USER0 + 1) .. (SOFTIRQ - 1)) {
        ti[mutex - USER0].ti_priority = PRI_MIN;

        /* sched_enqueue(mutex, AT): prevent nested d_step */
        ti[mutex - USER0].ti_state = THREAD_STATE_ACTIVED;
        add_tail(mutex, sched_bm[SCHED_BITMAP_ACTIVE], get_ti_prio(mutex), NB_WAIT_TASKS);
        set_bit(get_ti_prio(mutex), sched_bm[SCHED_BITMAP_ACTIVE].map)
    }
    mutex = 0;

    ti[SOFTIRQ - USER0].ti_priority = PRI_MAX;
    ti[SOFTIRQ - USER0].ti_state = THREAD_STATE_NEW
}

#endif /* _THREAD_INFO_ */
