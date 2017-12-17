/*
 * Global define
 */

#define THREAD_STATE_NEW 0
#define THREAD_STATE_READY1 1
#define THREAD_STATE_READY2 2
#define THREAD_STATE_RUNNING 3
#define THREAD_STATE_TERMINATED 4
#define THREAD_STATE_BLOCKED 5

#define THREAD_STATE_ACTIVED THREAD_SCHED_STATE[0]
#define THREAD_STATE_EXPIRED THREAD_SCHED_STATE[1]

#define get_ti_prio(proc) ti[proc - USER0].ti_priority
#define get_ti_state(proc) ti[proc - USER0].ti_state
#define get_ti_private(proc) ti[proc - USER0].ti_private

/*
 * Local define
 */

#ifndef _THREAD_INFO_
#define _THREAD_INFO_

#include "variables.pml"
#include "sched.pml"

typedef thread_info {
    byte ti_priority;
    byte ti_state;
    byte ti_private;
};

/* ACTIVED: 0
 * EXPIRED: 1
 */
int THREAD_SCHED_STATE[2];
thread_info ti[NBUSERS + 1];

inline swap_sched_state_map()
{
    if
    :: THREAD_SCHED_STATE[0] == THREAD_STATE_READY1 ->
        assert(THREAD_SCHED_STATE[1] == THREAD_STATE_READY2);
        THREAD_SCHED_STATE[0] = THREAD_STATE_READY2;
        THREAD_SCHED_STATE[1] = THREAD_STATE_READY1
    :: THREAD_SCHED_STATE[0] == THREAD_STATE_READY2 ->
        assert(THREAD_SCHED_STATE[1] == THREAD_STATE_READY1);
        THREAD_SCHED_STATE[0] = THREAD_STATE_READY1;
        THREAD_SCHED_STATE[1] = THREAD_STATE_READY2
    fi
}

inline thread_info_initialize()
{
    THREAD_SCHED_STATE[0] = THREAD_STATE_READY1;
    THREAD_SCHED_STATE[1] = THREAD_STATE_READY2;

    /* The USER0 is the user's entry-point to the system. It is not
     * added to the runqueue because it has been implicityl "elecetd"
     * when initialize return
     */
    ti[USER0 - USER0].ti_priority = PRI_MIN;
    ti[USER0 - USER0].ti_state = THREAD_STATE_NEW;

    /* using idx2 to prevent idx being changed in sched_enqueue */
    for (idx2: (USER0 + 1) .. (SOFTIRQ - 1)) {
        ti[idx2 - USER0].ti_priority = PRI_MIN;
        ti[idx2 - USER0].ti_state = THREAD_STATE_NEW;
        sched_enqueue(idx2, AT)
    }
    idx2 = 0;

    ti[SOFTIRQ - USER0].ti_priority = PRI_MAX;
    ti[SOFTIRQ - USER0].ti_state = THREAD_STATE_NEW
}

#endif /* _THREAD_INFO_ */
