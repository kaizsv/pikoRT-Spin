/*
 * Global define
 */

#define THREAD_STATE_NEW 0
#define THREAD_STATE_ACTIVED 1
#define THREAD_STATE_EXPIRED 2
#define THREAD_STATE_RUNNING 3
#define THREAD_STATE_TERMINATED 4
#define THREAD_STATE_BLOCKED 5

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
    int ti_priority;
    int ti_state;
    int ti_private;
};

thread_info ti[NBUSERS + 1];

inline thread_info_initialize()
{
    /* using idx2 to prevent idx being changed in sched_enqueue */
    for (idx2: USER0 .. (SOFTIRQ - 1)) {
        ti[idx2 - USER0].ti_priority = PRI_MIN;
        ti[idx2 - USER0].ti_state = THREAD_STATE_NEW;
        sched_enqueue(idx2, AT)
    }
    idx2 = 0;

    ti[SOFTIRQ - USER0].ti_priority = PRI_MAX;
    ti[SOFTIRQ - USER0].ti_state = THREAD_STATE_NEW;
    sched_enqueue(SOFTIRQ, AT)
}

#endif /* _THREAD_INFO_ */
