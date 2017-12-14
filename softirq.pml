#ifndef _SOFTIRQ_
#define _SOFTIRQ_

#include "variables.pml"
#include "helper.pml"
#include "sched.pml"
#include "sched_bitmap.pml"
#include "systick.pml"

#define PRIO_TASKLET_MINPRIO 31
#define TIMER_SOFTIRQ_PRIO 0

#define NO_BH_TASK 0
#define BH_SYSTICK 1
byte next_task_func = NO_BH_TASK;

bitmap_struct prio_tasklet;

inline raise_softirq(tid)
{
    if
    :: !ghost_softirq ->
        sched_enqueue(SOFTIRQ, tid);
        AWAITS(tid, ghost_softirq = 1)
    :: else ->
        AWAITS(tid, skip)
    fi
}

inline tasklet_bitmap_enqueue(new, prio, tid)
{
    AWAITS(tid, add_queue_tail(new, prio, prio_tasklet));
    AWAITS(tid, set_bit(prio, prio_tasklet.map))
}

inline tasklet_schedule(task, prio, tid)
{
    AWAITS(tid, assert(task != NO_BH_TASK || prio <= PRIO_TASKLET_MINPRIO));
    tasklet_bitmap_enqueue(task, prio, tid);
    raise_softirq(tid)
}

inline tasklet_action(tid)
{
    do
    :: true ->
        if
        :: prio_tasklet.map != 0 ->
            AWAITS(tid, find_first_bit(prio_tasklet.map, max_prio, PRI_MIN));
            AWAITS(tid, bitmap_first_entry(prio_tasklet, max_prio, next_task_func));
            bitmap_queue_del(next_task_func, max_prio, prio_tasklet, tid);

            /* XXX:
             * To prevent the unreached statement, using assert rather than
             * condition instruction. If more than one buttom helf functions
             * are used need to re-write with condition
             *
             * if
             * :: next_task_func == BH_XXX ->
             * :: else ->
             * fi
             */
            /* the elected tasketlet must be systick buttom half */
            AWAITS(tid, assert(next_task_func == BH_SYSTICK));
            systick_bh(tid);
        :: else ->
            AWAITS(tid, next_task_func = NO_BH_TASK; break);
        fi
    od
}

#endif /* _SOFTIRQ_ */
