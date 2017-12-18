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

bitmap_struct prio_tasklet;

inline tasklet_bitmap_enqueue(new, prio, tid)
{
    AWAITS(tid, add_queue_tail(new, prio, prio_tasklet));
    AWAITS(tid, set_bit(prio, prio_tasklet.map))
}

inline tasklet_schedule(task, prio, tid)
{
    /* if the assert fails, use condition statement to skip the false */
    AWAITS(tid, assert(task != NO_BH_TASK || prio <= PRIO_TASKLET_MINPRIO));
    tasklet_bitmap_enqueue(task, prio, tid);

    /* raise softirq */
    if
    :: !ghost_softirq ->
        sched_enqueue(SOFTIRQ, tid);
        AWAITS(tid, ghost_softirq = 1)
    :: else ->
        AWAITS(tid, skip)
    fi
}

inline tasklet_action(tid)
{
    do
    :: true ->
        if
        :: prio_tasklet.map != 0 ->
            AWAITS(tid, find_first_bit(prio_tasklet.map, max_prio, PRI_MIN));
            /* bitmap_first_entry() */
            AWAITS(tid, next_tasklet = prio_tasklet.queue[max_prio * NB_WAIT_TASKS + 0]);
            bitmap_queue_del(next_tasklet, max_prio, prio_tasklet, tid);

            /* XXX:
             * To prevent the unreached statement, using assert rather than
             * condition instruction. If more than one bottom half functions
             * are used need to re-write with condition
             *
             * if
             * :: next_tasklet == BH_XXX -> XXX_bh()
             * :: ...
             * :: else ->
             * fi
             */
            /* the elected tasketlet must be systick buttom half */
            AWAITS(tid, assert(next_tasklet == BH_SYSTICK));
            systick_bh(tid)
        :: else ->
            AWAITS(tid, next_tasklet = NO_BH_TASK);
            /* AWAITS without d_step for break */
            atomic { (tid == AT); break }
        fi
    od
}

#endif /* _SOFTIRQ_ */
