#ifndef _SOFTIRQ_
#define _SOFTIRQ_

#include "variables.pml"
#include "helper.pml"
#include "sched.pml"
#include "sched_bitmap.pml"
//#include "systick.pml"

#define PRIO_TASKLET_MINPRIO 31
#define TIMER_SOFTIRQ_PRIO 0

#define NO_BH_TASK 0
#define BH_SYSTICK 1

bitmap_struct prio_tasklet;

// XXX: Because there are only one bottom half task in this model.
//      To prevent redundant task asserting into the slot, check
//      if map is zero or not.
// TODO: Rewrite if there are more than one bottom half tasks
inline tasklet_bitmap_enqueue(new, prio, tid)
{
    if
    :: prio_tasklet.map == 0 ->
        AWAITS(tid, add_tail(new, prio_tasklet, prio, NB_WAIT_TASKS));
        AWAITS(tid, set_bit(prio, prio_tasklet.map))
    :: else
    fi
}

inline tasklet_schedule(task, prio, tid)
{
    tasklet_bitmap_enqueue(task, prio, tid);

    /* raise softirq */
    if
    :: !ghost_softirq ->
        sched_enqueue(SOFTIRQ, tid);
        AWAITS(tid, ghost_softirq = 1)
    :: else
    fi
}

inline tasklet_action(ret, tid)
{
    do
    :: if
       :: prio_tasklet.map != 0 ->
           AWAITS(tid, find_first_bit(prio_tasklet.map, max_prio, PRI_MIN));
           AWAITS(tid, bitmap_first_entry(prio_tasklet, max_prio, ret));
           bitmap_queue_del(ret, max_prio, prio_tasklet, tid);

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
           AWAITS(tid, assert(next_tasklet == BH_SYSTICK))
           //systick_bh(tid)
       :: else ->
           AWAITS(tid, ret = NO_BH_TASK);
           break
       fi
    od;
    skip
}

#endif /* _SOFTIRQ_ */
