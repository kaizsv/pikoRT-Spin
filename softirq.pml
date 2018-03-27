#ifndef _SOFTIRQ_
#define _SOFTIRQ_

#include "variables.pml"
#include "helper.pml"
#include "sched.pml"
#include "sched_bitmap.pml"
//#include "systick.pml"

/* irq_pending[0] is useless, let ir records the softirq run bit */
#define GET_SOFTIRQRUN   get_bit(0, irq_pending)
#define SET_SOFTIRQRUN   set_bit(0, irq_pending)
#define CLEAR_SOFTIRQRUN clear_bit(0, irq_pending)

#define PRIO_TASKLET_MINPRIO 31
#define TIMER_SOFTIRQ_PRIO 0

#define NO_BH_TASK 0
#define BH_SYSTICK 1

#define NBSOFTIRQ 1
typedef prio_struct {
    unsigned map : NBSOFTIRQ = 0
    byte queue[NBSOFTIRQ * NB_WAIT_TASKS] = UNKNOWN
};
prio_struct prio_tasklet;

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
    :: !GET_SOFTIRQRUN ->
        sched_enqueue(SOFTIRQ, tid);
        AWAITS(tid, SET_SOFTIRQRUN)
    :: else
    fi
}

inline tasklet_action(ret, tid)
{
    do
    :: if
       :: prio_tasklet.map != 0 ->
           AWAITS(tid, find_first_bit(prio_tasklet.map, max_prio, NBSOFTIRQ - 1));
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
