#ifndef _SOFTIRQ_
#define _SOFTIRQ_

#include "variables.pml"
#include "helper.pml"
#include "sched.pml"
#include "sched_bitmap.pml"
//#include "systick.pml"

#define PRIO_TASKLET_MINPRIO 31
#define TIMER_SOFTIRQ_PRIO 0

mtype:tasklet_t = { NO_BH_TASK, BH_SYSTICK };

// XXX: increase if more than one bottom half tasks
#define NBSOFTIRQ 1
#define NB_WAIT_TASKLETS 1
typedef prio_struct {
    unsigned map : NBSOFTIRQ = 0
    byte queue[NBSOFTIRQ * NB_WAIT_TASKLETS] = UNKNOWN
};
prio_struct prio_tasklet;

// XXX: Because there are only one bottom half task in this model.
//      To prevent redundant task asserting into the slot, check
//      if map is zero or not.
// TODO: Rewrite if there are more than one bottom half tasks
inline tasklet_bitmap_enqueue(new, prio, tid)
{
    if
    :: SELE(tid, prio_tasklet.map == 0) ->
        AWAITS(tid, add_tail(new, prio_tasklet, prio, NB_WAIT_TASKLETS));
        AWAITS(tid, set_bit(prio, prio_tasklet.map))
    :: ELSE(tid, prio_tasklet.map == 0)
    fi
}

inline tasklet_schedule(task, prio, tid)
{
    tasklet_bitmap_enqueue(task, prio, tid);

    /* raise softirq */
    if
    :: SELE(tid, !softirq_run) ->
        sched_enqueue(SOFTIRQ, tid);
        AWAITS(tid, softirq_run = true)
    :: ELSE(tid, !softirq_run)
    fi
}

/* copy from bitmap_first_entry besides the size of NB_WAIT_TASKLETS */
inline tasklet_first_entry(bm, prio, ret)
{
    ret = bm.queue[prio * NB_WAIT_TASKLETS + 0];
    assert(ret != UNKNOWN)
}

/* copy from bitmap_queue_del besides the size of NB_WAIT_TASKLETS */
inline tasklet_queue_del(del, prio, bm, tid)
{
    AWAITS(tid, list_del(del, bm, prio * NB_WAIT_TASKLETS, NB_WAIT_TASKLETS));
    if
    :: SELE(tid, bm.queue[prio * NB_WAIT_TASKLETS + 0] == UNKNOWN) ->
        AWAITS(tid, clear_bit(prio, bm.map))
    :: ELSE(tid, bm.queue[prio * NB_WAIT_TASKLETS + 0] == UNKNOWN)
    fi
}

inline tasklet_action(ret, tid)
{
    do
    :: SELE(tid, prio_tasklet.map != 0) ->
        AWAITS(tid, find_first_bit(prio_tasklet.map, max_prio, NBSOFTIRQ - 1));
        AWAITS(tid, tasklet_first_entry(prio_tasklet, max_prio, ret); assert(ret == BH_SYSTICK));
        tasklet_queue_del(ret, max_prio, prio_tasklet, tid);
        /* the elected tasklet must be systick buttom half */

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
        //systick_bh(tid)
    :: ELSE(tid, prio_tasklet.map != 0) ->
        A_AWAITS(tid, ret = NO_BH_TASK; break)
    od
}

#endif /* _SOFTIRQ_ */
