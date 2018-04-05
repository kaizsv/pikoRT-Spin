#ifndef _SCHED_BITMAP_
#define _SCHED_BITMAP_

#include "variables.pml"
#include "helper.pml"
#include "ti.pml"
#include "sched.pml"

/* XXX: increase NB_WAIT_TASKS if more than two user tasks are
 *      in the same priority */
#define NB_WAIT_TASKS 2
typedef bitmap_struct {
    unsigned map : NBITMAP_BIT = 0
    byte queue[NBITMAP_BIT * NB_WAIT_TASKS] = UNKNOWN
};

/* _bm[0] is active queue, denote as _bm[SCHED_BITMAP_ACTIVE].
 * _bm[1] is expire queue, denote as _bm[SCHED_BITMAP_EXPIRE].
 *
 * If the `THREAD_SCHED_STATE_SWAP` is been set to 1, the active and
 * expire queue will be exchanged through the macro SCHED_BITMAP_ACTIVE
 * and SCHED_BITMAP_EXPIRE. */
bitmap_struct sched_bm[2];

#define SCHED_BITMAP_ACTIVE (0 | THREAD_SCHED_STATE_SWAP)
#define SCHED_BITMAP_EXPIRE (1 ^ THREAD_SCHED_STATE_SWAP)

inline add_tail(new, bm, prio, size)
{
    assert(prio < NBITMAP_BIT);
    list_add_tail(new, bm, prio * size, size)
}

inline bitmap_first_entry(bm, prio, ret)
{
    ret = bm.queue[prio * NB_WAIT_TASKS + 0];
    assert(ret != UNKNOWN)
}

inline find_next_thread(bm, ret, tid)
{
    AWAITS(tid, find_first_bit(bm.map, max_prio, PRI_MIN));

    if
    :: max_prio == NBITMAP_BIT ->
        /* empty bm.map */
        AWAITS(tid, ret = IDLE_THREAD)
    :: else ->
        AWAITS(tid, bitmap_first_entry(bm, max_prio, ret))
    fi
}

/* this compares the expire runqueue with the nextUser (active runqueue)
 * to prevent the usage of tempUser variable. */
inline compare_runqueues_to_swap(tid)
{
    AWAITS(tid, find_first_bit(sched_bm[SCHED_BITMAP_EXPIRE].map, max_prio, PRI_MIN));

    /* if expire runqueue has elements, the max_prio will not be NBITMAP_BIT */
    if
    :: nextUser == IDLE_THREAD && max_prio != NBITMAP_BIT ->
        AWAITS(tid, swap_sched_state_map());
        find_next_thread(sched_bm[SCHED_BITMAP_ACTIVE], nextUser, tid)
    :: else
    fi
}

inline sched_bitmap_enqueue(new, prio, tid)
{
    AWAITS(tid, add_tail(new, sched_bm[SCHED_BITMAP_ACTIVE], prio, NB_WAIT_TASKS));
    AWAITS(tid, set_bit(prio, sched_bm[SCHED_BITMAP_ACTIVE].map))
}

inline bitmap_queue_del(del, prio, bm, tid)
{
    AWAITS(tid, list_del(del, bm, prio * NB_WAIT_TASKS, NB_WAIT_TASKS));
    if
    :: bm.queue[prio * NB_WAIT_TASKS + 0] == UNKNOWN ->
        /* list empty */
        AWAITS(tid, clear_bit(prio, bm.map))
    :: else
    fi
}

inline sched_bitmap_dequeue(dequeue, prio, bm, tid)
{
    if
    :: dequeue != curUser ->
        bitmap_queue_del(dequeue, prio, bm, tid)
    :: else /* active thread is not in the runqueue */
    fi
}

inline sched_bitmap_elect(flags, tid)
{
    find_next_thread(sched_bm[SCHED_BITMAP_ACTIVE], nextUser, tid);

    /* check each thrd timeslice in active queue
     * if necessary swap active and expire queue */
    compare_runqueues_to_swap(tid);

    /* idle thread */
    if
    :: nextUser != IDLE_THREAD ->
        bitmap_queue_del(nextUser, get_ti_prio(nextUser), sched_bm[SCHED_BITMAP_ACTIVE], tid)
    :: else -> assert(curUser != IDLE_THREAD)
    fi;

//    if
//    TODO: thread exit has not been implemented yet,
//          comment to prevent unreached statement
//    :: flags == SCHED_OPT_RESTORE_ONLY ->
//        /* restore only */
//        AWAITS(tid, curUser = nextUser);
//        AWAITS(tid, thread_restore(curUser))
//    :: else ->
        if
        :: flags == SCHED_OPT_TICK && curUser != IDLE_THREAD ->
            /* task enqueue to SCHED_BITMAP_EXPIRE */
            AWAITS(tid, add_tail(curUser, sched_bm[SCHED_BITMAP_EXPIRE], get_ti_prio(curUser), NB_WAIT_TASKS));
            AWAITS(tid, set_bit(get_ti_prio(curUser), sched_bm[SCHED_BITMAP_EXPIRE].map));
            AWAITS(tid, ti[curUser - USER0].ti_state = THREAD_STATE_EXPIRED)
        :: else
        fi;
        if
        :: nextUser == curUser -> skip
        :: else ->
            /* context switch */
            AWAITS(tid, switch_to(curUser));
            AWAITS(tid, curUser = nextUser);
            AWAITS(tid, thread_restore(curUser))
        fi
//    fi
}

#endif /* _SCHED_BITMAP_ */
