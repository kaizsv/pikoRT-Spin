#ifndef _SCHED_BITMAP_
#define _SCHED_BITMAP_

#include "variables.pml"
#include "helper.pml"
#include "ti.pml"
#include "sched.pml"

/* XXX: increase NB_WAIT_TASKS if more than two user tasks are
 *      in the same priority */
#define NB_WAIT_TASKS 3
typedef bitmap_struct {
    unsigned map : NBITMAP_BIT = 0
    byte queue[NBITMAP_BIT * NB_WAIT_TASKS] = UNKNOWN
};

/* _bm[0] is active queue, denote as _bm[SCHED_BITMAP_ACTIVE].
 * _bm[1] is expire queue, denote as _bm[SCHED_BITMAP_EXPIRE].
 *
 * If the `SCHED_STATE_MAP` is been set to 1, the active and expire
 * runqueue will be exchanged through the macro SCHED_BITMAP_ACTIVE
 * and SCHED_BITMAP_EXPIRE. */
bitmap_struct sched_bm[2];

/**
* ACTIVED: 0 | THREAD_SCHED_STATE_SWAP
* EXPIRED: 1 ^ THREAD_SCHED_STATE_SWAP
*/
bit SCHED_STATE_MAP = 0;
#define SCHED_BITMAP_ACTIVE (0 | SCHED_STATE_MAP)
#define SCHED_BITMAP_EXPIRE (1 ^ SCHED_STATE_MAP)

inline swap_sched_state_map()
{
    SCHED_STATE_MAP = SCHED_STATE_MAP ^ 1
}

inline add_tail(new, bm, prio, size, tid)
{
    assert(prio < NBITMAP_BIT);
    list_add_tail(new, bm, prio * size, size, tid)
}

inline bitmap_first_entry(bm, prio, ret)
{
    ret = bm.queue[prio * NB_WAIT_TASKS + 0];
    assert(ret != UNKNOWN)
}

inline find_next_thread(bm, ret, tid)
{
    AWAITS(tid, assert(ret == UNKNOWN));
    find_first_bit(bm.map, max_prio, PRI_MIN, tid);

    if
    :: SELE(tid, max_prio == NBITMAP_BIT) -> /* empty bm.map */
        AWAITS(tid, ret = IDLE_THREAD; max_prio = UNKNOWN)
    :: ELSE(tid, max_prio == NBITMAP_BIT) ->
        AWAITS(tid, bitmap_first_entry(bm, max_prio, ret); max_prio = UNKNOWN)
    fi
}

/* this compares the expire runqueue with the nextUser (active runqueue)
 * to prevent the usage of tempUser variable. */
inline compare_runqueues_to_swap(tid)
{
    find_first_bit(sched_bm[SCHED_BITMAP_EXPIRE].map, max_prio, PRI_MIN, tid);

    /* if expire runqueue has elements, the max_prio will not be NBITMAP_BIT */
    if
    :: SELE(tid, nextUser == IDLE_THREAD && max_prio != NBITMAP_BIT) ->
        AWAITS(tid, nextUser = UNKNOWN; swap_sched_state_map());
        find_next_thread(sched_bm[SCHED_BITMAP_ACTIVE], nextUser, tid)
    :: ELSE(tid, nextUser == IDLE_THREAD && max_prio != NBITMAP_BIT) ->
        max_prio = UNKNOWN
    fi
}

inline sched_bitmap_enqueue(new, prio, tid)
{
    add_tail(new, sched_bm[SCHED_BITMAP_ACTIVE], prio, NB_WAIT_TASKS, tid);
    AWAITS(tid, set_bit(prio, sched_bm[SCHED_BITMAP_ACTIVE].map))
}

inline bitmap_queue_del(del, prio, bm, tid)
{
    list_del(del, bm, prio * NB_WAIT_TASKS, NB_WAIT_TASKS, tid);
    if
    :: SELE(tid, bm.queue[prio * NB_WAIT_TASKS + 0] == UNKNOWN) ->
        /* list empty */
        AWAITS(tid, clear_bit(prio, bm.map))
    :: ELSE(tid, bm.queue[prio * NB_WAIT_TASKS + 0] == UNKNOWN)
    fi
}

inline sched_bitmap_dequeue(dequeue, prio, bm, tid)
{
    if
    :: SELE(tid, dequeue != curUser) ->
        bitmap_queue_del(dequeue, prio, bm, tid)
    :: ELSE(tid, dequeue != curUser)
        /* active thread is not in the runqueue */
    fi
}

inline sched_bitmap_elect(flags, tid)
{
    find_next_thread(sched_bm[SCHED_BITMAP_ACTIVE], nextUser, tid);

    /* check each thrd timeslice in active queue
     * if necessary swap active and expire queue */
    compare_runqueues_to_swap(tid);

    if
    :: SELE(tid, nextUser != IDLE_THREAD) ->
        bitmap_queue_del(nextUser, get_ti_prio(nextUser), sched_bm[SCHED_BITMAP_ACTIVE], tid)
    :: ELSE(tid, nextUser != IDLE_THREAD) /* idle thread */
    fi;

//  TODO: thread exit has not been implemented yet,
//        comment to prevent unreached statement
    if
    :: SELE(tid, flags == SCHED_OPT_TICK && curUser != IDLE_THREAD) ->
        /* task enqueue to SCHED_BITMAP_EXPIRE */
        add_tail(curUser, sched_bm[SCHED_BITMAP_EXPIRE], get_ti_prio(curUser), NB_WAIT_TASKS, tid);
        AWAITS(tid, set_bit(get_ti_prio(curUser), sched_bm[SCHED_BITMAP_EXPIRE].map));
        AWAITS(tid, ti[curUser - USER0].ti_state = THREAD_STATE_EXPIRED)
    :: ELSE(tid, flags == SCHED_OPT_TICK && curUser != IDLE_THREAD)
    fi;
    if
    :: SELE(tid, nextUser != curUser) -> /* context switch */
        AWAITS(tid, switch_to(curUser));
        AWAITS(tid, curUser = nextUser; nextUser = UNKNOWN);
        AWAITS(tid, thread_restore(curUser); assert(curUser != UNKNOWN))
    :: ELSE(tid, nextUser != curUser) ->
        nextUser = UNKNOWN
    fi
}

#endif /* _SCHED_BITMAP_ */
