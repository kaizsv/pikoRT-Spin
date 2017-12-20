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
    unsigned map : NBITMAP_BIT = 0;
    byte queue[NBITMAP_BIT * NB_WAIT_TASKS] = UNKNOWN
};

/* _bm[0] is active queue, denote as _bm[SCHED_BITMAP_ACTIVE].
 * _bm[1] is expire queue, denote as _bm[SCHED_BITMAP_EXPIRE].
 *
 * If the `sched.is_swap` is been set to 1, the active and expire queue
 * will be exchanged through the macro SCHED_BITMAP_ACTIVE and
 * SCHED_BITMAP_EXPIRE. */
typedef sched_struct {
    bitmap_struct _bm[2];
    bit is_swap
};

sched_struct sched;

#define SCHED_BITMAP_ACTIVE (0 | sched.is_swap)
#define SCHED_BITMAP_EXPIRE (1 ^ sched.is_swap)

inline find_next_thread(bm, ret, tid)
{
    AWAITS(tid, find_first_bit(bm.map, max_prio, PRI_MIN));

    if
    :: max_prio == NBITMAP_BIT ->
        /* empty bm.map */
        AWAITS(tid, ret = IDLE_THREAD)
    :: else ->
        /* bitmap_first_entry() */
        AWAITS(tid, ret = bm.queue[max_prio * NB_WAIT_TASKS + 0])
    fi;
    AWAITS(tid, assert(ret != UNKNOWN))
}

// XXX: can move out of the sched_bitmap.pml
inline add_queue_tail(new, prio, bm)
{
    /* increase BITMAP_BITS if fails */
    assert(prio < NBITMAP_BIT);
    for (idx: 0 .. (NB_WAIT_TASKS - 1)) {
        if
        :: bm.queue[prio * NB_WAIT_TASKS + idx] == new ->
            assert(bm.map == prio_tasklet.map);
            break
        :: bm.queue[prio * NB_WAIT_TASKS + idx] == UNKNOWN ->
            bm.queue[prio * NB_WAIT_TASKS + idx] = new;
            break
        :: else -> assert(idx != (NB_WAIT_TASKS - 1))
        // TODO: What happen if all slots are full?
        fi
    }
    idx = 0
}

inline sched_bitmap_enqueue(new, prio, tid)
{
    AWAITS(tid, add_queue_tail(new, prio, sched._bm[SCHED_BITMAP_ACTIVE]));
    AWAITS(tid, set_bit(prio, sched._bm[SCHED_BITMAP_ACTIVE].map))
}

/* XXX: del_queue will remove the task from runqueue and move the slots
 * behind the task forward to act as the delection in link list. */
inline del_queue(del, prio, bm)
{
    for (idx: 0 .. (NB_WAIT_TASKS - 1)) {
        if
        :: (bm.queue[prio * NB_WAIT_TASKS + idx] == del) && !del_queue_check ->
            del_queue_check = true
        :: else ->
            if
            :: del_queue_check ->
                /* del_queue_check */
                bm.queue[prio * NB_WAIT_TASKS + idx - 1] =
                    bm.queue[prio * NB_WAIT_TASKS + idx];
                if
                :: idx == (NB_WAIT_TASKS - 1) ->
                    bm.queue[prio * NB_WAIT_TASKS + idx] = UNKNOWN
                :: else -> skip
                fi
            :: else -> skip
            fi
        fi
    }
    idx = 0;
    del_queue_check = false
}

inline bitmap_queue_del(del, prio, bm, tid)
{
    AWAITS(tid, del_queue(del, prio, bm));
    if
    :: bm.queue[prio * NB_WAIT_TASKS + 0] == UNKNOWN ->
        /* list empty */
        AWAITS(tid, clear_bit(prio, bm.map))
    :: else ->
        AWAITS(tid, skip)
    fi
}

inline sched_bitmap_dequeue(dequeue, prio, bm, tid)
{
    if
    :: dequeue != curUser ->
        bitmap_queue_del(dequeue, prio, bm, tid)
    :: else ->
        /* active thread is not in the runqueue */
        AWAITS(tid, skip)
    fi
}

inline swap_sched_state()
{
    sched.is_swap = sched.is_swap ^ 1;
    swap_sched_state_map()
}

inline sched_bitmap_elect(flags, tid)
{
    find_next_thread(sched._bm[SCHED_BITMAP_ACTIVE], nextUser, tid);

    /* check each thrd timeslice in active queue
     * if necessary swap active and expire queue */
    find_next_thread(sched._bm[SCHED_BITMAP_EXPIRE], tempUser, tid);
    if
    :: (nextUser == IDLE_THREAD && tempUser != IDLE_THREAD) ->
        AWAITS(tid, swap_sched_state());
        find_next_thread(sched._bm[SCHED_BITMAP_ACTIVE], nextUser, tid)
    :: else ->
        AWAITS(tid, skip)
    fi;

    /* idle thread */
    if
    :: nextUser != IDLE_THREAD ->
        bitmap_queue_del(nextUser, get_ti_prio(nextUser), sched._bm[SCHED_BITMAP_ACTIVE], tid)
    :: else ->
        AWAITS(tid, skip)
    fi;

    /* context switch */
    if
//    TODO: thread exit has not been implemented yet,
//          comment to prevent unreached statement
//    :: flags == SCHED_OPT_RESTORE_ONLY ->
//        /* restore only */
//        AWAITS(tid, curUser = nextUser);
//        AWAITS(tid, thread_restore(curUser))
    :: (nextUser == IDLE_THREAD || nextUser == curUser) ->
        AWAITS(tid, assert(flags != SCHED_OPT_RESTORE_ONLY))
    :: else ->
        AWAITS(tid, assert(flags != SCHED_OPT_RESTORE_ONLY))
        if
        :: flags == SCHED_OPT_TICK ->
            /* task enqueue to SCHED_BITMAP_EXPIRE */
            AWAITS(tid, add_queue_tail(curUser, get_ti_prio(curUser), sched._bm[SCHED_BITMAP_EXPIRE]));
            AWAITS(tid, set_bit(get_ti_prio(curUser), sched._bm[SCHED_BITMAP_EXPIRE].map));
            AWAITS(tid, ti[curUser - USER0].ti_state = THREAD_STATE_EXPIRED)
        :: else ->
            AWAITS(tid, skip)
        fi;
        AWAITS(tid, switch_to(curUser));
        AWAITS(tid, curUser = nextUser);
        AWAITS(tid, thread_restore(curUser))
    fi
}

#endif /* _SCHED_BITMAP_ */
