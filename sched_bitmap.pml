#ifndef _SCHED_BITMAP_
#define _SCHED_BITMAP_

#include "variables.pml"
#include "helper.pml"
#include "ti.pml"
#include "sched.pml"

#define NB_WAIT_TASKS (NBUSERS + 1)
typedef bitmap_struct {
    unsigned map : 31 = 0;
    byte queue[31 * NB_WAIT_TASKS] = UNKNOWN
};

/*
 * _bm[0] is active queue, denote as _bm[SCHED_BITMAP_ACTIVE].
 * _bm[1] is expire queue, denote as _bm[SCHED_BITMAP_EXPIRE].
 *
 * If the `sched.is_swap` is been set to 1, the active and expire queue
 * will be exchanged through the macro SCHED_BITMAP_ACTIVE and
 * SCHED_BITMAP_EXPIRE.
 */
typedef sched_struct {
    bitmap_struct _bm[2];
    bit is_swap
};

sched_struct sched;

#define SCHED_BITMAP_ACTIVE (0 | sched.is_swap)
#define SCHED_BITMAP_EXPIRE (1 ^ sched.is_swap)

inline bitmap_first_entry(bm, p, ret)
{
    ret = bm.queue[p * NB_WAIT_TASKS + 0]
}

inline find_next_thread(bm, ret, tid)
{
    AWAITS(tid, find_first_bit(bm.map, max_prio));

    // TODO: IDLE_THREAD, idle_thread is in privileged mode
    if
    :: max_prio == 31 ->
        AWAITS(tid, ret = IDLE_THREAD)
    :: else ->
        AWAITS(tid, bitmap_first_entry(bm, max_prio, ret))
    fi;
    AWAITS(tid, assert(ret != UNKNOWN))
}

// TODO: move out of the sched_bitmap.pml
inline add_queue_tail(new, prio, bm)
{
    for (idx: 0 .. (NB_WAIT_TASKS - 1)) {
        if
        :: bm.queue[prio * NB_WAIT_TASKS + idx] == UNKNOWN ->
            bm.queue[prio * NB_WAIT_TASKS + idx] = new;
            break
        :: else ->
            // TODO: What happen if all slots are full?
            assert(idx < NB_WAIT_TASKS)
        fi
    }
    idx = 0;
}

inline sched_bitmap_enqueue(new, prio, tid)
{
    AWAITS(tid, add_queue_tail(new, prio, sched._bm[SCHED_BITMAP_ACTIVE]));
    AWAITS(tid, set_bit(prio, sched._bm[SCHED_BITMAP_ACTIVE].map))
}

inline del_queue(del, prio, bm)
{
    for (idx: 0 .. (NB_WAIT_TASKS - 1)) {
        if
        :: (bm.queue[prio * NB_WAIT_TASKS + idx] == del) && !del_queue_check ->
            del_queue_check = true;
        :: else ->
            skip
        fi;
        if
        :: del_queue_check ->
            if
            :: idx == (NB_WAIT_TASKS - 1) ->
                bm.queue[prio * NB_WAIT_TASKS + idx] = UNKNOWN
            :: else ->
                bm.queue[prio * NB_WAIT_TASKS + idx] = 
                    bm.queue[prio * NB_WAIT_TASKS + idx + 1]
            fi
        :: else ->
            skip
        fi
    }
    idx = 0;
    del_queue_check = false
}

inline sched_bitmap_dequeue(dequeue, prio, bm, tid)
{
    if
    :: dequeue != curUser ->
        AWAITS(tid, del_queue(dequeue, prio, bm));
        if
        :: bm.queue[prio * NB_WAIT_TASKS + 0] == UNKNOWN ->
            /* list empty */
            AWAITS(tid, clear_bit(prio, bm.map))
        :: else ->
            AWAITS(tid, skip)
        fi
    :: else ->
        /* active thread is not in the runqueue */
        AWAITS(tid, skip)
    fi
}

inline sched_bitmap_elect(flags, tid)
{
    find_next_thread(sched._bm[SCHED_BITMAP_ACTIVE], nextUser, tid);

    /* check each thrd timeslice in active queue */
    /* if necessary swap active and expire queue */
    find_next_thread(sched._bm[SCHED_BITMAP_EXPIRE], tempUser, tid);
    if
    :: (nextUser == IDLE_THREAD) && (tempUser != IDLE_THREAD) ->
        AWAITS(tid, sched.is_swap = sched.is_swap ^ 1);
        find_next_thread(sched._bm[SCHED_BITMAP_ACTIVE], nextUser, tid)
    :: else ->
        AWAITS(tid, skip)
    fi;

    /* idle thread */
    if
    :: nextUser != IDLE_THREAD ->
        sched_bitmap_dequeue(nextUser, get_ti_prio(nextUser), sched._bm[SCHED_BITMAP_ACTIVE], tid)
    :: else ->
        AWAITS(tid, skip)
    fi;

    /* context switch */
    if
    :: flags == SCHED_OPT_RESTORE_ONLY ->
        AWAITS(tid, curUser = nextUser);
        AWAITS(tid, thread_restore(curUser))
    :: else ->
        if
        :: (nextUser == IDLE_THREAD) || (nextUser == curUser) ->
            AWAITS(tid, skip)
        :: flags == SCHED_OPT_TICK ->
            /* task enqueue to SCHED_BITMAP_EXPIRE */
            AWAITS(tid, add_queue_tail(curUser, get_ti_prio(curUser), sched._bm[SCHED_BITMAP_EXPIRE]));
            AWAITS(tid, set_bit(get_ti_prio(curUser), sched._bm[SCHED_BITMAP_EXPIRE].map));
            AWAITS(tid, ti[curUser - USER0].ti_state = THREAD_STATE_EXPIRED)
        fi;
        AWAITS(tid, switch_to(curUser));
        AWAITS(tid, curUser = nextUser);
        AWAITS(tid, thread_restore(curUser));
    fi
}

#endif /* _SCHED_BITMAP_ */
