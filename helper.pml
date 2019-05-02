#ifndef _HELPER_
#define _HELPER_

#define get_bit(b, word) ((word >> b) & 1)

inline set_bit(b, word)
{
    word = word | (1 << b)
}

inline clear_bit(b, word)
{
    word = word & ~(1 << b)
}

inline find_first_bit(addr, ret, pri_min, tid)
{
    AWAITS(tid, ret = 0);
    for (idx: 0 .. pri_min) {
        if
        :: SELE(tid, (addr & (1 << idx)) == 0) ->
            AWAITS(tid, ret = ret + 1)
        :: ELSE(tid, (addr & (1 << idx)) == 0) ->
            A_AWAITS(tid, break)
        fi
    }
    A_AWAITS(tid, idx = 0)
}

inline list_add_tail(new, stack, base, size, tid)
{
    for (idx: 0 .. (size - 1)) {
        if
        :: SELE(tid, stack.queue[base + idx] == UNKNOWN) ->
            AWAITS(tid, stack.queue[base + idx] = new);
            A_AWAITS(tid, break)
        :: ELSE(tid, stack.queue[base + idx] == UNKNOWN) ->
            assert(idx < (size - 1) && stack.queue[base + idx] != new)
        fi
    }
    A_AWAITS(tid, idx = 0)
}

inline list_del(del, stack, base, size, tid)
{
    for (idx: 0 .. (size - 1)) {
        if
        :: SELE(tid, stack.queue[base + idx] == del && !del_queue_check) ->
            AWAITS(tid, del_queue_check = true);
            AWAITS(tid, stack.queue[base + idx] = UNKNOWN)
        :: SELE(tid, del_queue_check) ->
            AWAITS(tid, stack.queue[base + idx - 1] = stack.queue[base + idx]);
            if
            :: SELE(tid, idx == (size - 1)) ->
                AWAITS(tid, stack.queue[base + idx] = UNKNOWN)
            :: ELSE(tid, idx == (size - 1))
            fi
        :: ELSE(tid, (stack.queue[base + idx] == del && !del_queue_check) || del_queue_check)
        fi
    }
    A_AWAITS(tid, idx = 0);
    AWAITS(tid, assert(del_queue_check); del_queue_check = false)
}

#endif /* _HELPER_ */
