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

inline find_first_bit(addr, ret, pri_min)
{
    ret = 0;
    for (idx: 0 .. pri_min) {
        if
        :: (addr & (1 << idx)) == 0 -> ret = ret + 1;
        :: else -> break
        fi
    }
    idx = 0
}

inline list_add_tail(new, stack, base, size)
{
    for (idx: 0 .. (size - 1)) {
        if
        :: stack.queue[base + idx] == UNKNOWN ->
            stack.queue[base + idx] = new;
            break
        :: else -> assert(idx < (size - 1) || stack.queue[base + idx] != new)
        /* increase size if fail */
        fi
    }
    idx = 0
}

inline list_del(del, stack, base, size)
{
    for (idx: 0 .. (size - 1)) {
        if
        :: stack.queue[base + idx] == del && !del_queue_check ->
            del_queue_check = true;
            stack.queue[base + idx] = UNKNOWN
        :: else ->
            if
            :: del_queue_check ->
                stack.queue[base + idx - 1] = stack.queue[base + idx]
                if
                :: idx == (size - 1) ->
                    stack.queue[base + idx] = UNKNOWN
                :: else
                fi
            :: else
            fi
        fi
    }
    idx = 0;
    del_queue_check = false
}

#endif /* _HELPER_ */
