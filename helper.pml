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

#endif /* _HELPER_ */
