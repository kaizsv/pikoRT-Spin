#define SWITCH  switching_check
#define LI      list_check

#define PRECEDES(a, b) (!(b) W ((a) && !(b)))

ltl { PRECEDES(SWITCH, LI) }
