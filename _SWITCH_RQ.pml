#define SWITCH  switching_check
#define RQ      runqueue_check

#define PRECEDES(a, b) (!(b) W ((a) && !(b)))

ltl { PRECEDES(SWITCH, RQ) }
