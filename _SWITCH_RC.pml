#define SWITCH  switching_check
#define RC      race_condition_check

#define PRECEDES(a, b) (!(b) W ((a) && !(b)))

ltl { PRECEDES(SWITCH, RC) }
