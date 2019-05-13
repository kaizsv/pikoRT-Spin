#define RQ      runqueue_check
#define LI      list_check
#define RC      race_condition_check

#define PRECEDES(a, b) (!(b) W ((a) && !(b)))

ltl { PRECEDES(RQ || LI, RC) }
