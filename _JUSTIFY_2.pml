#define RQ      runqueue_check
#define LI      list_check
#define RC      race_condition_check

ltl { [](!RQ && !LI && !RC) }
