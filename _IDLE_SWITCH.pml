#define IDLE    idle_check
#define SWITCH  switching_check

#define PRECEDES(a, b) (!(b) W ((a) && !(b)))

ltl { PRECEDES(IDLE, SWITCH) }
