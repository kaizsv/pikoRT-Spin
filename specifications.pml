//          init  svc  pendsv  systick  interrupt  consumer  producer  softirq
// evalPID         0     1        2         3         4         5         6
//  _pid     0     1     2        3         4         5         6         7
//
// _pid is a fixed value in Spin.
// _last is the process id of the last statement.

/** Exclude continuous exceptions and livelock
* Original: !(<>[](_last == 2 || _lasst == 3 || _last == 4 || _last == 7))
* push neg: []<>(_last != 2 && _lasst != 3 && _last != 4 && _last != 7)
* equivalence:    []<>(_last == 1 || _last == 5 || _last == 6)
* simplification: []<>(_last == 5 || _last == 6)
*
* There is a false positive path about single asynchronous exception
* interrupts and return from exception all the time. Thus we filter out this
* situation. Note the _pid 2, 3, and 4 are the asynchronous exceptions.
*
* Softirq has 2 loops. Both loops might cause livelock. The outer loop requires
* `sched_yield' to give up the execution. But priority of Softirq is higher than
* others, after the system call softirq is still elected. The inner loop is to
* execute the bottom half task. If Systick always inserts its B.H. into tasklet,
* Softirq inner loop runs infinitely.
*
* The formula only filters out both situations without Consumer or Producer
* loops infinitely. Note that there is also an infinite loop in the mutex lock
* routines. The specification can detect the block of the inner loop inside the
* mutex lock.
*/
#define EX_CONT_INTS_LIVELOCK []<>(_last == 5 || _last == 6)

/** Exclude interrupts storm
* Original: !([]<>(interrupts@iret || systick@iret) && []<>(T_c@lock_0 || T_p@unlock_0...))
*
* Because exception return resets the exclusive label of all addresses, the
* mutex lock routine needs to reload the value of the mutex lock. There might
* be a situation that asynchronous exceptions keep interrupting and the mutex
* lock routine is blocked inside the inner loop. We call this situation the
* interrupts storm.
*/
#define EX_INT_STORM (<>[](!interrupts@iret && !systick@iret) || <>[](!consumer@lock_0 && !producer@lock_0))
#define EX_INT_STORM_C (<>[](!interrupts@iret && !systick@iret) || <>[](!consumer@lock_0 && !producer@lock_0 && !consumer@unlock_0))
#define EX_INT_STORM_P (<>[](!interrupts@iret && !systick@iret) || <>[](!consumer@lock_0 && !producer@lock_0 && !producer@unlock_0))

/** LIVENESS
* If `a' is set, `b' must be set in the future path.
*/
#define LIVENESS(a, b) ([]((a) -> <>(b)))

ltl consumer_starvation_free { (EX_CONT_INTS_LIVELOCK && EX_INT_STORM_P) -> LIVENESS(consumer@lock_0, consumer@cs) }
ltl producer_starvation_free { (EX_CONT_INTS_LIVELOCK && EX_INT_STORM_C) -> LIVENESS(producer@lock_0, producer@cs) }
ltl deadlock_free { (EX_CONT_INTS_LIVELOCK && EX_INT_STORM) -> LIVENESS(consumer@lock_0 && producer@lock_0, consumer@cs || producer@cs) }
