/* pid:
 *                           2 ~      (2+NBINTS)~
 *   0         1        (2+NBINTS-1)  (SOFTIRQ-1) (2+NBINTS+NBUSERS)
 *  svc  ||  pendsv  ||  interrupts  ||  users  ||  softirq
 *
 * Note:
 * softirq is one of the user tasks.
 *
 * Warning:
 * The number of users and interrupts must smaller or equal than seven.
 * To simplify the verification result, this model use bitwise operator 
 * to repesent the usage of arrays. Change partial variables' datatype
 * from "byte" to "short" if you want to verify more processes.
 *
 * Because the data structure of context switch is regular, we remove the
 * usage of CTXT data structure.
 *     Strictly speaking, the ctxt_ATStack need to store the whole ATStack.
 *     But durning the context switch, the ATStack remains regular. To
 *     reduce size of ctxt_ATStack, the NBCTXT is setting to 1 and there
 *     is no need to store the ctxt_ATTop. If the NBCTXT must be set greater
 *     than 1, each ATStack in ctxt_ATStack need to be UNKNOWN except the
 *     ATStack[0] to be self user id and the ctxt_ATTop must be 0.
 *
 *     For example: ctxt_ATStack
 *     | 4 U U U U U U | 5 U U U U U U | 6 U U U U U U |
 *     |NBCTXT == NBALL|
 *
 *     #define NBCTXT 1
 *     byte ctxt_ATStack[(NBUSERS + 1) * NBCTXT];
 *     int ctxt_ATTop[NBUSERS + 1];
 */
#define NBUSERS 2
#define NBINTS 2
#define SVC 0
#define PendSV 1
#define USER0 (2 + NBINTS)
#define SOFTIRQ (2 + NBINTS + NBUSERS)
#define NBALL (SOFTIRQ + 1)
#define NBATSTACK (NBINTS + 2)
#define UNKNOWN 255
#define IDLE_THREAD 254

#define FOR_EXCEP_IDX for (idx: 2 .. (2 + NBINTS - 1))
#define FOR_USER_IDX for (idx: USER0 .. (USER0 + NBUSERS - 1))
#define FOR_ATTOP_IDX for (idx: 0 .. ATTop)

#define evalPID (_pid - 1)
#define AWAITS(pid, C)   d_step { (pid == AT) -> C }
#define A_AWAITS(pid, C) atomic { (pid == AT) -> C }
#define SELE(pid, C) (pid == AT) && (C)
#define ELSE(pid, C) (pid == AT) && !(C)

#ifndef _VARIABLES_
#define _VARIABLES_

mtype:svc_t = { SYS_MUTEX_LOCK, SYS_MUTEX_UNLOCK, SYS_PTHREAD_YIELD,
                SYS_COND_WAIT, SYS_COND_SIGNAL };
chan svc_chan = [0] of { mtype:svc_t };

bit PendSV_pending = 0;
unsigned irq_pending : NBINTS = 0;
unsigned ghost_direct_AT : NBINTS = 0;
byte irq_prio[NBINTS + 2] = 16;
byte AT = USER0;
byte ATStack[NBATSTACK] = UNKNOWN;
short ATTop = -1;
byte curUser = USER0;

inline switch_to(proc)
{
    assert(USER0 <= proc && proc <= SOFTIRQ && ATTop == 0);
    assert(proc == ATStack[ATTop])
}

inline thread_restore(proc)
{
    assert(USER0 <= proc && proc <= SOFTIRQ && ATTop == 0);
    ATStack[ATTop] = proc;
    for (idx: 1 .. (NBATSTACK - 1)) {
        assert(ATStack[idx] == UNKNOWN)
    }
    idx = 0
}

inline system_initialize()
{
    /* setting exceptin priority */
    FOR_EXCEP_IDX {
        if
        /* priority 3 for systick */
        :: idx == 2 -> irq_prio[idx] = 3
        /* minimal priority for others */
        :: else
        fi
    }
    idx = 0;
}

#endif /* _VARIABLES_ */
