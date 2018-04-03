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

#ifndef _VARIABLES_
#define _VARIABLES_

mtype:svc_t = { SYS_MUTEX_LOCK, SYS_MUTEX_UNLOCK, SYS_PTHREAD_YIELD,
                SYS_COND_WAIT, SYS_COND_SIGNAL };
chan svc_chan = [0] of { mtype:svc_t };

bit PendSV_pending = 0;
unsigned irq_pending : NBINTS = 0;
unsigned ghost_direct_AT : NBINTS = 0;
byte irq_prio[NBINTS + 2];
byte AT;
byte ATStack[NBATSTACK] = UNKNOWN;
short ATTop;
byte curUser;

inline sys_call(__svc_type)
{
    d_step {
        assert(ATTop < 0 && irq_pending == 0);
        assert(ghost_direct_AT == 0);

        /* push_and_change_AT(SVC) is placed in pikoRT.pml, write directly */
        ATTop = ATTop + 1;
        assert(ATTop < NBATSTACK);
        ATStack[ATTop] = AT;
        AT = SVC
    };

    /* rendezvous chan will block the process, need to place outside d_step */
    svc_chan ! __svc_type;
    (evalPID == AT)
}

inline switch_to(proc)
{
    assert(USER0 <= proc && proc <= SOFTIRQ && ATTop == 0);
    assert(proc == ATStack[ATTop])
//    FOR_CTXT_IDX {
//        ctxt_ATStack[(proc - USER0) * NBCTXT + idx] = ATStack[idx]
//    }
//    idx = 0
}

inline thread_restore(proc)
{
    assert(USER0 <= proc && proc <= SOFTIRQ && ATTop == 0);
    ATStack[ATTop] = proc;
//    FOR_CTXT_IDX {
//        ATStack[idx] = ctxt_ATStack[(proc - USER0) * NBCTXT + idx]
//    }
//    idx = 0;
    for (idx: 1 .. (NBATSTACK - 1)) {
        assert(ATStack[idx] == UNKNOWN)
    }
    idx = 0
}

inline system_initialize()
{
    curUser = USER0;
    AT = USER0;
    ATTop = -1;

    /* setting exceptin priority */
    irq_prio[SVC] = 16;
    irq_prio[PendSV] = 16;
    FOR_EXCEP_IDX {
        if
        /* priority 3 for systick */
        :: idx == 2 -> irq_prio[idx] = 3
        /* minimal priority for others */
        :: else -> irq_prio[idx] = 16
        fi
    }
    idx = 0;

//    FOR_USER_IDX {
//        ctxt_ATStack[(idx - USER0) * NBCTXT + 0] = idx
//    }
//    idx = 0;
//    ctxt_ATStack[(SOFTIRQ - USER0) * NBCTXT + 0] = SOFTIRQ
}

#endif /* _VARIABLES_ */
