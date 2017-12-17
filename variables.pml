/* pid:
 *                           2 ~      (2+NBINTS)~
 *   0         1        (2+NBINTS-1)  (NBROUTS-1) (2+NBINTS+NBUSERS)
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
 */
#define BITMAP_BITS 3
#define NBUSERS (BITMAP_BITS - 1)
#define NBINTS 2
#define SVC 0
#define PendSV 1
#define USER0 (2 + NBINTS)
#define SOFTIRQ (2 + NBINTS + NBUSERS)
#define NBROUTS (2 + NBINTS + NBUSERS)
#define NBALL (NBROUTS + 1)
#define NBCTXT 1
#define UNKNOWN 255
#define IDLE_THREAD 254

#define FOR_EXCEP_IDX for (idx: 2 .. (2 + NBINTS - 1))
#define FOR_USER_IDX for (idx: USER0 .. (USER0 + NBUSERS - 1))
#define FOR_ALL_IDX for (idx: 0 .. (NBALL - 1))
#define FOR_CTXT_IDX for (idx: 0 .. (NBCTXT - 1))
#define FOR_ATTOP_IDX for (idx: 0 .. ATTop)

#define AWAITS(pid, C) atomic { (pid == AT); C }

#ifndef _VARIABLES_
#define _VARIABLES_

mtype = { DEFAULT_SYS, SYS_MUTEX_LOCK, SYS_MUTEX_UNLOCK, SYS_PTHREAD_YIELD };
mtype svc_type = DEFAULT_SYS;

short irq_pending;
byte irq_prio[NBINTS + 2];
bit PendSVReq;
pid AT;
pid ATStack[NBALL];
short ATTop;
pid nextUser;
pid curUser;

pid ctxt_ATStack[(NBUSERS + 1) * NBCTXT];
//int ctxt_ATTop[NBUSERS + 1];

short ghost_direct_AT;
//bit ghost_svc;

inline sys_call(__svc_type)
{
    d_step {
        assert(USER0 <= curUser && curUser <= SOFTIRQ);
        assert(ATTop < 0 && irq_pending == 0 && ghost_direct_AT == 0);
        svc_type = __svc_type;

        /* push_and_change_AT(SVC) is placed in pikoRT.pml, write directly */
        ATTop = ATTop + 1;
        assert(ATTop < NBALL);
        ATStack[ATTop] = AT;
        AT = SVC
    }
}

inline switch_to(proc)
{
    d_step {
        assert(USER0 <= proc && proc <= SOFTIRQ && ATTop == 0);
        assert(USER0 <= ATStack[ATTop] && ATStack[ATTop] <= SOFTIRQ);
        FOR_CTXT_IDX {
            ctxt_ATStack[(proc - USER0) * NBCTXT + idx] = ATStack[idx]
        }
        idx = 0
    }
}

inline thread_restore(proc)
{
    d_step {
        assert(USER0 <= proc && proc <= SOFTIRQ);
        ATTop = 0;
        FOR_CTXT_IDX {
            ATStack[idx] = ctxt_ATStack[(proc - USER0) * NBCTXT + idx]
        }
        idx = 0;
        for (idx: 1 .. (NBALL - 1)) {
            assert(ATStack[idx] == UNKNOWN)
        }
        idx = 0
    }
}

inline system_initialize()
{
    curUser = USER0;
    nextUser = UNKNOWN;
    AT = USER0;
    ATTop = -1;
    FOR_ALL_IDX {
        ATStack[idx] = UNKNOWN
    }
    idx = 0;

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

    /* XXX setting context
     * Strictly speaking, the ctxt_ATStack need to store the whole ATStack.
     * But durning the context switch, the ATStack remains UNKNOWN except
     * ATStack[0] to be curUser and ATTop to be 0.
     *
     * To reduce size of ctxt_ATStack, the NBCTXT is setting to 1 and there
     * is no need to store the ctxt_ATTop. If the NBCTXT must be set greater
     * than 1, each ATStack in ctxt_ATStack need to be UNKNOWN except the
     * ATStack[0] to be self user id and the ctxt_ATTop must be 0.
     *
     * For example: ctxt_ATStack
     * | 4 U U U U U U | 5 U U U U U U | 6 U U U U U U |
     * |NBCTXT == NBALL|
     */
    FOR_USER_IDX {
        ctxt_ATStack[(idx - USER0) * NBCTXT + 0] = idx
    }
    idx = 0;
    ctxt_ATStack[(SOFTIRQ - USER0) * NBCTXT + 0] = SOFTIRQ
}

#endif /* _VARIABLES_ */
