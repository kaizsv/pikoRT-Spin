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
#define NBUSERS 2
#define NBINTS 2
#define SVC 0
#define PendSV 1
#define USER0 (2 + NBINTS)
#define SOFTIRQ (2 + NBINTS + NBUSERS)
#define NBROUTS (2 + NBINTS + NBUSERS)
#define NBALL (NBROUTS + 1)
#define NBCTXT NBALL
#define UNKNOWN 255
#define IDLE_THREAD 254

#define FOR_EXCEP_IDX for (idx: 2 .. (2 + NBINTS - 1))
#define FOR_USER_IDX for (idx: USER0 .. (USER0 + NBUSERS - 1))
#define FOR_USER_LOCAL_IDX for (idx: 0 .. (NBUSERS - 1))
#define FOR_ALL_IDX for (idx: 0 .. (NBALL - 1))
#define FOR_CTXT_IDX for (idx: 0 .. (NBCTXT - 1))
#define FOR_ATTOP_IDX for (idx: 0 .. ATTop)

#define AWAITS(pid, C) atomic { (pid == AT); C }

#ifndef _VARIABLES_
#define _VARIABLES_

mtype = { DEFAULT_SYS, SYS_MUTEX_LOCK, SYS_MUTEX_UNLOCK, SYS_PTHREAD_YIELD};
mtype svc_type = DEFAULT_SYS;

int irq_pending;
byte irq_prio[NBINTS + 2];
bit PendSVReq;
pid AT;
pid ATStack[NBALL];
int ATTop;
pid nextUser;
pid curUser;

//bit ctxt_preempt[NBUSERS];
pid ctxt_ATStack[(NBUSERS + 1) * NBCTXT];//TODO: can be smaller
int ctxt_ATTop[NBUSERS + 1];

bit ghost_softirq;
int ghost_direct_AT;
bit ghost_svc;

inline switch_to(proc)
{
    d_step {
    assert(USER0 <= proc && proc <= SOFTIRQ);
    ctxt_ATTop[proc - USER0] = ATTop;
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
    ATTop = ctxt_ATTop[proc - USER0];
    FOR_CTXT_IDX {
        ATStack[idx] = ctxt_ATStack[(proc - USER0) * NBCTXT + idx]
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

    /* setting context */
    FOR_USER_IDX {
        for (idx2: 1 .. (NBCTXT - 1)) {
            ctxt_ATStack[(idx - USER0) * NBCTXT + idx2] = UNKNOWN
        }
        idx2 = 0;

        ctxt_ATTop[idx - USER0] = 0;
        ctxt_ATStack[(idx - USER0) * NBCTXT + 0] = idx
    }
    idx = 0;
    for (idx2: 1 .. (NBCTXT - 1)) {
        ctxt_ATStack[(SOFTIRQ - USER0) * NBCTXT + idx2] = UNKNOWN
    }
    idx2 = 0;
    ctxt_ATTop[SOFTIRQ - USER0] = 0;
    ctxt_ATStack[(SOFTIRQ - USER0) * NBCTXT + 0] = SOFTIRQ
}

#endif /* _VARIABLES_ */
