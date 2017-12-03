#ifndef _SYSTICK_
#define _SYSTICK_

#include "variables.pml"

/* TODO: the systick_bh need to handle system call sys_msleep function */
/*       to resched the specific user task after msecs. The sys_msleep */
/*       will dequeue the current task. After msecs, the systick_bh will */
/*       call the callback function to enqueue the user task. */
inline systick_bh(tid)
{
    AWAITS(tid, skip)
}

#endif /* _SYSTICK_ */
