# pikoRT-Spin
A Promela model of pikoRT under the Spin model checker. https://github.com/Piko-RT/pikoRT

Make sure you have enough RAM on your machine. 52G is the default setting and can be modified in Makefile. You can add `MA=<24>` to reduce the memory usage but increase the running time.

## Three types of check
### Safety
make safety_bfs  
A simple command for checking if there exists any wrong of the Promela model. The memory limit is 1GB.
  
make safety_dfs_full  
A complete check using DFS algorithms, the default setting of memory limit is 52GB and search depth is 100,000,000.

### LTL acceptance cycles
There are two LTL propertyies, starvation_free and deadlock_free.  
make ltl_deadlock_free  
make ltl_starvation_free  
However, the LTL formulas are too complicated to verify.
