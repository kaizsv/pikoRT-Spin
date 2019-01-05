# pikoRT-Spin
A Promela model of pikoRT under the Spin model checker. https://github.com/Piko-RT/pikoRT

Make sure you have enough RAM on your machine. 52G is the default setting and can be modified in Makefile. You can add `MA=<24>` to reduce the memory usage but increase the running time.

## Two types of check
### Safety
```make safety_dfs_full``` or ```make safety_bfs``` <br />
A complete check using DFS or BFS algorithms, the default setting of memory limit is 52GB and search depth is 100,000,000.

### LTL acceptance cycles
There are two LTL propertyies, starvation_free and deadlock_free. You can find the properties name in the ```specifications.pml``` file or write your own properties. <br />
```make acceptance_ltl_full CLAIM=<propertie name>``` or ```make ltl_deadlock_free```

## Documents
For more informations, please see the wiki page. https://github.com/kaizsv/pikoRT-Spin/wiki.
