SPIN = spin
CC = gcc
CFLAGS = -w -O2
SPINFLAGS = -a
COMPILERTIME_FLAGS = -DXUSAFE -DCOLLAPSE

TARGET = pikoRT.pml
OUT = pan
MAXMLIMIT = 53248 # maxima memory usage 52G
MLIMIT ?= $(MAXMLIMIT)
MAXDEPTH = 100000000
RUNTIME_FLAGS = -m$(MAXDEPTH)

ifdef MA
COMPILERTIME_FLAGS += -DMA=$(MA)
endif

ifdef WF # weak fairness
RUNTIME_FLAGS += -f
endif

$(OUT).c:
	$(SPIN) $(SPINFLAGS) $(TARGET)

$(OUT): $(OUT).c
	$(CC) $(CFLAGS) -DMEMLIM=$(MLIMIT) $(COMPILERTIME_FLAGS) -o $@ $<

$(OUT)_safety: COMPILERTIME_FLAGS += -DBFS -DSAFETY -DNOCLAIM
$(OUT)_safety: $(OUT)

$(OUT)_safety_dfs: COMPILERTIME_FLAGS += -DSAFETY -DNOCLAIM
$(OUT)_safety_dfs: $(OUT)

$(OUT)_np_dfs: SPINFLAGS += -DNONP
$(OUT)_np_dfs: COMPILERTIME_FLAGS += -DNP -DNOCLAIM -DNFAIR=3
$(OUT)_np_dfs: $(OUT)

$(OUT)_ltl_dfs: $(OUT)

safety_bfs: MLIMIT = 1024
safety_bfs: clean $(OUT)_safety
	./$(OUT)

safety_dfs_full: clean $(OUT)_safety_dfs
	./$(OUT) $(RUNTIME_FLAGS)

nprogress_dfs_full: clean $(OUT)_np_dfs
	./$(OUT) $(RUNTIME_FLAGS) -l

acceptance_ltl_full: clean $(OUT)_ltl_dfs
	./$(OUT) $(RUNTIME_FLAGS) -a

ltl_starvation_free: RUNTIME_FLAGS += -N starvation_free
ltl_starvation_free: acceptance_ltl_full

ltl_deadlock_free: RUNTIME_FLAGS += -N deadlock_free
ltl_deadlock_free: acceptance_ltl_full

error_trail:
	$(SPIN) -t -p -v $(TARGET)

.PHONY: cleanall clean
clean:
	rm -rf $(OUT)*

cleanall: clean
	rm -rf $(TARGET).trail
	rm -rf _spin_nvr.tmp
