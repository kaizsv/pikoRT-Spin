SPIN = spin
CC = gcc
CFLAGS = -w -O2
SPINFLAGS = -a
COMPILERTIME_FLAGS = -DXUSAFE -DCOLLAPSE -DNOFAIR

TARGET = pikoRT.pml
OUT = pan
MAXMLIMIT = 53248 # maxima memory usage 52G
MLIMIT ?= $(MAXMLIMIT)
MAXDEPTH = 100000000
RUNTIME_FLAGS = -m$(MAXDEPTH)
SKIP_TRAIL_STEPS =
MAX_TRAIL_STEPS =

ifdef MA
COMPILERTIME_FLAGS += -DMA=$(MA)
endif

ifdef CLAIM
RUNTIME_FLAGS += -N $(CLAIM)
endif

ifdef J
SKIP_TRAIL_STEPS = -j$(J)
endif

ifdef U
MAX_TRAIL_STEPS = -u$(U)
endif

$(OUT).c:
	$(SPIN) $(SPINFLAGS) $(TARGET)

$(OUT): $(OUT).c
	$(CC) $(CFLAGS) -DMEMLIM=$(MLIMIT) $(COMPILERTIME_FLAGS) -o $@ $<

$(OUT)_safety: COMPILERTIME_FLAGS += -DBFS -DSAFETY -DNOCLAIM
$(OUT)_safety: $(OUT)

$(OUT)_safety_dfs: COMPILERTIME_FLAGS += -DSAFETY -DNOCLAIM
$(OUT)_safety_dfs: $(OUT)

$(OUT)_ltl_dfs: SPINFLAGS += -DLTL
$(OUT)_ltl_dfs: $(OUT)

safety_bfs: clean $(OUT)_safety
	./$(OUT)

safety_dfs_full: clean $(OUT)_safety_dfs
	./$(OUT) $(RUNTIME_FLAGS)

acceptance_ltl_full: clean $(OUT)_ltl_dfs
	./$(OUT) $(RUNTIME_FLAGS) -a

ltl_deadlock_free: RUNTIME_FLAGS += -N deadlock_free
ltl_deadlock_free: acceptance_ltl_full

error_trail:
	$(SPIN) -t -p -v $(SKIP_TRAIL_STEPS) $(MAX_TRAIL_STEPS) $(TARGET)

error_trail_full:
	$(SPIN) -p -s -r -X -v -n123 -l -g $(SKIP_TRAIL_STEPS) -k $(TARGET).trail $(MAX_TRAIL_STEPS) $(TARGET)

.PHONY: cleanall clean
clean:
	rm -rf $(OUT)*

cleanall: clean
	rm -rf $(TARGET).trail
	rm -rf _spin_nvr.tmp
