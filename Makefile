SPIN = spin
CC = gcc
CFLAGS = -w -O2
SPINFLAGS = -DXUSAFE -DCOLLAPSE

TARGET = pikoRT.pml
OUT = pan
MAXMLIMIT = 53248 # maxima memory usage 52G
MLIMIT ?= $(MAXMLIMIT)
MAXDEPTH = 100000000
RUNTIME_FLAGS = -m$(MAXDEPTH)

ifdef MA
SPINFLAGS += -DMA=$(MA)
endif

ifdef WF # weak fairness
RUNTIME_FLAGS += -f
endif

$(OUT).c:
	$(SPIN) -a $(TARGET)

$(OUT): $(OUT).c
	$(CC) $(CFLAGS) -DMEMLIM=$(MLIMIT) $(SPINFLAGS) -o $@ $<

$(OUT)_safety: SPINFLAGS += -DBFS -DSAFETY -DNOCLAIM
$(OUT)_safety: $(OUT)

$(OUT)_safety_dfs: SPINFLAGS += -DSAFETY -DNOCLAIM
$(OUT)_safety_dfs: $(OUT)

$(OUT)_np_dfs: SPINFLAGS += -DNP -DNOCLAIM -DFAIR=3
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

error_trail:
	$(SPIN) -t -p -v $(TARGET)

.PHONY: cleanall clean
clean:
	rm -rf $(OUT)*

cleanall: clean
	rm -rf $(TARGET).trail
	rm -rf _spin_nvr.tmp
