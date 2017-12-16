SPIN = spin
CC = gcc
CFLAGS = -w -O2
SPINFLAGS = -DXUSAFE -DCOLLAPSE

TARGET = pikoRT.pml
OUT = pan
MLIMIT ?= 1024
MAXMLIMIT = 53248 # maxima memory usage 52G

ifdef MA
SPINFLAGS += -DMA=$(MA)
endif

$(OUT).c:
	$(SPIN) -a $(TARGET)

$(OUT): $(OUT).c
	$(CC) $(CFLAGS) -DMEMLIM=$(MLIMIT) $(SPINFLAGS) -o $@ $<

$(OUT)_safety: SPINFLAGS += -DBFS -DSAFETY -DNOCLAIM
$(OUT)_safety: $(OUT)

$(OUT)_ltl: SPINFLAGS += -DBFS -DSAFETY
$(OUT)_ltl: $(OUT)

$(OUT)_safety_dfs: SPINFLAGS += -DSAFETY -DNOCLAIM
$(OUT)_safety_dfs: $(OUT)

safety_bfs: clean $(OUT)_safety
	./$(OUT)

safety_bfs_full: MLIMIT = $(MAXMLIMIT)
safety_bfs_full: safety_bfs

safety_dfs_full: MLIMIT = $(MAXMLIMIT)
safety_dfs_full: clean $(OUT)_safety_dfs
	./$(OUT) -m100000000

ltl_safety_bfs: clean $(OUT)_ltl
	./$(OUT)

error_trail:
	$(SPIN) -t -p -v $(TARGET)

.PHONY: cleanall clean
clean:
	rm -rf $(OUT)*

cleanall: clean
	rm -rf $(TARGET).trail
	rm -rf _spin_nvr.tmp

