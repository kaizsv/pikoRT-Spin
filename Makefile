SPIN = spin
CC = gcc
CFLAGS = -w -O0
SPINFLAGS = -DXUSAFE -DCOLLAPSE

TARGET = pikoRT.pml
OUT = pan
MLIMIT ?= 1024

$(OUT).c:
	$(SPIN) -a $(TARGET)

$(OUT): $(OUT).c
	$(CC) $(CFLAGS) -DMEMLIM=$(MLIMIT) $(SPINFLAGS) -o $@ $<

$(OUT)_safety: SPINFLAGS += -DBFS -DSAFETY -DNOCLAIM
$(OUT)_safety: $(OUT)

$(OUT)_ltl: SPINFLAGS += -DBFS -DSAFETY
$(OUT)_ltl: $(OUT)

safety_bfs: clean $(OUT)_safety
	./$(OUT)

safety_bfs_full: MLIMIT = 53248  # memory limit 52G
safety_bfs_full: safety_bfs

ltl_safety_bfs: clean $(OUT)_ltl
	./$(OUT)

.PHONY: cleanall clean
clean:
	rm -rf $(OUT)*

cleanall: clean
	rm -rf $(TARGET).trail
	rm -rf _spin_nvr.tmp

