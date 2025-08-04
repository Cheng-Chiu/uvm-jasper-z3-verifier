#!/usr/bin/env bash
set -e
vcs -full64 -sverilog \
	-override_timescale=1ns/100ps \
	+incdir+../rtl \
	+incdir+./tb/fifo \
	-ntb_opts uvm \
	./tb/fifo/fifo_pkg.sv \
	../rtl/fifo.sv \
	./tb/fifo/fifo_if.sv \
	./tb/fifo/tb_fifo_top.sv \
	-l compile.log

./simv \
	+UVM_TESTNAME=fifo_test_default \
	+UVM_VERBOSITY=UVM_LOW \
| tee sim.log
