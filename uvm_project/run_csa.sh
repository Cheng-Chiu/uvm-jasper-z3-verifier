#!/usr/bin/env bash
set -e
vcs -full64 -sverilog \
    -override_timescale=1ns/100ps \
    +incdir+../rtl \
    +incdir+./tb/csa \
    -ntb_opts uvm \
    ./tb/csa/csa_pkg.sv \
    ../rtl/carry_select_adder.sv \
    ./tb/csa/csa_if.sv \
    ./tb/csa/tb_csa_top.sv \
    -l compile.log

./simv \
    +UVM_TESTNAME=add_test \
    +UVM_VERBOSITY=UVM_LOW \
| tee sim.log
