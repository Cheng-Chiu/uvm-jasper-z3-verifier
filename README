# uvm-jasperz3-verifier

A unified verification framework for realistic adder and FIFO designs, combining:

- **UVM** for scalable, modular testbenches  
- **Cadence JasperGold** for formal verification and coverage  
- **Z3 SMT Solver** for netlist‐level functional proofs  

All RTL sources live under `rtl/`.

---

## Table of Contents

1. [Features](#features)  
2. [Repository Layout](#repository-layout)  
3. [Getting Started](#getting-started)  
   - [Prerequisites](#prerequisites)  
4. [Usage](#usage)  
   - [UVM Testbenches](#uvm-testbenches)  
   - [JasperGold Formal](#jaspergold-formal)  
   - [Z3 Netlist Proofs](#z3-netlist-proofs)   

---

## Features

- **UVM**  
  - Cleanly separated driver / monitor / transaction / sequence / scoreboard / reference-model  
  - Agent & environment layers for both Carry-Select Adder (CSA) and FIFO buffer  
- **JasperGold Formal**  
  - Functional correctness proofs, edge‐case analysis, and coverage metrics  
- **Z3 SMT**  
  - Python‐based conversion of synthesized netlists (RCA, CSA, KSA) into SMT formulas  
  - Automated equivalence checks via the Z3 API  

---

## Repository Layout

```text
├── README
├── jaspergold_project
│   ├── adder_verifier.sv
│   ├── fifo_verifier.sv
│   ├── run_fm_adder.tcl
│   └── run_fm_fifo.tcl
├── rtl
│   ├── carry_select_adder.sv
│   └── fifo.sv
├── uvm_project
│   ├── run_csa.sh
│   ├── run_fifo.sh
│   └── tb
│       ├── csa
│       │   ├── csa_if.sv
│       │   ├── csa_pkg.sv
│       │   └── tb_csa_top.sv
│       └── fifo
│           ├── fifo_if.sv
│           ├── fifo_pkg.sv
│           └── tb_fifo_top.sv
└── z3_project
    ├── cell_sat.py
    └── synth
        ├── carry_select_adder.vg
        ├── kogge_stone_adder.vg
        └── ripple_carry_adder.vg
```
## Getting Started

### Prerequisites

- **Simulator & UVM**  
  - Any SystemVerilog simulator compliant with UVM 1.2+/IEEE 1800-2017 (e.g. VCS, Questa, Xcelium)  
  - `$UVM_HOME` or simulator‐provided UVM package on your `+incdir`

- **Cadence JasperGold**  
  - Formal verification kit installed and licensed  
  - Set `$JASPERGOLD_HOME` in your environment

- **Python 3.9+**  
  - Z3 Python bindings (`pip install z3-solver`)  
  - PyVerilog (`pip install pyverilog`)


## Usage

### UVM Testbenches
```bash
cd uvm_project
./run_csa.sh       # Carry-Select Adder
./run_fifo.sh      # FIFO buffer
```

### JasperGold
```bash
cd jaspergold_project
jaspergold -tcl run_fm_adder.tcl    # CSA
jaspergold -tcl run_fm_fifo.tcl     # FIFO
```
### Z3-SMT Solver
```bash
cd z3_project
python3 cell_sat.py     # Verify RCA, CSA, and KSA netlists under synth/
```