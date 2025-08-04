package csa_pkg;
	import uvm_pkg::*;
	`include "uvm_macros.svh"

	// ------------------------------------------------------------
	// Transaction
	// ------------------------------------------------------------
	class add_txn extends uvm_sequence_item;
		rand bit [63:0] op1, op2;
		rand bit        carry_in;
		bit       		carry_out;
		bit 	 [63:0] s;
		`uvm_object_utils(add_txn)
		// any constraints go here
		function new(string name="add_txn");
			super.new(name);
		endfunction
	endclass

	// ------------------------------------------------------------
	// Sequence
	// ------------------------------------------------------------
	class add_seq extends uvm_sequence#(add_txn);
		`uvm_object_utils(add_seq)
		int unsigned n_ops = 1000;

		function new(string name="add_seq");
			super.new(name);
		endfunction

		virtual task body();
			repeat (n_ops) begin
				add_txn tr = add_txn::type_id::create("tr");
				start_item(tr);
				assert(tr.randomize());
				finish_item(tr);
			end
		endtask
	endclass

	// ------------------------------------------------------------
	// Driver
	// ------------------------------------------------------------
	class add_driver extends uvm_driver#(add_txn);
		`uvm_component_utils(add_driver)
		virtual csa_if vif;

		function new(string name, uvm_component parent);
			super.new(name,parent);
		endfunction

		virtual function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			if (!uvm_config_db#(virtual csa_if)::get(this,"","vif",vif))
				`uvm_fatal("NOVIF","virtual interface not set")
		endfunction

		virtual task run_phase(uvm_phase phase);
			add_txn req;
			forever begin
				seq_item_port.get_next_item(req);
				@(posedge vif.clock);			// drive on clock edge
				vif.drv_cb.a <= req.op1;
				vif.drv_cb.b <= req.op2;
				vif.drv_cb.carry_in <= req.carry_in;
				seq_item_port.item_done();	// scoreboard will check later
			end
		endtask
	endclass

	// ------------------------------------------------------------
	// Monitor
	// ------------------------------------------------------------
	class add_monitor extends uvm_monitor;
		`uvm_component_utils(add_monitor)
		virtual csa_if vif;
		uvm_analysis_port#(add_txn) mon_ap;

		function new(string n, uvm_component p);
			super.new(n,p);
			mon_ap = new("mon_ap", this);
		endfunction

		virtual function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			if (!uvm_config_db#(virtual csa_if)::get(this,"","vif",vif))
				`uvm_fatal("NOVIF","virtual interface not set")
		endfunction

		virtual task run_phase(uvm_phase phase);
			add_txn tx;
			bit [63:0] op1;
			bit [63:0] op2;
			bit        carry_in;
			forever begin
				@(posedge vif.clock);
			    if (vif.mon_cb.reset)
			    	continue; 
				op1      = vif.mon_cb.a;
				op2      = vif.mon_cb.b;
				carry_in = vif.mon_cb.carry_in;

				@(posedge vif.clock); // since the adder result is ready at next cycle

				tx = add_txn::type_id::create("tx");
				tx.op1       = op1;
				tx.op2       = op2;
				tx.carry_in  = carry_in;
				tx.s         = vif.mon_cb.s;
				tx.carry_out = vif.mon_cb.carry_out;
				mon_ap.write(tx);
			end
		endtask
	endclass
	

	// ------------------------------------------------------------
	// Scoreboard
	// ------------------------------------------------------------
	class add_scoreboard extends uvm_component;
		`uvm_component_utils(add_scoreboard)
		// to become a subscriber
		uvm_analysis_imp#(add_txn, add_scoreboard) sb_imp;

		function new(string n, uvm_component p);
			super.new(n,p);
			sb_imp = new("sb_imp",this);
		endfunction

		virtual function void write(add_txn t);
			bit [64:0] full = t.op1 + t.op2 + t.carry_in;
 			bit [63:0] exp_sum   = full[63:0];
  			bit        exp_cout  = full[64];
			if (t.s !== exp_sum || t.carry_out !== exp_cout) begin
				`uvm_error("sCHK", $sformatf(
				"%h + %h +%0b (mod 2^64) = %h,%b but got %h,%b",
				t.op1, t.op2, t.carry_in, exp_sum, exp_cout,
				t.s,  t.carry_out
				));
			end else begin
        		`uvm_info("SUMCHK","OK",UVM_LOW);
			end
		endfunction
	endclass

	// ------------------------------------------------------------
	// Agent   (driver+sequencer+monitor)
	// ------------------------------------------------------------
	class add_agent extends uvm_agent;
		`uvm_component_utils(add_agent)
		add_driver					  drv;
		uvm_sequencer#(add_txn)		  seqr;
		add_monitor					  mon;

		function new(string n, uvm_component p);
			super.new(n,p);
		endfunction

		virtual function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			drv  = add_driver::type_id::create("drv", this);
			seqr = uvm_sequencer#(add_txn)::type_id::create("seqr", this);
			mon  = add_monitor::type_id::create("mon", this);
		endfunction

		virtual function void connect_phase(uvm_phase phase);
			drv.seq_item_port.connect(seqr.seq_item_export);
		endfunction
	endclass

	// ------------------------------------------------------------
	// Environment
	// ------------------------------------------------------------
	class add_env extends uvm_env;
		`uvm_component_utils(add_env)
		add_agent		agent;
		add_scoreboard	sb;

		function new(string n, uvm_component p);
			super.new(n,p);
		endfunction

		virtual function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			agent = add_agent::type_id::create("agent", this);
			sb = add_scoreboard::type_id::create("sb", this);
		endfunction

		virtual function void connect_phase(uvm_phase phase);
			agent.mon.mon_ap.connect(sb.sb_imp);
		endfunction
	endclass

	// ------------------------------------------------------------
	// Test, to modulize the framework
	// ------------------------------------------------------------
	class add_test extends uvm_test;
		`uvm_component_utils(add_test)
		add_env env;

		function new(string n, uvm_component p);
			super.new(n,p);
		endfunction

		virtual function void build_phase(uvm_phase phase);
			super.build_phase(phase);
			env = add_env::type_id::create("env", this);
		endfunction

		virtual task run_phase(uvm_phase phase);
			add_seq seq = add_seq::type_id::create("seq");
			phase.raise_objection(this);
			seq.start(env.agent.seqr);
			phase.drop_objection(this);
		endtask
	endclass
endpackage
