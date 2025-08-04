package fifo_pkg;
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // transaction
    class fifo_item #(type T = logic [31:0]) extends uvm_sequence_item;
        rand T data;
        `uvm_object_param_utils(fifo_item#(T))

        function new(string name="fifo_item");
            super.new(name);
        endfunction
    endclass

    class fifo_sequencer #(type T = logic [31:0]) extends uvm_sequencer #(fifo_item#(T));
        `uvm_component_param_utils(fifo_sequencer#(T))
        function new(string name, uvm_component parent);
            super.new(name, parent);
        endfunction
    endclass

    class fifo_seq #(type T = logic [31:0]) extends uvm_sequence #(fifo_item#(T));
        `uvm_object_param_utils(fifo_seq#(T))
        int unsigned n_items = 1000;

        function new(string name="fifo_seq");
            super.new(name);
        endfunction

        virtual task body();
            fifo_item#(T) req;
            for (int i = 0; i < n_items; i++) begin
                req = fifo_item#(T)::type_id::create($sformatf("req_%0d", i));
                assert(req.randomize());
                start_item(req);
                finish_item(req);
            end
        endtask
    endclass

    class fifo_driver #(type T = logic [31:0]) extends uvm_driver #(fifo_item#(T));
        `uvm_component_param_utils(fifo_driver#(T))
        virtual fifo_if#(T).DRV vif;

        function new(string name, uvm_component parent);
            super.new(name, parent);
        endfunction

        virtual task run_phase(uvm_phase phase);
            if (vif == null) `uvm_fatal(get_type_name(), "vif not set in driver")
            fork
                drive_out_ready(); // for output
                drive_producer(); // for input
            join
            phase.wait_for_state(UVM_PHASE_ENDED);
            disable fork;
        endtask

        task drive_out_ready();
            vif.drv_cb.out_ready <= 1'b0;
            forever begin
                @(vif.drv_cb);
                if (vif.reset) begin
                    vif.drv_cb.out_ready <= 1'b0;
                end else begin
                    // 50% of chance out_ready is high
                    vif.drv_cb.out_ready <= ($urandom_range(0,99) < 50);
                end
            end
            // or can set to be always high to get output whenever ready
            // vif.drv_cb.out_ready <= 1'b1;
            // forever @(vif.drv_cb);
        endtask

        task drive_producer();
            fifo_item#(T) req;

            // defaults
            vif.drv_cb.in_valid  <= 1'b0;
            vif.drv_cb.packet_in <= '0;

            do @(vif.drv_cb); while (vif.reset);

            forever begin
                seq_item_port.get_next_item(req);

                vif.drv_cb.in_valid  <= 1'b1;
                vif.drv_cb.packet_in <= req.data;

                do @(vif.drv_cb); while (!vif.drv_cb.in_ready);

                vif.drv_cb.in_valid <= 1'b0;

                seq_item_port.item_done();
            end
        endtask 
    endclass

    class fifo_monitor #(type T = logic [31:0]) extends uvm_component;
        `uvm_component_param_utils(fifo_monitor#(T))

        virtual fifo_if#(T).MON vif;

        uvm_analysis_port#(T) ap_enq;
        uvm_analysis_port#(T) ap_deq;

        function new(string name, uvm_component parent);
        super.new(name, parent);
            ap_enq = new("ap_enq", this);
            ap_deq = new("ap_deq", this);
        endfunction

        virtual task run_phase(uvm_phase phase);
            bit deq_now, deq_d1;
            T pkt_now;

            if (vif == null) `uvm_fatal(get_type_name(), "vif not set in monitor");

            // Wait for reset is deasserted
            @(vif.mon_cb);
            while (vif.mon_cb.reset) @(vif.mon_cb);

            deq_d1 = 0;

            forever begin
                @(vif.mon_cb);

                // just like rtl logic
                pkt_now = vif.mon_cb.packet_out;
                deq_now = (vif.mon_cb.out_valid && vif.mon_cb.out_ready);

                // Registered-output FIFO: publish DEQ for previous handshake
                if (deq_d1) ap_deq.write(pkt_now);

                // Publish enqueue exactly once per handshake
                if (vif.mon_cb.in_valid && vif.mon_cb.in_ready)
                    ap_enq.write(vif.mon_cb.packet_in);

                deq_d1 = deq_now;
            end
        endtask
    endclass

    // overload write() function name
    `uvm_analysis_imp_decl(_enq)
    `uvm_analysis_imp_decl(_deq)

    class fifo_scoreboard #(type T = logic [31:0]) extends uvm_component;
        `uvm_component_param_utils(fifo_scoreboard#(T))
        // queue to represent the fifo
        T exp_q[$];

        int unsigned allow_trailing_deqs = 1;

        uvm_analysis_imp_enq#(T, fifo_scoreboard#(T)) enq_imp;
        uvm_analysis_imp_deq#(T, fifo_scoreboard#(T)) deq_imp;

        function new(string name, uvm_component parent);
            super.new(name, parent);
            enq_imp = new("enq_imp", this);
            deq_imp = new("deq_imp", this);
        endfunction

        function void write_enq(T t);
            exp_q.push_back(t);
            `uvm_info("SCB", $sformatf("ENQ   : %p  (depth=%0d)", t, exp_q.size()), UVM_MEDIUM)
        endfunction

        function void write_deq(T got);
            T exp;
            if (exp_q.size() == 0) begin
            if ( allow_trailing_deqs > 0) begin
                allow_trailing_deqs--;
                return;
            end
                `uvm_error("SCB", $sformatf("Underflow: got=%p but expected queue is empty", got))
                return;
            end
            exp = exp_q.pop_front();
            if (got !== exp)
                `uvm_error("SCB", $sformatf("Mismatch: EXP=%p GOT=%p", exp, got))
            else
                `uvm_info("SCB", $sformatf("DEQ OK: %p  (remaining=%0d)", got, exp_q.size()), UVM_LOW)
        endfunction
    endclass

    class fifo_agent #(type T = logic [31:0]) extends uvm_agent;
        `uvm_component_param_utils(fifo_agent#(T))

        fifo_sequencer#(T)  seqr;
        fifo_driver#(T)     drv;
        fifo_monitor#(T)    mon;

        virtual fifo_if#(T).DRV vif_drv;
        virtual fifo_if#(T).MON vif_mon;

        function new(string name, uvm_component parent);
        super.new(name, parent);
        endfunction

        virtual function void build_phase(uvm_phase phase);
            super.build_phase(phase);

            // Get modport VIFs from config DB
            if (!uvm_config_db#(virtual fifo_if#(T).DRV)::get(this, "", "vif_drv", vif_drv))
                `uvm_fatal(get_type_name(), "vif_drv not set")
            if (!uvm_config_db#(virtual fifo_if#(T).MON)::get(this, "", "vif_mon", vif_mon))
                `uvm_fatal(get_type_name(), "vif_mon not set")

            seqr = fifo_sequencer#(T)::type_id::create("seqr", this);
            drv  = fifo_driver#(T)::type_id::create("drv" , this);
            mon  = fifo_monitor#(T)::type_id::create("mon" , this);

            drv.vif = vif_drv;
            mon.vif = vif_mon;
        endfunction

        virtual function void connect_phase(uvm_phase phase);
            super.connect_phase(phase);
            drv.seq_item_port.connect(seqr.seq_item_export);
        endfunction
    endclass

    class fifo_env #(type T = logic [31:0]) extends uvm_env;
        `uvm_component_param_utils(fifo_env#(T))

        fifo_agent#(T)      agt;
        fifo_scoreboard#(T) scb;

        function new(string name, uvm_component parent);
            super.new(name, parent);
        endfunction

        virtual function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            agt = fifo_agent#(T)::type_id::create("agt", this);
            scb = fifo_scoreboard#(T)::type_id::create("scb", this);
        endfunction

        virtual function void connect_phase(uvm_phase phase);
            super.connect_phase(phase);
            agt.mon.ap_enq.connect(scb.enq_imp);
            agt.mon.ap_deq.connect(scb.deq_imp);
        endfunction
    endclass

    class fifo_test #(type T = logic [31:0]) extends uvm_test;
        `uvm_component_param_utils(fifo_test#(T))

        fifo_env#(T)  env;
        fifo_seq#(T)  seq;

        function new(string name, uvm_component parent);
            super.new(name, parent);
        endfunction

        virtual function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            env = fifo_env#(T)::type_id::create("env", this);
        endfunction

        virtual task run_phase(uvm_phase phase);
            phase.raise_objection(this);

            seq = fifo_seq#(T)::type_id::create("seq");
            seq.start(env.agt.seqr);
            @(posedge env.agt.vif_mon.clock);

            wait (env.scb.exp_q.size() == 0);
            repeat (2) @(posedge env.agt.vif_drv.clock);

            phase.drop_objection(this);
        endtask
    endclass

    // same test name without parameter for easier usage in bash script
    class fifo_test_default extends fifo_test#(logic [31:0]);
        `uvm_component_utils(fifo_test_default)
        function new(string name="fifo_test_default", uvm_component parent=null);
            super.new(name, parent);
        endfunction
    endclass

endpackage
