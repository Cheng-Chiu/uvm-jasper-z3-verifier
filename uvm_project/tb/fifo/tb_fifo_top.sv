`timescale 1ns/100ps
import uvm_pkg::*;
import fifo_pkg::*;

module top;

	logic clock = 0;
	always #5ns clock = ~clock;

	typedef logic [31:0] pkt_t;
	fifo_if#(pkt_t) vif (clock);

	fifo #(.DEPTH(100), .PACKET_T(pkt_t)) dut (
		.clock      (clock),
		.reset      (vif.reset),
		.in_valid   (vif.in_valid),
		.in_ready   (vif.in_ready),
		.packet_in  (vif.packet_in),
		.out_valid  (vif.out_valid),
		.out_ready  (vif.out_ready),
		.packet_out (vif.packet_out)
	);

	initial begin
		vif.reset = 1'b1;
		repeat (3) @(posedge clock);
		vif.reset = 1'b0;
	end

  // Hook modports to UVM
  initial begin
    uvm_config_db#(virtual fifo_if#(pkt_t).DRV)::set(null, "uvm_test_top.env.agt", "vif_drv", vif);
    uvm_config_db#(virtual fifo_if#(pkt_t).MON)::set(null, "uvm_test_top.env.agt", "vif_mon", vif);
    run_test("fifo_test_default");
  end

endmodule
