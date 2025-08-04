import uvm_pkg::*;
import csa_pkg::*;

module tb_top;
  logic clock = 0;
  always #5 clock = ~clock;

    csa_if #(64) if0 (.clock(clock));
    carry_select_adder dut (
        .clock     (if0.clock),
        .reset     (if0.reset),
        .a         (if0.a),
        .b         (if0.b),
        .carry_in  (if0.carry_in),
        .s         (if0.s),
        .carry_out (if0.carry_out)
    );

	initial begin
		if0.reset = 1;
		repeat (3) @(posedge clock);
		if0.reset = 0;
	end

	initial begin
		uvm_config_db#(virtual csa_if)::set(null,"*","vif",if0);
		run_test("add_test");
	end
endmodule
