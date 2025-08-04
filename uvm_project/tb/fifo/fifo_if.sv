interface fifo_if #(parameter type PACKET_T = logic [31:0]) (input logic clock);

	logic reset;

	logic    in_valid;
	logic    in_ready;
	PACKET_T packet_in;

	logic    out_valid;
	logic    out_ready;
	PACKET_T packet_out;

	//  #1step after the edge to avoid races
	clocking drv_cb @(posedge clock);
		default input #0 output #1step;
		output in_valid, packet_in, out_ready;
		input  in_ready, out_valid, packet_out;
	endclocking

	clocking mon_cb @(posedge clock);
		default input #1step output #0;
		input reset;
		input in_valid, packet_in, out_ready;
		input out_valid, packet_out, in_ready;
	endclocking

	// specify port direction
	modport DRV (clocking drv_cb, input clock, input reset);
	modport MON (clocking mon_cb, input clock);

endinterface
