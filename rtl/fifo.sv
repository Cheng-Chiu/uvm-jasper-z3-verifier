module fifo #(
	parameter int  DEPTH    = 8,
	parameter type PACKET_T = logic [31:0]
) (
	input  logic    clock,
	input  logic    reset,

	// Enqueue side
	input  logic    in_valid,
	output logic    in_ready,
	input  PACKET_T packet_in,

	// Dequeue side
	output logic    out_valid,
	input  logic    out_ready,
	output PACKET_T packet_out
);

    localparam int AW = $clog2(DEPTH);

    PACKET_T         mem [DEPTH];
    logic [AW-1:0]   rd_ptr, wr_ptr;
    logic [AW:0]     occ;

    // Current-cycle Handshakes
    logic enq, deq;
    assign out_valid = (occ != 0);
    assign in_ready  = (occ != DEPTH) || (out_valid && out_ready);
    assign enq       = in_valid  && in_ready;
    assign deq       = out_valid && out_ready;

    assign packet_out = mem[rd_ptr];

    // Next-state
    logic [AW-1:0] rd_ptr_n, wr_ptr_n;
    logic [AW:0]   occ_n;

    always_comb begin
        rd_ptr_n = rd_ptr;
        wr_ptr_n = wr_ptr;
        occ_n    = occ;

        if (enq) begin
            wr_ptr_n = (wr_ptr == DEPTH-1) ? '0 : wr_ptr + 1;
            occ_n    = occ + 1;
        end
        if (deq) begin
            rd_ptr_n = (rd_ptr == DEPTH-1) ? '0 : rd_ptr + 1;
            occ_n    = occ_n - 1;
        end
    end

  	always_ff @(posedge clock) begin
        if (reset) begin
            rd_ptr <= '0;
            wr_ptr <= '0;
            occ    <= '0;
			for (int i = 0; i < DEPTH; i++) begin
				mem[i] <= '0;
			end
        end else begin
            rd_ptr <= rd_ptr_n;
            wr_ptr <= wr_ptr_n;
            occ    <= occ_n;
            if (enq) mem[wr_ptr] <= packet_in;
        end
 	end
endmodule