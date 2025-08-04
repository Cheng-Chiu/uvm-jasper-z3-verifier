`define W 64
module RCA1(
		input a, b, cin,
		output s, cout
	);

    assign s = a ^ b ^ cin;
    assign cout = (a & b) | ((a ^ b) & cin);

endmodule

module ripple_carry_adder_8
	(
		input [7:0] a,
		input [7:0] b,          
		input cin,
		output [7:0] s,
		output cout
	);
	
	logic [8:0] c;
	assign c[0] = cin;
    assign cout = c[8];
    
	genvar i;
    generate
		for (i = 0; i < 8; i = i + 1) begin : rca
			RCA1 FA (.a(a[i]), .b(b[i]), .cin(c[i]), .s(s[i]), .cout(c[i+1]));
		end
	endgenerate
	
endmodule


module carry_select_adder
    (
        input logic          clock,
        input logic          reset,
		input logic [`W-1:0] a,
		input logic [`W-1:0] b,
		input logic carry_in,
		output logic [`W-1:0] s,
		output logic carry_out
	);
    logic [`W-1:0] s_next;
    logic [7:0] s0 [7:0], s1 [7:0], s_sel [7:0];
    logic       cout0[7:0], cout1[7:0], carry [8:0];

    assign carry[0] = carry_in;

    genvar i;
    generate
        for (i = 0; i < 8; i++) begin : block
            ripple_carry_adder_8 rca0 (
                .a   (a[i*8 +: 8]),
                .b   (b[i*8 +: 8]),
                .cin (1'b0),
                .s (s0[i]),
                .cout(cout0[i])
            );

            ripple_carry_adder_8 rca1 (
                .a   (a[i*8 +: 8]),
                .b   (b[i*8 +: 8]),
                .cin (1'b1),
                .s (s1[i]),
                .cout(cout1[i])
            );
            
            assign s_sel[i]   = (carry[i] == 1'b0) ? s0[i]   : s1[i];
            assign carry[i+1] = (carry[i] == 1'b0) ? cout0[i] : cout1[i];
        end
    endgenerate

    assign s_next = {
        s_sel[7], s_sel[6], s_sel[5], s_sel[4],
        s_sel[3], s_sel[2], s_sel[1], s_sel[0]
    };

    always_ff @(posedge clock) begin
        if (reset) begin
            s <= '0;
            carry_out <= '0;
        end else begin
            s <= s_next;
            carry_out <= carry[8];
        end
    end
endmodule

