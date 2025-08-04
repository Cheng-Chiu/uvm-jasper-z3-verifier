`define W 64
module adder_verifier
(
  input                 clock,
  input                 reset,
  input  [`W-1:0]       a, b,
  input                 carry_in,
  output [`W-1:0]       s,
  output                carry_out
);

    default clocking @(posedge clock); endclocking
    default disable iff (reset); // disable assertions when reset is high

    carry_select_adder dut(.*);

    logic [`W:0] gold;
    always_ff @(posedge clock) begin
        if (reset) gold <= '0;
        else       gold <= {1'b0, a} + {1'b0, b} + {64'b0, carry_in};
    end

    ast_correct: assert property ( {carry_out, s} == gold );
    cov_large: cover property (
        a >= 64'h0000_0000_F000_0000 && b >= 64'h0000_0000_F000_0000
    );
endmodule
