interface csa_if #(parameter int W = 64) (input logic clock);
    logic reset;
    logic [W-1:0] a, b;
    logic [W-1:0] s;
    logic carry_in, carry_out;

    // driver side
    clocking drv_cb @(posedge clock);
        output a,b;
        output carry_in;
        output reset;
        input  s;
        input carry_out;
    endclocking


    // monitor side
    clocking mon_cb @(posedge clock);
        input reset;
		input a, b;
		input carry_in;
		input s;
		input carry_out;
    endclocking
endinterface
