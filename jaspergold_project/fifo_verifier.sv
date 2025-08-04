
module fifo_verifier();
    parameter DEPTH = 16;
    typedef logic [7:0] pkt_t;
    logic    clock;
    logic    reset;

    // Enqueue side
    logic    in_valid;
    logic    in_ready;
    pkt_t    packet_in;

    // Dequeue side
    logic    out_valid;
    logic    out_ready;
    pkt_t    packet_out;
    
    fifo #(.DEPTH(16), .PACKET_T(pkt_t)) dut (.*);

    int wr_idx, rd_idx;
    assign packet_in = wr_idx;

    // make the input data be in the sequence of natural numbers for convenience
    // using sv queue to track will significantly enlarge the search space
    always_ff @(posedge clock) begin
        if (reset) begin
            wr_idx <= 0;
            rd_idx <= 0;
        end else begin
            // one increment when actaully enqueuing and dequeuing
            if (in_valid && in_ready)  wr_idx <= wr_idx + 1;
            if (out_valid && out_ready) rd_idx <= rd_idx + 1;
        end
    end

    // clocking block for synchronization
    clocking cb @(posedge clock);

        // ---------- Function ----------
        // Sanity check of the enqueued packet
        property wr_data_match;
            in_valid && in_ready |-> packet_in == wr_idx;
        endproperty

        // Make sure the dequeued packet is as expected
        property rd_data_match;
            out_valid && out_ready |-> packet_out == rd_idx;
        endproperty

        // ---------- Environment liveness --------
        // Make sure when fifo is full it will dequeue eventually
        property eventually_deq;
            dut.occ == DEPTH |=> s_eventually out_ready;
        endproperty

        // Make sure when fifo is empty it will enqueue eventually
        property eventually_enq;
            dut.occ == 0 |=> s_eventually in_valid;
        endproperty

        // Whenever fifo is not ready to take input but one is presented, 
        // at later time when fifo becomes ready, in_valid will eventually be high to input
        property retry_enq;
            in_valid && !in_ready |=> s_eventually in_valid;
        endproperty

        // Whenever fifo is not ready to output but is being requested for one, 
        // at later time when fifo becomes ready, out_ready will eventually be high to output
        property retry_deq;
            out_ready && !out_valid |=> s_eventually out_ready;
        endproperty

    endclocking

    // Assume the input/enqueue/write-side follows the following patterns
    assume property (cb.wr_data_match);
    assume property (cb.eventually_enq);
    assume property (cb.eventually_deq);
    assume property (cb.retry_enq);
    assume property (cb.retry_deq);
    
    // Assert read-side equivalence, checking the expected output (GOAL)
    // assert property (cb.rd_data_match);

    // Coverpoints
    cover property (@(posedge clock) dut.occ == DEPTH); // full FIFO
    cover property (@(posedge clock) dut.occ == 0);  // empty FIFO
        // full handshake simultaneously enqueuing and dequeuing 
    cover property (@(posedge clock) in_valid && in_ready && out_valid && out_ready);
    
endmodule