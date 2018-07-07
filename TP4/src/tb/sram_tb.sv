`timescale 1ns/1ns

module sram_tb;

    logic               clk;
    logic               reset;
    logic [17:0]        addr;
    logic [15:0]        wdata;
    logic               rnw;
    logic               start;
    logic [15:0]        rdata;
    logic               busy;
    wire logic [15:0]   bus_data;
    logic [17:0]        bus_addr;
    logic               bus_nCE;
    logic               bus_nOE;
    logic               bus_nWE;
    logic               bus_nLB;
    logic               bus_nUB;

    logic [15:0]        bus_data_w;
    logic [15:0]        bus_data_r;
    logic               bus_data_wen;

    // --------------------------------------------------------------
    // Generate the clock
    // --------------------------------------------------------------
    localparam CLOCK_FREQUENCY_MHZ = 100;
    localparam CLOCK_PERIOD_NS = 1000 / CLOCK_FREQUENCY_MHZ;

    initial begin
        clk <= 1'b0;
        forever begin
            #(CLOCK_PERIOD_NS/2);
            clk <= ~clk;
        end
    end

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------
    sram dut   (.i_clk       (clk),
                .i_reset     (reset),
                // input
                .i_addr      (addr),
                .i_wdata     (wdata),
                .i_rnw       (rnw),
                .i_start     (start),
                // output
                .o_rdata     (rdata),
                // status
                .o_busy      (busy),
                // bus ports
                .io_data     (bus_data),
                .o_addr      (bus_addr),
                .o_nCE       (bus_nCE),
                .o_nOE       (bus_nOE),
                .o_nWE       (bus_nWE),
                .o_nLB       (bus_nLB),
                .o_nUB       (bus_nUB));

    // --------------------------------------------------------------
    // data bus
    // --------------------------------------------------------------
    assign bus_data_r = bus_data;
    assign bus_data = bus_data_wen ? bus_data_w : 'z;

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin
        // reset the dut
        reset <= 1;
        start <= 0;
        addr <= 18'h0;
        rnw <= 1;
        bus_data_wen <= 0;
        #(CLOCK_PERIOD_NS*10);
        reset <= 0;
        #(CLOCK_PERIOD_NS*10);

        bus_data_wen <= 1;
        for (int b = 0; b < 16; b++) begin
            bus_data_w <= 16'b1 << b;
            #CLOCK_PERIOD_NS;
        end
        bus_data_wen <= 0;

        // pulse start for one tick
        start <= 1;
        #CLOCK_PERIOD_NS;
        start <= 0;
        #CLOCK_PERIOD_NS;

        // pulse start for 5 ticks
        start <= 1;
        #(CLOCK_PERIOD_NS * 5);
        start <= 0;
        #CLOCK_PERIOD_NS;

        // do a write
        wdata <= 16'h1234;
        rnw <= 0;
        start <= 1;
        #CLOCK_PERIOD_NS;
        start <= 0;
        #(CLOCK_PERIOD_NS*5);

        // write 2 words in a row
        addr <= 18'h1;
        wdata <= 16'hABCD;
        start <= 1;
        #CLOCK_PERIOD_NS;
        #CLOCK_PERIOD_NS;
        addr <= 18'h2;
        wdata <= 16'h9876;
        #CLOCK_PERIOD_NS;
        start <= 0;
        #(CLOCK_PERIOD_NS*5);

        // read 2 words then write a word
        addr <= 18'h31234;
        rnw <= 1;
        start <= 1;
        #CLOCK_PERIOD_NS;
        addr <= 18'h31235;
        #CLOCK_PERIOD_NS;
        addr <= 18'h31236;
        rnw <= 0;
        #CLOCK_PERIOD_NS;
        start <= 0;
        #(CLOCK_PERIOD_NS*10);

        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------
    // check that CE, WE, OE are deasserted (1) while in reset
    // and that the data bus is high impedance
    inRst:
    assert property
        (@(posedge clk)
        reset |-> (bus_nCE &&
                   bus_nOE &&
                   bus_nWE &&
                   bus_data === 'Z));

    // check that if we are idle (not start and not busy)
    // then CE, WE, OE are deasserted (1)
    idle:
    assert property
        (@(posedge clk)
        disable iff (reset)
        (!start && !busy) |=> (bus_nCE &&
                               bus_nOE &&
                               bus_nWE));

    // check that if we are not busy and !bus_data_write_en,
    // then bus_data is high impedance
    idleBusData:
    assert property
        (@(posedge clk)
        disable iff (reset)
        (!bus_data_wen && !busy) |->
        (bus_data === 'z));


    // chack that data put into the data bus comes out
    // of the rdata signal 2 ticks later
    rdData3Cycles:
    assert property
        (@(posedge clk)
        disable iff (reset)
        ##2 // so we don't try to get values before time 0
        (rdata === $past(bus_data,2)));

    // check the address on the bus is the address in
    // when start and !busy
    addrMatches:
    assert property
        (@(posedge clk)
        disable iff (reset)
        (start && !busy) |=> (bus_addr === $past(addr, 1)));

    // check that WE and OE are never asserted together
    notWenAndOen:
    assert property
        (@(posedge clk)
        disable iff (reset)
        (bus_nWE || bus_nOE));

    // check that if start and read the enable lines are correct
    // and the bus data is high impedance
    startRead:
    assert property
        (@(posedge clk)
        disable iff (reset)
        (start && rnw) |=> ((!bus_nCE &&
                             !bus_nOE &&
                             bus_nWE &&
                             !bus_nLB &&
                             !bus_nUB &&
                             bus_data === 'Z)));

    // check the writing works as desired
    startWrite:
    assert property
        (@(posedge clk)
        disable iff (reset)
        (start && !rnw && !busy) |=>
        (!bus_nCE && bus_nOE && !bus_nWE && !bus_nLB &&
         !bus_nUB && busy    && bus_data === wdata)
        ##1 // one tick later everything gets released
        (bus_nCE && bus_nOE && bus_nWE && bus_nLB &&
         bus_nUB && !busy    && bus_data === 'Z));


endmodule
