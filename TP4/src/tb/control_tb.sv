`timescale 1ns/1ns

module control_tb;

    // --------------------------------------------------------------
    // Ports to DUT
    // --------------------------------------------------------------

    // inputs to DUT
    logic           clk;
    logic           reset;
    logic [7:0]     uartData;
    logic           uartDataValid;
    logic           requestNewData;

    // outputs from DUT
    logic           transformStart;
    logic           sramStart;
    logic           sramRnW;
    logic [17:0]    sramAddr;
    logic [15:0]    sramWdata;
    logic           waitingForData;
    logic           transforming;

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

    control dut
    (
        .i_clk              (clk),
        .i_reset            (reset),
        .i_uartData         (uartData),
        .i_uartDataValid    (uartDataValid),
        .i_requestNewData   (requestNewData),
        .o_transformStart   (transformStart),
        .o_sramStart        (sramStart),
        .o_sramRnW          (sramRnW),
        .o_sramAddr         (sramAddr),
        .o_sramWdata        (sramWdata),
        .o_waitingForData   (waitingForData),
        .o_transforming     (transforming)
    );

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    logic           expectSramWrite;
    logic [17:0]    expectSramAddr;
    logic [15:0]    expectSramData;

    initial begin
        uartDataValid <= 0;
        requestNewData <= 0;
        expectSramWrite <= 0;
        expectSramData <= '0;
        expectSramAddr <= '0;

        // reset the DUT for a bit
        reset <= 1;
        repeat (5) @(posedge clk);
        // bring it out of reset
        @(posedge clk);
        reset <= 0;

        // wait a bit
        repeat (5) @(posedge clk);

        // At this point we should be waiting
        // for the number of coordinates.
        // so lets tell it there are two
        @(posedge clk);
        uartData <= 8'd2;
        uartDataValid <= 1;
        @(posedge clk);
        uartDataValid <= 0;
        @(posedge clk);
        uartData <= 8'd0;
        uartDataValid <= 1;
        @(posedge clk);
        uartDataValid <= 0;

        // Now we should be waiting for coordinate data
        // send coord 0 X,Y,Z at full speed

        // X
        @(posedge clk); // LSB
            uartData <= 8'h01;
            uartDataValid <= 1;
        @(posedge clk); // MSB
            uartData <= 8'h23;
            expectSramAddr <= 18'd0;
            expectSramData <= 16'h2301;
            expectSramWrite <= 1;

        // Y
        @(posedge clk); // LSB
            uartData <= 8'h45;
            expectSramWrite <= 0;
        @(posedge clk); // MSB
            uartData <= 8'h67;
            expectSramWrite <= 1;
            expectSramAddr <= 18'd1;
            expectSramData <= 16'h6745;

        // Z
        @(posedge clk); // LSB
            uartData <= 8'h89;
            expectSramWrite <= 0;
        @(posedge clk); // MSB
            uartData <= 8'hAB;
            expectSramWrite <= 1;
            expectSramAddr <= 18'd2;
            expectSramData <= 16'hAB89;

        // clear valid
        @(posedge clk);
            uartDataValid <= 0;
            expectSramWrite <= 0;

        // send coord 1 X,Y,Z at slow speed
        // and change the data after one tick
        // so we can check it reads the correct value

        // X
        @(posedge clk); // LSB
            uartData <= 8'hCD;
            uartDataValid <= 1;
        @(posedge clk);
            uartData <= 8'h00;
            uartDataValid <= 0;
        repeat(10) @(posedge clk);
        @(posedge clk); // MSB
            uartData <= 8'hEF;
            uartDataValid <= 1;
            expectSramWrite <= 1;
            expectSramAddr <= 18'd3;
            expectSramData <= 16'hEFCD;
        @(posedge clk);
            uartData <= 8'h00;
            uartDataValid <= 0;
            expectSramWrite <= 0;
        repeat(10) @(posedge clk);

        // Y
        @(posedge clk); // LSB
            uartData <= 8'h1F;
            uartDataValid <= 1;
            expectSramWrite <= 1;
        @(posedge clk);
            uartData <= 8'h00;
            uartDataValid <= 0;
            expectSramWrite <= 0;
        repeat(10) @(posedge clk);
        @(posedge clk); // MSB
            uartData <= 8'h2E;
            uartDataValid <= 1;
            expectSramWrite <= 1;
            expectSramAddr <= 18'd4;
            expectSramData <= 16'h2E1F;
        @(posedge clk);
            uartData <= 8'h00;
            uartDataValid <= 0;
            expectSramWrite <= 0;
        repeat(10) @(posedge clk);

        // Z
        @(posedge clk); // LSB
            uartData <= 8'h3D;
            uartDataValid <= 1;
            expectSramWrite <= 1;
        @(posedge clk);
            uartData <= 8'h00;
            uartDataValid <= 0;
            expectSramWrite <= 0;
        repeat(10) @(posedge clk);
        @(posedge clk); // LSB
            uartData <= 8'h4C;
            uartDataValid <= 1;
            expectSramWrite <= 1;
            expectSramAddr <= 18'd5;
            expectSramData <= 16'h4C3D;
        @(posedge clk);
            uartData <= 8'h00;
            uartDataValid <= 0;
            expectSramWrite <= 0;

        // check we are still in the receive data state
        stillInWaitingForData: assert (waitingForData);

        repeat(10) @(posedge clk);

        // now check we are not in the reciving data state
        leftWaitingForData: assert (!waitingForData);

        // request new data
        @(posedge clk);
        requestNewData <= 1;
        @(posedge clk);
        requestNewData <= 0;

        repeat(20) @(posedge clk);

        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------
    // check signals while in reset
    inRst:
    assert property (
        @(posedge clk)
        reset |-> (!transformStart   &&
                   !sramStart        &&
                   sramRnW           &&
                   waitingForData    &&
                   !transforming));

    // check that sramRnW is low for only one tick at a time
    rnwPulse:
    assert property (
        @(posedge clk)
        disable iff (reset)
        $fell(sramRnW) |=> $rose(sramRnW));

    // if sramRnW falls then sramStart should rise
    rnwAndStart:
    assert property (
        @(posedge clk)
        disable iff (reset)
        $fell(sramRnW) |-> $rose(sramStart));

    // check that sramRnW only falls when expectSramWrite
    rnwOnlyWhenExpected:
    assert property (
        @(posedge clk)
        disable iff (reset)
        $fell(sramRnW) |-> $past(expectSramWrite, 1));

    // check that when we write we write the correct data
    // to the correct address
    writeDataAndAddr:
    assert property (
        @(posedge clk)
        disable iff (reset)
        $fell(sramRnW) |-> ((sramAddr === $past(expectSramAddr,1)) &&
                            (sramWdata === $past(expectSramData,1))));

    // check that requestNewData had to rise for transforming
    // to be asserted
    transformingAsserted:
    assert property (
        @(posedge clk)
        disable iff (reset)
        $rose(transforming) |-> ($past(requestNewData, 1) &&
                                 !$past(requestNewData, 2)));

    // When transforming rises it should remain high for
    // the time it takes to read all 6 words of data
    // which is 6 clock ticks
    transformingHighFor6Ticks:
    assert property (
        @(posedge clk)
        disable iff (reset)
        $rose(transforming) |=>
            ($stable(transforming) [*5]
             ##1 $fell(transforming)));

    // if transforming is high, sram_start should be high
    transformingAndSramStart:
    assert property (
        @(posedge clk)
        disable iff (reset)
        transforming |-> (sramStart && sramRnW));

    // transformStart pulses high for one tick when
    // transforming rises
    transformingAndTransformStart:
    assert property (
        @(posedge clk)
        disable iff (reset)
        $rose(transforming) |->
            ($rose(transformStart)
             ##1
             $fell(transformStart)));

    // sramAddr counts from 0 to 5 starting when transforming
    // asserts
    sramAddrCountsUp:
    assert property (
        @(posedge clk)
        disable iff (reset)
        $rose(transforming) |->
            (    (sramAddr === 0)
             ##1 (sramAddr === 1)
             ##1 (sramAddr === 2)
             ##1 (sramAddr === 3)
             ##1 (sramAddr === 4)
             ##1 (sramAddr === 5)));

endmodule
