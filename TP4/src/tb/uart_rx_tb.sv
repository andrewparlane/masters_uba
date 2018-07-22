`timescale 1ns/1ns

module uart_rx_tb;

    // --------------------------------------------------------------
    // Ports to DUT
    // --------------------------------------------------------------

    // Clock/reset
    logic       clk;
    logic       reset;

    // Bus ports
    logic       rx;

    // Data ports
    logic [7:0] readData;
    logic       readDataValid;
    logic       readDataError;

    // Status ports
    logic       receiving;
    logic       isBreak;

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

    localparam BAUD = 115200;
    localparam BIT_TIME_NS = 1000000000 / BAUD;

    uart_rx #
    (
        .CLOCK_PERIOD_NS    (CLOCK_PERIOD_NS),
        .BIT_TIME_NS        (BIT_TIME_NS)
    )
    dut
    (
        .i_clk              (clk),
        .i_reset            (reset),
        .i_rx               (rx),
        .o_readData         (readData),
        .o_readDataValid    (readDataValid),
        .o_readDataError    (readDataError),
        .o_receiving        (receiving),
        .o_isBreak          (isBreak)
    );

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    localparam FRAME_TIME_NS    = BIT_TIME_NS * 10; // (8 data bits, 1 start bit, 1 stop bit)
    localparam BIT_TIME_TICKS   = BIT_TIME_NS / CLOCK_PERIOD_NS;
    localparam FRAME_TIME_TICKS = FRAME_TIME_NS / CLOCK_PERIOD_NS;

    logic [7:0] expectingData;
    logic       expectingValid;
    logic       expectingError;
    logic       expectingBreak;

    initial begin
        expectingValid <= 0;
        expectingError <= 0;
        expectingBreak <= 0;

        // reset the DUT for a bit while wiggling rx
        reset <= 1;
        rx <= 1;
        repeat (5) @(posedge clk);
        rx <= 0;
        repeat (5) @(posedge clk);
        rx <= 1;
        // bring it out of reset
        @(posedge clk);
        reset <= 0;

        // wait a bit, to confirm idle state when not in reset
        repeat (5) @(posedge clk);

        // check for receiving pulse as soon it sees a falling edge
        expectingValid <= 1;
        expectingData <= 8'hFF;
        rx <= 0; repeat (BIT_TIME_TICKS) @(posedge clk);
        rx <= 1; repeat (FRAME_TIME_TICKS) @(posedge clk);
        rx <= 0; repeat (BIT_TIME_TICKS) @(posedge clk);
        rx <= 1; repeat (FRAME_TIME_TICKS) @(posedge clk);

        // send 0xAC + start and stop bits (lsb first)
        // 0 0011 0101 11
        expectingData <= 8'hAC;
        rx <= 0; repeat (BIT_TIME_TICKS) @(posedge clk);
        rx <= 0; repeat (BIT_TIME_TICKS) @(posedge clk);
        rx <= 0; repeat (BIT_TIME_TICKS) @(posedge clk);
        rx <= 1; repeat (BIT_TIME_TICKS) @(posedge clk);
        rx <= 1; repeat (BIT_TIME_TICKS) @(posedge clk);
        rx <= 0; repeat (BIT_TIME_TICKS) @(posedge clk);
        rx <= 1; repeat (BIT_TIME_TICKS) @(posedge clk);
        rx <= 0; repeat (BIT_TIME_TICKS) @(posedge clk);
        rx <= 1; repeat (BIT_TIME_TICKS) @(posedge clk);
        rx <= 1; repeat (BIT_TIME_TICKS) @(posedge clk);
        rx <= 1; repeat (BIT_TIME_TICKS) @(posedge clk);

        // lets test some error cases
        expectingValid <= 0;
        expectingError <= 1;

        // start bit 1 (put 0 for a few ticks then go back to 1)
        rx <= 0; repeat (8) @(posedge clk);
        rx <= 1; repeat (FRAME_TIME_TICKS) @(posedge clk);

        // stop bits 0 (data bits none zero, so it's not a break)
        rx <= 0; repeat (BIT_TIME_TICKS) @(posedge clk);
        rx <= 1; repeat (BIT_TIME_TICKS*8) @(posedge clk);
        rx <= 0; repeat (BIT_TIME_TICKS*2) @(posedge clk);
        rx <= 1; repeat (FRAME_TIME_TICKS) @(posedge clk);

        // break detect
        expectingError <= 0;
        expectingBreak <= 1;
        rx <= 1; repeat (FRAME_TIME_TICKS) @(posedge clk);
        rx <= 0; repeat (FRAME_TIME_TICKS*2) @(posedge clk);
        rx <= 1; repeat (FRAME_TIME_TICKS) @(posedge clk);
        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------
    // check that we are not receiving while in reset
    inRst:
    assert property
        (@(posedge clk)
        reset |-> (!receiving));

    // check that if receiving asserts, it's because rx
    // fell 8 ticks ago (2 for sync + 5 for debounce +
    // 1 for receiving to rise)
    recivingBecauseRxInFell:
    assert property (
        @(posedge clk)
        $rose(receiving) |->  $past(rx, 9) &&
                             !$past(rx, 8));

    // check that if rx falls and we aren't currently receiving
    // then receiving asserts in 8 ticks
    rxInToReceiving:
    assert property (
        @(posedge clk)
        disable iff (reset)
        (!receiving && $fell(rx)) |->
        ##8 $rose(receiving));

    // check that readDataValid is only asserted for one tick
    rdDataValidWidth:
    assert property (
        @(posedge clk)
        disable iff (reset)
        $rose(readDataValid) |=>
        $fell(readDataValid));

    // check that readDataError is only asserted for one tick
    rdDataErrorWidth:
    assert property (
        @(posedge clk)
        disable iff (reset)
        $rose(readDataError) |=>
        $fell(readDataError));

    // readDataError and readDataValid can't happen at the same time
    notErrorAndValid:
    assert property (
        @(posedge clk)
        disable iff (reset)
        !(readDataError && readDataValid));

    // isBreak can't happen at the same time as readDataError
    // or readDataValid
    notBreakAndValidOrError:
    assert property (
        @(posedge clk)
        disable iff (reset)
        !(isBreak && (readDataError || readDataValid)));

    // check that readDataValid asserts when receiving falls
    // if it's expected
    rdDataValid:
    assert property (
        @(posedge clk)
        disable iff (reset)
        ($fell(receiving) && expectingValid) |->
        $rose(readDataValid));

    // check that if readDataValid occurs, we were expecting it
    // and not an error
    rdDataValidWhenExpectingError:
    assert property (
        @(posedge clk)
        disable iff (reset)
        readDataValid |-> (expectingData && !expectingError));

    // check that if readDataError occurs, we were expecting it
    // and not valid
    rdDataErrorWhenExpectingValid:
    assert property (
        @(posedge clk)
        disable iff (reset)
        readDataError |-> (expectingError && !expectingValid));

    // check that readDataError asserts when receiving falls
    // if it's expected
    rdDataError:
    assert property (
        @(posedge clk)
        disable iff (reset)
        ($fell(receiving) && expectingError) |->
        $rose(readDataError));

    // check the received data is as expected
    rdData:
    assert property (
        @(posedge clk)
        disable iff (reset)
        ($fell(receiving) && expectingValid) |->
        (readData === expectingData));

    // check that isBreak falls when receiving falls
    breakFallsWithReceiving:
    assert property (
        @(posedge clk)
        disable iff (reset)
        ($fell(receiving) && $past(isBreak,1)) |->
        $fell(isBreak));

    // check that isBreak occurs when expected
    breakDetect:
    assert property (
        @(posedge clk)
        disable iff (reset)
        ($rose(receiving) && expectingBreak) |->
        ##(BIT_TIME_TICKS*9 + (BIT_TIME_TICKS/2) + 1)
        $rose(isBreak));

endmodule
