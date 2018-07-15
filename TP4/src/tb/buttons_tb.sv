`timescale 1ns/1ns

module buttons_tb;

    // --------------------------------------------------------------
    // Ports to DUT
    // --------------------------------------------------------------

    // inputs to DUT
    logic           clk;
    logic           reset;
    logic           buttonAlpha;
    logic           buttonBeta;
    logic           buttonGamma;
    logic           reverse;
    logic           update;

    // outputs from DUT
    logic [31:0]    alpha;
    logic [31:0]    beta;
    logic [31:0]    gamma;

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

    buttons dut
    (
        .i_clk              (clk),
        .i_reset            (reset),
        .i_buttonAlpha      (buttonAlpha),
        .i_buttonBeta       (buttonBeta),
        .i_buttonGamma      (buttonGamma),
        .i_reverse          (reverse),
        .i_update           (update),
        .o_alpha            (alpha),
        .o_beta             (beta),
        .o_gamma            (gamma)
    );

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin
        buttonAlpha <= 0;
        buttonBeta <= 0;
        buttonGamma <= 0;
        reverse <= 0;
        update <= 0;

        // reset the DUT for a bit
        reset <= 1;
        repeat (5) @(posedge clk);
        // bring it out of reset
        @(posedge clk);
        reset <= 0;

        // wait a bit
        repeat (5) @(posedge clk);

        // make sure nothing changes if the buttons aren't pressed
        update <= 1;
        repeat (5) @(posedge clk);
        reverse <= 1;
        repeat (5) @(posedge clk);
        reverse <= 0;

        // check alpha counting up
        @(posedge clk);
        assert (alpha === 32'd0);
        buttonAlpha <= 1;
        repeat (4) @(posedge clk);
        assert (alpha === 32'd4915200);

        // reverse the direction (doesn't take affect for
        // a few cycles because of the syncroniser)
        reverse <= 1;
        @(posedge clk);
        assert (alpha === 32'd9830400);
        @(posedge clk);
        assert (alpha === 32'd14745600);
        @(posedge clk);
        assert (alpha === 32'd19660800);
        @(posedge clk);
        // now the reverse takes affect and we start counting down
        assert (alpha === 32'd14745600);
        @(posedge clk);
        assert (alpha === 32'd9830400);
        @(posedge clk);
        assert (alpha === 32'd4915200);

        // reverse again
        reverse <= 0;
        @(posedge clk);
        assert (alpha === 32'd0);

        // should wrap
        @(posedge clk);
        assert (alpha === 32'd3014983680);
        @(posedge clk);
        assert (alpha === 32'd3010068480);
        @(posedge clk);
        // now the reverse takes affect again
        assert (alpha === 32'd3014983680);

        // should wrap
        @(posedge clk);
        assert (alpha === 32'd0);
        buttonAlpha <= 0;


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
        reset |-> ((alpha === 0) &&
                   (beta  === 0) &&
                   (gamma === 0)));

    // check that alpha doesn't change unless buttonAlpha
    // is asserted, and that update was asserted
    alphaChange:
    assert property (
        @(posedge clk)
        disable iff (reset)
        !$stable(alpha) |->
            ($past(buttonAlpha, 3) &&
             $past(update, 1)));

    // check that beta doesn't change unless buttonBeta
    // is asserted, and that update was asserted
    betaChange:
    assert property (
        @(posedge clk)
        disable iff (reset)
        !$stable(beta) |->
            ($past(buttonBeta, 3) &&
             $past(update, 1)));

    // check that gamma doesn't change unless buttonGamma
    // is asserted, and that update was asserted
    gammaChange:
    assert property (
        @(posedge clk)
        disable iff (reset)
        !$stable(gamma) |->
            ($past(buttonGamma, 3) &&
             $past(update, 1)));

endmodule
