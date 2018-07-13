program vga_props #(parameter H_ACTIVE,
                    parameter H_FRONT_PORCH,
                    parameter H_SYNC,
                    parameter H_BACK_PORCH,
                    parameter V_ACTIVE,
                    parameter V_FRONT_PORCH,
                    parameter V_SYNC,
                    parameter V_BACK_PORCH)
                   (input logic clk,
                    input logic rst,
                    input logic [$clog2(H_ACTIVE)-1:0] pixelX,
                    input logic [$clog2(V_ACTIVE)-1:0] pixelY,
                    input logic endOfFrame,
                    input logic inActive,
                    input logic nHSync,
                    input logic nVSync);

    parameter H_TOTAL = H_ACTIVE +
                        H_FRONT_PORCH +
                        H_SYNC +
                        H_BACK_PORCH;

    parameter H_NOT_ACTIVE = H_TOTAL - H_ACTIVE;

    parameter V_TOTAL = V_ACTIVE +
                        V_FRONT_PORCH +
                        V_SYNC +
                        V_BACK_PORCH;

    parameter V_NOT_ACTIVE = V_TOTAL - V_ACTIVE;

    default disable iff (rst);

    // --------------------------------------------------------------
    // First check horizontal timings
    // Show that the FP, sync, BP and active times are as desired
    // --------------------------------------------------------------

    // check that pixelX counts from 1 to H_ACTIVE - 1
    pixelXCounts: assert property
        (@(posedge clk)
        ((pixelX != (H_ACTIVE-1)) &&
         (pixelX != 0)) |=>
            (pixelX === $past(pixelX)+1'b1));

    // check that pixelX wraps from H_ACTIVE - 1 to 0
    // then stays there for at least FP + SYNC + BP ticks
    // It actually can stay at 0 for longer during vertical
    // blanking. So we can't check that it changes after that
    pixelXWrap: assert property
        (@(posedge clk)
        (pixelX === (H_ACTIVE-1)) |=>
            (pixelX === 0)
            ##1 $stable(pixelX) [*H_NOT_ACTIVE]);

    // Check that nHSync falls FP pixel
    // after pixelX = H_ACTIVE-1
    pixelXToHS: assert property
        (@(posedge clk)
        (pixelX === (H_ACTIVE-1)) |=>
            ##(H_FRONT_PORCH) $fell(nHSync));

    // check that endOfFrame only asserts for one tick
    endOfFramePulseWidth: assert property
        (@(posedge clk)
        ($rose(endOfFrame) |=>
            $fell(endOfFrame)));

    // Check that nHSync falls FP pixel
    // after endOfFrame
    endOfFrameToHSync: assert property
        (@(posedge clk)
        ($rose(endOfFrame) |=>
            ##(H_FRONT_PORCH) $fell(nHSync)));

    // check that once nHSync asserts (active low) then it should
    // stay low for H_SYNC ticks and then rise again
    hsyncLow: assert property
        (@(posedge clk)
        $fell(nHSync) |=>
            $stable(nHSync) [*H_SYNC-1] ##1 $rose(nHSync));

    // now we've shown that pixelX goes from 1 to H_ACTIVE-1
    // to 0 and FP ticks later nHSync falls, SYNC ticks later
    // it rises again. This shows that the active, fp and sync
    // timings are correct. Now check that nHSync falls every
    // H_TOTAL ticks. That shows that H_TOTAL is correct, implying
    // that BP is correct
    hsyncPerLine: assert property
        (@(posedge clk)
        $fell(nHSync) |=>
            ##(H_TOTAL-1) $fell(nHSync));

    // --------------------------------------------------------------
    // Repeat for vertical timings
    // Show that the FP, sync, BP and active times are as desired
    // --------------------------------------------------------------

    // check that pixelY only ever changes when pixelX goes from
    // H_ACTIVE-1 to 0
    pixelYonPixelXWrap: assert property
        (@(posedge clk)
        $changed(pixelY) |->
        ($changed(pixelX) && (pixelX === 0)));

    // check that pixelY counts from 1 to V_ACTIVE - 1
    // every H_TOTAL ticks
    pixelYCounts: assert property
        (@(posedge clk)
        ($changed(pixelY) &&
         (pixelY !== 0) &&
         (pixelY !== (V_ACTIVE - 1))) |=>
            $stable(pixelY) [*H_TOTAL-1]
            ##1 (pixelY === $past(pixelY)+1));

    // check that pixelY wraps from V_ACTIVE - 1 to 0
    // then stays there for (V_NOT_ACTIVE+1) * H_TOTAL ticks
    // (V_NOT_ACTIVE+1) because the first line of active has
    // pixelY = 0
    pixelYWraps: assert property
        (@(posedge clk)
        ($changed(pixelY) &&
         (pixelY === (V_ACTIVE - 1))) |=>
            $stable(pixelY) [*H_TOTAL-1]
            ##1 (pixelY === 0) [*(H_TOTAL*(V_NOT_ACTIVE+1))]
            ##1 (pixelY === 1));

    // Check that nVSync falls FP lines
    // after pixelY changes to 0
    pixelYToVS: assert property
        (@(posedge clk)
        ($changed(pixelY) &&
         (pixelY === 0)) |->
            ##(H_TOTAL*V_FRONT_PORCH) $fell(nVSync));


    // check that once nVSync asserts (active low) then it should
    // stay low for V_SYNC * H_TOTAL ticks and then rise again
    vsyncLowCycles: assert property
        (@(posedge clk)
        $fell(nVSync) |=>
            $stable(nVSync) [*(V_SYNC*H_TOTAL)-1]
            ##1 $rose(nVSync));

    // now we've shown that pixelY goes from 1 to V_ACTIVE-1
    // to 0 and FP ticks later nVSync falls, SYNC ticks later
    // it rises again. This shows that the active, fp and sync
    // timings are correct. Now check that nVSync falls every
    // V_TOTAL * H_TOTAL ticks.
    // That shows that V_TOTAL is correct, implying
    // that BP is correct
    vsyncPerFrame: assert property
        (@(posedge clk)
        $fell(nVSync) |=>
            ##((V_TOTAL*H_TOTAL)-1) $fell(nVSync));

    // --------------------------------------------------------------
    // Finally check the inActive net
    // --------------------------------------------------------------

    // pixelX only counts when we are in the active region
    // so pixelX changes if and only if inActive.
    active: assert property
        (@(posedge clk)
        ($changed(pixelX) === $past(inActive)));

endprogram

module vga_sva_wrapper;
    bind vga
         vga_props #(.H_ACTIVE(H_ACTIVE),
                     .H_FRONT_PORCH(H_FRONT_PORCH),
                     .H_SYNC(H_SYNC),
                     .H_BACK_PORCH(H_BACK_PORCH),
                     .V_ACTIVE(V_ACTIVE),
                     .V_FRONT_PORCH(V_FRONT_PORCH),
                     .V_SYNC(V_SYNC),
                     .V_BACK_PORCH(V_BACK_PORCH))
         vga_sva_bind (.*);
endmodule
