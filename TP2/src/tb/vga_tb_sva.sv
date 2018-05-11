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
                    input logic inActive,
                    input logic nHSync,
                    input logic nVSync);

    parameter H_TOTAL = H_ACTIVE +
              H_FRONT_PORCH +
              H_SYNC +
              H_BACK_PORCH;

    // check that once nHSync asserts (active low) then it should
    // stay low for H_SYNC ticks and then rise again
    hsync_low_cycles: assert property
        (@(posedge clk)
        disable iff (rst)
        $fell(nHSync) |=>
            $stable(nHSync) [*H_SYNC-1] ##1 $rose(nHSync));

    // repeat for sVSync
    vsync_low_cycles: assert property
        (@(posedge clk)
        disable iff (rst)
        $fell(nVSync) |=>
            $stable(nVSync) [*(V_SYNC*H_TOTAL)-1] ##1 $rose(nVSync));
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
