program adv7123_props #(parameter DELAY_TICKS,
                        parameter H_ACTIVE,
                        parameter H_FRONT_PORCH,
                        parameter H_SYNC,
                        parameter H_BACK_PORCH,
                        parameter V_ACTIVE,
                        parameter V_FRONT_PORCH,
                        parameter V_SYNC,
                        parameter V_BACK_PORCH)
                       (input logic clk,
                        input logic rst,
                        input logic [9:0] rIn,
                        input logic [9:0] gIn,
                        input logic [9:0] bIn,
                        input logic [$clog2(H_ACTIVE)-1:0] pixelX,
                        input logic [$clog2(V_ACTIVE)-1:0] pixelY,
                        input logic clkOut,
                        input logic [9:0] rOut,
                        input logic [9:0] gOut,
                        input logic [9:0] bOut,
                        input logic nBlank,
                        input logic nSync,
                        input logic nHSync,
                        input logic nVSync);

    // Assume that the vga_tb_sva.sv assertions have passed
    // so we don't care about the relations between hs, vs
    // pixelX and pixelY.
    // I'm going to ignore clkOut here, as it's just a simple
    // connection.

    default disable iff (rst);

    // First check that Sync is 0 whenever HSync or VSync is 0
    sync: assert property
        (@(posedge clk)
         (nSync === 0) ===
            ((nHSync === 0) || (nVSync === 0)));

    // whenever we are in blanking the output RGB should be 0s
    blankingRGB: assert property
        (@(posedge clk)
         (nBlank === 0) |->
            ((rOut === 0) &&
             (gOut === 0) &&
             (bOut === 0)));

    // whenever we are not in blanking the output RGB should be
    // the previous input RGB
    notBlankingRGB: assert property
        (@(posedge clk)
         (nBlank === 1) |->
            ((rOut === rIn) &&
             (gOut === gIn) &&
             (bOut === bIn)));


    integer f;
    initial begin
        // Generar un archivo para uso con
        // https://ericeastwood.com/lab/vga-simulator/
        $timeformat(-9, 0, " ns", 0);
        f = $fopen("adv7123_out.txt", "w");
        forever begin
            @(posedge clk);

            // Escribir la línea
            $fwrite(f, "%t: %b %b %b %b %b\n",
                    $time, nHSync, nVSync,
                    rOut, gOut, bOut);
        end
    end

    final begin
        // cerrar el archivo a final de la simulación
        $fclose(f);
    end

endprogram

module adv7123_sva_wrapper;
    bind adv7123
         adv7123_props #(.DELAY_TICKS(DELAY_TICKS),
                         .H_ACTIVE(H_ACTIVE),
                         .H_FRONT_PORCH(H_FRONT_PORCH),
                         .H_SYNC(H_SYNC),
                         .H_BACK_PORCH(H_BACK_PORCH),
                         .V_ACTIVE(V_ACTIVE),
                         .V_FRONT_PORCH(V_FRONT_PORCH),
                         .V_SYNC(V_SYNC),
                         .V_BACK_PORCH(V_BACK_PORCH))
         adv7123_sva_bind (.*);
endmodule
