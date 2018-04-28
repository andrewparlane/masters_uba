program adv7123_props #(parameter H_ACTIVE,
                        parameter H_FRONT_PORCH,
                        parameter H_SYNC,
                        parameter H_BACK_PORCH,
                        parameter V_ACTIVE,
                        parameter V_FRONT_PORCH,
                        parameter V_SYNC,
                        parameter V_BACK_PORCH)
                     (input logic eClk,
                      input logic eRst,
                      input logic [9:0] eR,
                      input logic [9:0] eG,
                      input logic [9:0] eB,
                      input logic [$clog2(H_ACTIVE)-1:0] pixel_x,
                      input logic [$clog2(V_ACTIVE)-1:0] pixel_y,
                      input logic sClk,
                      input logic [9:0] sR,
                      input logic [9:0] sG,
                      input logic [9:0] sB,
                      input logic sBlank,
                      input logic sSync,
                      input logic sHSync,
                      input logic sVSync);

    parameter H_TOTAL = H_ACTIVE +
              H_FRONT_PORCH +
              H_SYNC +
              H_BACK_PORCH;

    er_eq_sr: assert property (@(posedge eClk) (eR === sR));
    eg_eq_sg: assert property (@(posedge eClk) (eG === sG));
    eb_eq_sb: assert property (@(posedge eClk) (eB === sB));

    // check that once sHSync asserts (active low) then it should
    // stay low for H_SYNC ticks and then rise again
    hsync_low_cycles: assert property
        (@(posedge eClk)
        disable iff (eRst)
        $fell(sHSync) |=>
            $stable(sHSync) [*H_SYNC-1] ##1 $rose(sHSync));

    // repeat for sVSync
    vsync_low_cycles: assert property
        (@(posedge eClk)
        disable iff (eRst)
        $fell(sVSync) |=>
            $stable(sVSync) [*(V_SYNC*H_TOTAL)-1] ##1 $rose(sVSync));

    integer f;
    initial begin
        // Generar un archivo para uso con
        // https://ericeastwood.com/lab/vga-simulator/
        $timeformat(-9, 0, " ns", 0);
        f = $fopen("adv7123_out.txt", "w");
        forever begin
            @(posedge eClk);

            // Escribir la línea
            $fwrite(f, "%t: %b %b %b %b %b\n",
                    $time, sHSync, sVSync,
                    sR, sG, sB);
        end
    end

    final begin
        // cerrar el archivo a final de la simulación
        $fclose(f);
    end

endprogram

module adv7123_sva_wrapper;
    bind adv7123
         adv7123_props #(.H_ACTIVE(H_ACTIVE),
                         .H_FRONT_PORCH(H_FRONT_PORCH),
                         .H_SYNC(H_SYNC),
                         .H_BACK_PORCH(H_BACK_PORCH),
                         .V_ACTIVE(V_ACTIVE),
                         .V_FRONT_PORCH(V_FRONT_PORCH),
                         .V_SYNC(V_SYNC),
                         .V_BACK_PORCH(V_BACK_PORCH))
         adv7123_sva_bind (.*);
endmodule
