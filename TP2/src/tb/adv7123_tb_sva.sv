program adv7123_props #(parameter H_ACTIVE,
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


    parameter H_TOTAL = H_ACTIVE +
              H_FRONT_PORCH +
              H_SYNC +
              H_BACK_PORCH;

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
