// ============================================================================
//  lib/aspfirst/cells_sim.sv -- the primitive cells an ASP-first design instantiates in
//  `--mode cells`, with the SAME interfaces as examples/rtl2asp/primitives_demo/stubs/cells.sv and
//  BEHAVIOURAL bodies so a simulator (Icarus) can run the printed design. sv2asp never reads
//  these bodies: it recognises each cell by NAME and supplies the semantics from its registry
//  (src/sv2asp/primitives.py), which is what makes the round trip a real check of the two
//  readings against each other.
// ============================================================================

// --- flip-flops (en = enable; WIDTH = data width) --------------------------
module FF   #(parameter WIDTH=1) (input clk, input en, input [WIDTH-1:0] d, output [WIDTH-1:0] q);
  logic [WIDTH-1:0] q_r;
  always_ff @(posedge clk) if (en) q_r <= d;
  assign q = q_r;
endmodule

module ARFF #(parameter WIDTH=1, parameter RESET_VALUE=0)            // async active-low reset
  (input clk, input en, input rstL, input [WIDTH-1:0] d, output [WIDTH-1:0] q);
  logic [WIDTH-1:0] q_r;
  always_ff @(posedge clk or negedge rstL)
    if (!rstL) q_r <= RESET_VALUE;
    else if (en) q_r <= d;
  assign q = q_r;
endmodule

// --- latch (level-sensitive; the only sanctioned latch form) ---------------
module LATA (input clk, input en, input d, output q);
  logic q_r;
  always_latch if (en) q_r = d;
  assign q = q_r;
endmodule
