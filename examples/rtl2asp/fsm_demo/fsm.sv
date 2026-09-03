module fsm (input clk, input rst, input go, input done, output busy);
  typedef enum logic [1:0] {IDLE, RUN, FINISH} state_t;
  state_t state;
  always_ff @(posedge clk)
    if (rst) state <= IDLE;
    else case (state)
      IDLE:   if (go)   state <= RUN;
      RUN:    if (done) state <= FINISH;
      FINISH:           state <= IDLE;
    endcase
  assign busy = (state != IDLE);
endmodule
