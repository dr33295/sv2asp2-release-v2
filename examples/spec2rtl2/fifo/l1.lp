% spec2rtl2/fifo/l1.lp -- the design: a circular-buffer FIFO, PARAMETERIZED (the user's
% correction: the size is a parameter, not a build-time constant). `depth` and `width` are
% overridable params; the address and pointer widths derive from them. The loader resolves
% params to numbers for lint/refine (defaults below: depth 4, width 8 -- the instantiation the
% certificate runs at); the printer prints `#(parameter DEPTH = 4, WIDTH = 8)` with the derived
% widths as localparams. The level's `depth` param is resolved away by the loader before any
% solve, so it cannot collide with the spec's depth constant; the two must be set consistently
% when overriding (one number, two knobs -- a stated coupling, not automation).
% Full-word names (tenet 8); wrap-bit pointers; flags as pure pointer relations (no count);
% show-ahead output. The reasoning behind every decision: DESIGN.md.
module(fifo).
param(depth, 4).                            % overridable
param(width, 8).                            % overridable
param(address_width, log2(depth)).          % derived -> localparam
param(pointer_width, add(address_width, 1)).% derived: address + the wrap bit
port(clk, input, 1).       port(reset_n, input, 1).
port(push, input, 1).      port(data_push, input, width).   port(full, output, 1).
port(pop, input, 1).       port(data_pop, output, width).
port(valid_pop, output, 1). port(empty, output, 1).

net(vcc, 1). def(vcc, k(1, 1)).

% -- the two wrap-bit pointers: advance by one exactly on their event, else hold --
net(write_pointer, pointer_width). net(read_pointer, pointer_width).
net(push_accepted, 1). net(pop_served, 1).
def(push_accepted, logand(reset_n, logand(push, lnot(full)))).
def(pop_served,    logand(reset_n, logand(pop, lnot(empty)))).
inst(u_write_pointer, arff).
  pin(u_write_pointer, clk, clk). pin(u_write_pointer, rstL, reset_n).
  pin(u_write_pointer, en, push_accepted).
  pin(u_write_pointer, d, wp_plus_one). pin(u_write_pointer, q, write_pointer).
  iparam(u_write_pointer, width, pointer_width). iparam(u_write_pointer, reset_value, 0).
inst(u_read_pointer, arff).
  pin(u_read_pointer, clk, clk). pin(u_read_pointer, rstL, reset_n).
  pin(u_read_pointer, en, pop_served).
  pin(u_read_pointer, d, rp_plus_one). pin(u_read_pointer, q, read_pointer).
  iparam(u_read_pointer, width, pointer_width). iparam(u_read_pointer, reset_value, 0).
net(wp_plus_one, pointer_width). def(wp_plus_one, add(write_pointer, k(1, pointer_width), pointer_width)).
net(rp_plus_one, pointer_width). def(rp_plus_one, add(read_pointer, k(1, pointer_width), pointer_width)).

% -- the flags: pure pointer relations (no count exists anywhere in this design) --
def(empty, eq(read_pointer, write_pointer)).
net(write_pointer_opposed, pointer_width).
def(write_pointer_opposed, add(write_pointer, k(depth, pointer_width), pointer_width)).
def(full, eq(read_pointer, write_pointer_opposed)).
def(valid_pop, lnot(empty)).

% -- the storage: depth x width, one write port, read combinationally (show-ahead) --
net(write_address, address_width). def(write_address, slc(write_pointer, 0, address_width)).
net(read_address, address_width).  def(read_address, slc(read_pointer, 0, address_width)).
inst(storage, farray).
  pin(storage, clk, clk). pin(storage, we, push_accepted).
  pin(storage, wa, write_address). pin(storage, wd, data_push).
  iparam(storage, depth, depth). iparam(storage, width, width).
def(data_pop, mrd(storage, read_address)).
