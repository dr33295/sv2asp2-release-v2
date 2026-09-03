% spec2rtl2/fifo/roundtrip_scenario.lp -- the PRINT-STAGE concrete run (tenet 4: the round trip
% needs a concrete history and belongs to the print stage, not the proof). One pinned sequence
% at the DEFAULT parameters (depth 4, width 8): fill to full (a refused push at T=5), a
% same-cycle push+pop, drain to empty, the wrap bit exercised; data_push = 10+T so every value
% is distinct and a swapped order is visible in the traces. The round trip solves the authored
% model and the sv2asp translation of the PRINTED RTL under this scenario and compares every
% net and memory cell at every instant, with Icarus simulating the print as the independent
% arbiter. This file checks the PRINT; no proof claim rests on it.
#const k = 10.
time(clk, 0..k).
val(reset_n, 0, 0).
val(reset_n, 1, T) :- time(clk, T), T >= 1.

pushing(1). pushing(2). pushing(3). pushing(4). pushing(5). pushing(6).
popping(5). popping(6). popping(7). popping(8). popping(9).
val(push, 1, T) :- pushing(T).
val(push, 0, T) :- time(clk, T), not pushing(T).
val(pop, 1, T)  :- popping(T).
val(pop, 0, T)  :- time(clk, T), not popping(T).
val(data_push, 10 + T, T) :- time(clk, T).
