% spec2rtl2/rv_missq/roundtrip_scenario.lp -- the PRINT-STAGE concrete run. Not a proof: the
% proof is the certificate. This is one scripted story, pinned at every input and every
% instant, so the authored ASP, the printed SystemVerilog translated back, and Icarus can be
% compared value for value.
%
% The story: reset; a DEMAND for line 0x111; a prefetch for the SAME line, which merges and
% consumes no slot; a prefetch for a second line, which allocates; memory stalled at first so
% an enquiry is seen pending, then taken; the demand's line comes back and is FORWARDED with
% its tag; the second line comes back and its prefetch entry ends quietly.
#const k = 18.
time(clk, 0..k).
val(resetN, 0, 0).
val(resetN, 1, T) :- time(clk, T), T >= 1.

% requesting(Instant, Address, Tag, IsDemand)
requesting(2, 273, 1, 1).    % line 0x111, tag 1, DEMAND
requesting(3, 273, 2, 0).    % same line, prefetch -- merges, no second slot, no second fetch
requesting(5, 546, 3, 0).    % line 0x222, prefetch -- allocates

val(requestValid, 1, T) :- requesting(T, _, _, _).
val(requestValid, 0, T) :- time(clk, T), not requesting(T, _, _, _).
val(requestAddress, A, T) :- requesting(T, A, _, _).
val(requestAddress, 0, T) :- time(clk, T), not requesting(T, _, _, _).
val(requestTag, X, T) :- requesting(T, _, X, _).
val(requestTag, 0, T) :- time(clk, T), not requesting(T, _, _, _).
val(requestIsDemand, D, T) :- requesting(T, _, _, D).
val(requestIsDemand, 0, T) :- time(clk, T), not requesting(T, _, _, _).

% memory refuses the first enquiry for two cycles, so a pending fetch is actually observed
val(memoryRequestReady, 0, T) :- time(clk, T), T <= 3.
val(memoryRequestReady, 1, T) :- time(clk, T), T >= 4.

% the fills, one line at a time
filling(9,  273, 4369).      % the demand's line
filling(13, 546, 8738).      % the prefetched line
val(fillValid, 1, T) :- filling(T, _, _).
val(fillValid, 0, T) :- time(clk, T), not filling(T, _, _).
val(fillAddress, A, T) :- filling(T, A, _).
val(fillAddress, 0, T) :- time(clk, T), not filling(T, _, _).
val(fillData, V, T) :- filling(T, _, V).
val(fillData, 0, T) :- time(clk, T), not filling(T, _, _).

val(redirectValid, 0, T) :- time(clk, T).
