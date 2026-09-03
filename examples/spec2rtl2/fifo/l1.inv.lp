% spec2rtl2/fifo/l1.inv.lp -- l1's LINKAGE: the spec's three windows mounted onto THIS design's
% registers (tenet 2b: the spec declares, the level mounts). Derived views -- head at T, no
% state -- one line per window. A different implementation of the same spec would write a
% different file here and nothing else changes.
pointer_push(P, T) :- val(write_pointer, P, T).
pointer_pop(P, T)  :- val(read_pointer, P, T).
cell_value(A, V, T) :- val(cell(storage, A), V, T).

% The SAME three windows under the names fifo.spec declares (2026-08-31). The specification
% language's vocabulary is the declared name -- the compiler never renames and the linkage is
% where the two vocabularies meet. Both spellings are derived views of the same flops, so they
% cannot disagree: this is not the boundary-spelling hazard, because there is no free value.
pointerPush(P, T) :- val(write_pointer, P, T).
pointerPop(P, T)  :- val(read_pointer, P, T).
cellValue(A, V, T) :- val(cell(storage, A), V, T).
