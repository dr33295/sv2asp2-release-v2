# SystemVerilog feature coverage (sv2asp)

The goal: **translate every synthesizable SystemVerilog feature** to ASP. The verification layer
(assertions / properties / sequences / coverage) is deliberately **out of scope** — it is the
property layer, handled separately (and hand-authored today).

**This file's job is status, not translation walkthroughs.** For a worked "here is the SV, here
is the real emitted ASP" example of a construct, see `docs/reference/SV_TRANSLATION_CATALOG.md` (organized the
same way, by construct) or follow this file's own `examples/` links below — every one points at a
real, committed, regenerated-and-checked design (`scripts/regen_examples.py --check`).

Soundness invariant: anything **not** ✅/🟡 below is **flagged loud** (a coverage PROBLEM, exit 1
under `--strict-coverage`) — never silently dropped or mistranslated. See
`feedback-no-silent-miss`. This file is the worklist for closing the ❌/⚠️ rows.

**What a ✅ is backed by, and what it is not.** A row is ✅ when the construct translates on the
committed corpus and its tests. Two simulator differentials add independent evidence: the
IEEE differential (`proofs/gen_ieee_diff.py`, Icarus, combinational core at one instant) and
the idiom sweep (`test_idiom_sweep_matches_icarus`, Icarus, realistic sequential designs
matched cycle by cycle in both modes). A ✅ row that no sweep idiom exercises is a claim about
the corpus, not about RTL in the wild — that is how ten defects on ✅ rows were found in one
evening (2026-08-16). Where a row cites a sweep id or a `gen_ieee_diff` probe, the value was
checked against a simulator, not only translated.

Second soundness net: coverage "OK" only means every line was *translated* — it can't see an
unsafe free variable in the emitted ASP. `test_all_examples_ground_cleanly` grounds every example's
design with clingo and fails on any grounding error (the "coverage OK but won't ground" class).

**Legend** ✅ covered · 🟡 partial (common cases; limits noted) · ⚠️ deferred (recognized,
flagged, has a known reason) · ❌ gap (not yet; flagged) · 🔲 **out of scope** (the verification layer, or
non-synthesisable constructs — rejected loud, never encoded; not a gap we intend to close).

> **Status: the synthesisable design layer (Groups 1–6) is COMPLETE.** Every in-scope construct is ✅ or a
> deliberate, *sound* refusal (3-D+ arrays, non-uniform instance arrays, overlapping slice-writes flag rather
> than mistranslate). Modular (the default compile) and flat are proven observably equivalent. Remaining
> ❌/⚠️ rows are either out-of-scope or narrow refusals — not silent misses. Forward capability work
> (foundedness-liveness B2; the xmask sim-parity option B6.2) lives in `notes/WORKLIST.md` —
> tightness (T2) and wide-∀-via-Lean are DONE and proven.

---


**Cross-cutting note, tracked outside the tables**:

- **Unknown power-on state** — first-class, ON by default: every unreset 4-state STATE ELEMENT
  gets an exact-X domain choice in the generated `__xinit.lp` companion (2-state defaults to 0
  per LRM 6.8; enums pool over members; a family too large to enumerate gets guidance). Since
  F4 (2026-08-16) that covers registers, array cells, lanes, latches and `$rose`/`$fell` edges
  alike — the design layer carries no initial state at all, so where an element lives does not
  decide what power-on it gets. An element with no power-on policy is a loud problem, checked
  against the state vector the emitted rules carry. `--init-zero` writes a concrete all-zeros
  start as a separate opt-in file. Decision policy proven (`Xinit.choice_iff`,
  `Xinit.mem_is_opened`, `Xinit.lane_is_opened`); usage `docs/guide/SV2ASP_USAGE.md` §3; design record
  `notes/design/X_SEMANTICS.md`.

## 1. Data types & declarations
| Feature | Status | Notes / next |
|---|---|---|
| scalar `logic`/`wire`/`reg` | ✅ | a 1-bit signal is a width-1 WORD: `val(s, V, T)` with `V∈{0,1}`; the BIT label only drives the v1/v2 boolean encoding (two positive rules vs excluded-middle) |
| `'x` / `'z` value literal | ⚠️ | **REFUSED loudly** (Fix 87): a value literal with unknown bits is a coverage problem (`--strict-coverage` exits non-zero), never a silent 0 — `int()` of an unknown SVInt returns 0, which is exactly what the pre-fix code shipped. PROVEN: `Xinit.unknown_is_refused`, `refusal_never_a_value` (never becomes ANY value), `known_is_masked`+`known_is_wf` (the known path is the masked value, in-width); `XinitTable.lit_*` checks the model against the real `_lit_intake` on observed refusals + exhaustively. `casex`/`casez` labels are pattern wildcards, unaffected. Unknown power-on state is separate: x-init (S1.4) |
| packed vector `[N-1:0]` | ✅ | WORD: `val(s, V, T)`, `V` the N-bit value; all arithmetic via width-generic `@func` (`@add(_,_,N)`), wrap at `2^N` |
| unpacked array `[0:N-1]` (memory) | ✅ | ADDRESSED shape, §2.9; works in **modular** too — per-instance `addr(Inst,mem,A)` + init/write/hold (`test_modular_memory_matches_flat`) |
| 2-D unpacked array `[0:N][0:M]` | ✅ | two-address memory `val(q(A1, A2), V, T)` over `addr(q, A1, A2)`; `for(i)for(j) q[i][j]<=src[i][j]` lane-rolls to one rule, dynamic `q[a][b]` read/write, partial/guarded hold per dim (`test_2d_unpacked_array`, [`array2d_demo`](../../examples/rtl2asp/array2d_demo)); 3-D+ flags |
| packed 2-D `[N-1:0][W-1:0]` | ✅ | INDEXED (lane) via element select / generate |
| `enum` + `typedef` | ✅ | TAG shape, §3.6 ([`fsm_demo`](../../examples/rtl2asp/fsm_demo)). An enum register's ASYNC reset resets to the member's TAG (`val(state, idle, T) :- val(rst_n, 0, T)`), never its number — the number matched no transition arm, so an FSM without a `default` arm was dark forever after reset (`test_idiom_sweep_matches_icarus[enum_fsm_no_default]`). **An enum READ AS A NUMBER goes through `enum_value/3`** (the `EnumVal` IR node, `ir/enumval.py`): `state < B` (by value, not by tag name), `state == 3'd2`, `state == n`, `case (state) 3'd1:` (the member with that number), `if (state)` / `state \|\| x` (non-zero), `state + 1`, `state[0]`, `mem[state]`, `{state[1:0], x}`, `3'(state)` — in comb items, register D-inputs and memory addresses alike; a tag compare (`state == IDLE`, two enum signals) and a tag copy keep the TAG; the FSM-output decode `state == B0 \|\| state == B1` is a boolean tree of tag compares. A ternary of TAGS in a PROCEDURAL assignment (`next = st_t'(d ? S1 : S)`) keeps the tags (its hoisted temp is enum-typed). All Icarus-arbitrated in both modes: `test_idiom_sweep_matches_icarus[enum_read_as_number]`, `[enum_ternary_in_procedural_case]` |
| `parameter` / `localparam` | ✅ | concrete-resolved + folded (incl. DERIVED `localparam W2=K*2`, as a WIDTH, and WIDE values ≥2³¹ → canonical String in `param/2`); `param/2` schema. localparams excluded from the modular spec key (internal constants, not instance params) (`test_localparam_wide_derived_and_width`) |
| **uppercase / `_`-leading identifiers** | ✅ | SV allows `N_reg`, `MyBus`, `_t`; clingo reads those as VARIABLES, so each identifier component is normalized to a valid constant (`N_reg`→`n_reg`, `u_M(Field)`→`u_M(field)`) in flat AND modular — a post-pass on the final IR (`test_uppercase_identifiers_normalized`) |
| `struct` packed | ✅ | per-field subsignals `p(field)`; field access + whole concat/slice ([`struct_demo`](../../examples/rtl2asp/struct_demo)). Used as a WHOLE WORD — assigned to/from a vector, in arithmetic, compared, sliced as a packed vector — the word is (re)assembled from the fields with `@shl`/`@bor` and a word written into the struct is decomposed by `@slc` at each field's offset, so both views agree ([`struct_whole_copy_demo`](../../examples/rtl2asp/struct_whole_copy_demo)) |
| `struct` as a module port (field-access only) | ✅ | bridges PER FIELD `u(p(f)) <-> actual(f)` ([`struct_port_demo`](../../examples/rtl2asp/struct_port_demo)). Works correctly when the port is only ever accessed via field names. If the port is passed whole to another module or registered as a word, see the struct-packed limitation above. |
| `struct` unpacked | ✅ | per-field subsignals `p(field)`; whole-value copy fans out per-field (`reg1<=din` -> per-field next-state + hold, [`struct_whole_copy_demo`](../../examples/rtl2asp/struct_whole_copy_demo)); field access + concat/slice |
| nested struct `p.a.b` | ✅ | one-level subsignal `p(a)`; nested read slices it ([`nested_struct_demo`](../../examples/rtl2asp/nested_struct_demo)); nested field writes that TILE `p(a)` are reassembled ([`partial_write_demo`](../../examples/rtl2asp/partial_write_demo)); partial-coverage flags |
| struct arrays (unpacked) | ✅ | register file of records: word-cell memory, `arr[i].field` = slice of the cell ([`struct_array_demo`](../../examples/rtl2asp/struct_array_demo)); whole-element write + field reads; clocked field write `arr[i].f <= v` = cell read-modify-write ([`clocked_partial_demo`](../../examples/rtl2asp/clocked_partial_demo)) |
| clocked partial (slice) write | ✅ | `q[hi:lo] <= v`, `q.a.x <= v`, `arr[i].f <= v` → read-modify-write, untouched bits RETAIN prior value ([`clocked_partial_demo`](../../examples/rtl2asp/clocked_partial_demo)). One per-region RMW branch: a whole-write base overridden by slices (`q<=x; q[3:0]<=y`), and per-slice CONDITIONS (`if(c) q[3:0]<=a`) self-hold (`guard ? val : base[region]`) (`test_slice_write_edge_cases`). Overlapping/out-of-range slices flagged (ambiguous multi-driver). Slices of one register written from SEVERAL always blocks (`q[3:0] <= a` in one, `q[7:4] <= b` in another) compose into ONE read-modify-write at module level (`test_idiom_sweep_matches_icarus[two_always_disjoint_slices]`); overlapping slices, or two blocks with different clock/reset, refuse |
| `union` packed | ✅ | ONE WORD signal; members are slice/views — `u.all`→word, `u.f.hi`→`@slc` ([`union_demo`](../../examples/rtl2asp/union_demo)); field-by-field writes that TILE the word are reassembled ([`partial_write_demo`](../../examples/rtl2asp/partial_write_demo)); a partial-coverage write flags |
| `typedef` (non-enum scalar/vector) | ✅ | package vector/scalar alias as a PORT type, in ARITHMETIC (`@add` at the alias width), and ACROSS a hierarchy boundary + modular ([`typedef_arith_demo`](../../examples/rtl2asp/typedef_arith_demo), `test_typedef_arith_hierarchy` / `_modular_matches_flat`); element_type for arrays ([`typedef_mem_demo`](../../examples/rtl2asp/typedef_mem_demo)); `decl_type` preserves the alias name |
| **signed** types | ✅ | two's-complement bit pattern (same storage); signedness read per-OP from pyslang. Signed compare wraps `@signed`; widening `@sext`; `>>>` `@ashr`; signed `/`,`%` `@sidiv`/`@simod` ([`signed_demo`](../../examples/rtl2asp/signed_demo), [`signed_satcount_demo`](../../examples/rtl2asp/signed_satcount_demo)) |
| `real`/`string`/`time`/`event` | 🔲 | non-synthesisable — out of scope; rejected loud (never encoded), not a gap to close |

## 2. Operators
| Feature | Status | Notes / next |
|---|---|---|
| `+` `-` `*` | ✅ | `@add`/`@sub`/`@mul` (width-generic, wrap) |
| **wide arithmetic** (≥ 32-bit, e.g. 64-bit) | ✅ | a value ≥ 2³¹ exceeds clingo's 32-bit int → stored as a canonical decimal STRING; Python computes the exact result (magnitude-canonical, so `==`/`!=`/`\|x`/`&x` stay native, ordering routes through `@wcmp`). Concrete BMC only ([`wide_mul_demo`](../../examples/rtl2asp/wide_mul_demo)); all-input ∀-proofs route through completion → Lean 4 (`BitVec`/`bv_decide`), not `&bv` (the `&bv` propagator is deferred to its one niche: wide symbolic data mixed with ASP foundedness — WORKLIST §B1) |
| `/` `%` | ✅ | unsigned `@idiv`/`@imod`; SIGNED `@sidiv`/`@simod` (trunc toward zero, modulo takes dividend's sign); divide by zero → 0 ([`divmod_demo`](../../examples/rtl2asp/divmod_demo), [`signed_demo`](../../examples/rtl2asp/signed_demo)) |
| `**` power | ✅ | `@pow` (usually constant-folds first) |
| `&` `\|` `^` `~` `~^` bitwise | ✅ | `@band`/`@bor`/`@bxor`; `~` per truth-table (bit) or `@bnot` (word); binary XNOR `~^`/`^~` → `~(a^b)`; unary `-` → `@neg`; per-lane `~a[i]`/`-a[i]` in a generate (`test_per_lane_unary`, `test_binary_xnor`) |
| `&&` `\|\|` `!` logical | ✅ | logand/logor/lnot; operands may be bits, comparisons, or word `!=0` — boolean emitter treats each as an atomic leaf (on-set/off-set) |
| `==` `!=` `<` `>` `<=` `>=` | ✅ | word compare; tag compare for an enum against a member or another enum signal; an enum against a NUMBER or an ordering compare goes by the member's value (`enum_value/3`) |
| `===` `!==` case-equality | ✅ | 2-state model: `===`≡`==`, `!==`≡`!=` (no X/Z in the modeled state), same compare path ([`case_eq_demo`](../../examples/rtl2asp/case_eq_demo)) |
| `<<` `>>` shift | ✅ | `@shl`/`@shr` ([`shift_demo`](../../examples/rtl2asp/shift_demo)) |
| `<<<` `>>>` arithmetic shift | ✅ | `<<<` == `@shl`; signed `>>>` → `@ashr` (sign fill); unsigned `>>>` → logical `@shr` ([`signed_demo`](../../examples/rtl2asp/signed_demo)) |
| reduction `\|` `&` over lanes | ✅ | `ror`/`rand`, excluded-middle 0-side ([`reduce_demo`](../../examples/rtl2asp/reduce_demo)) |
| per-lane AND (CAM match), N-dim | ✅ | `match[i..] = valid[i..] && (entry[i..]==key)` over 1..N lane indices `val(match,I,J,..,T)` ([`cam_demo`](../../examples/rtl2asp/cam_demo), [`cam2d_demo`](../../examples/rtl2asp/cam2d_demo)) |
| reduction over N-dim lanes | ✅ | `\|arr`/`&arr` over a 2-D+ array reduces over ALL lane dims ([`cam2d_demo`](../../examples/rtl2asp/cam2d_demo) `\|match`) |
| N-dim lane copy / word-op / proc-`for` | ✅ | `y[i][j]=a[i][j]&b[i][j]` etc. — nested generate AND nested procedural `for` in always_comb (same `_idx` mechanism) |
| reduction over a WORD/expr | ✅ | `\|x`=`x!=0`, `&x`=`x==all-ones`, `^x`=`@parity`; composes over any operand |
| reduction `~\|` `~&` `~^` | ✅ | negated forms (flip polarity) |
| `$countones` / `$onehot` / `$onehot0` | ✅ | popcount: `$countones`=`@popcnt` (word); `$onehot`=`(@popcnt==1)`, `$onehot0`=`(@popcnt<=1)` (1-bit, compare path) (`test_countones_onehot`) |
| `$rose` / `$fell` | ✅ | sampled-value EDGE functions (Fix 92): a two-time-point test, so its own `EdgeItem` -- not a comb rule (same instant) nor a register (own state). All four (sample@T, sample@T+1) combinations emitted POSITIVELY (hard rule 3), disjoint and exhaustive so exactly one fires. UNBOUND at T=0 (no previous sample -- SV reads `x`), announced as a WARNING. Argument of a plain signal, inside a clocked block (`test_sampled_value_edges_rose_fell`) |
| `{a,b}` concatenation | ✅ | runtime: each field `@shl` to its offset, `@bor`'d ([`bitfield_demo`](../../examples/rtl2asp/bitfield_demo)) |
| `{N{x}}` replication | ✅ | N is always constant (SV); x may be runtime → N-copy concat ([`replication_demo`](../../examples/rtl2asp/replication_demo)). With bitvec ON (default), `{{N{expr}}}` in a Concat coalesces to a single range rule `val(sig(I), ..., T) :- I = lo..hi` (Fix 35). Both simple (`{N{bit}}`) and compound (`{N{a&b}}`) expressions collapse correctly. |
| `?:` conditional (ternary) | ✅ | comparison/1-bit selector native; general selector hoisted to a gcond bit — 1-bit boolean as `gcond=expr`, multi-bit as `gcond=(expr!=0)` ([`ternary_demo`](../../examples/rtl2asp/ternary_demo), [`ternary_sel_demo`](../../examples/rtl2asp/ternary_sel_demo)) |
| `[hi:lo]` part-select | ✅ | `@slc(v, lo, w)` = `(v>>lo)` masked to `w` bits |
| `[i]` bit/element select | ✅ | const + dynamic; LANE/VFF signal → lane read ([`lane_select_demo`](../../examples/rtl2asp/lane_select_demo)); packed WORD → bit/element SLICE `@slc`/`(a>>i)` ([`word_elem_select_demo`](../../examples/rtl2asp/word_elem_select_demo)); unpacked array → memory cell |
| `[base+:w]` indexed part-select | ✅ | constant base → constant `@slc`; **runtime base** → `(a>>i)&mask` via `@shr`/`@band` (`-:` shifts by i-(w-1)) ([`dyn_partsel_demo`](../../examples/rtl2asp/dyn_partsel_demo)); **genvar base** `a[i*W +: W]` inside a generate → lane `i` of `a` as W-bit lanes (see `generate for`) |

## 3. Continuous & procedural assignment
| Feature | Status | Notes / next |
|---|---|---|
| `assign` continuous | ✅ | the combinational mainline (Group 1) |
| `always_ff` / `always @(posedge)` | ✅ | sequential (Group 2): next-state `val(reg, V, T+1) :- time(clk, T), T<k, …`; reset/enable/case become guarded branches, mutually-exclusive + exhaustive so exactly one value per cycle |
| `always_comb` | ✅ | combinational emit at T: assigns/arithmetic, if/else, case (+ default), at T; latch-checked ([`always_comb_demo`](../../examples/rtl2asp/always_comb_demo)) |
| `always @(*)` / `always @(a,b)` | ✅ | no-edge sensitivity -> combinational (reuses always_comb path) ([`always_star_demo`](../../examples/rtl2asp/always_star_demo)) |
| `always @(posedge/negedge clk [or rst])` | ✅ | single edge = clock (any polarity); extra edge = async reset; **dual-edge same clock -> flagged**. A MEMORY write in the reset block's `else` is gated on the reset deasserted at T (it used to write under reset — `test_idiom_sweep_random_stimulus[fifo_ptrs]`) |
| multiple clock domains | ✅ | per-clock `time(Clk,T)`; ≥2 domains → master-tick model (slower clocks linked to the fastest via `gtime/1`; each register HOLDS between its own edges; reset wins over the hold). Modular: per-instance `clkof(Inst,CK)`. [`multi_clock_demo`](../../examples/rtl2asp/multi_clock_demo), [`mc_reset_boundary`](../../examples/rtl2asp/mc_reset_boundary) |
| clock gating (ICG) | ✅ | `clkgate`/`CKG`/`CKGL3` primitive → a DERIVED CLOCK DOMAIN `time(gclk,T):-time(clk,T),val(en,1,T)` (NOT a flop enable, §2.6); flop holds via the master-tick. Flat + **modular** (per-instance `time(gclk(Inst),T)` gated by the instance's own enable; ICG must live inside the unit, cross-domain flagged). [`clock_gating_demo`](../../examples/rtl2asp/clock_gating_demo), [`hier_clock_gating_demo`](../../examples/rtl2asp/hier_clock_gating_demo), [`flop_enable_demo`](../../examples/rtl2asp/flop_enable_demo) (contrast) (`test_idiom_sweep_matches_icarus[icg_clock_gate]`, `[gated_accumulator_and_free_counter]` — matched against Icarus cycle by cycle) |
| `always_latch` | 🟡 | `always_latch if (en) q <= d;` lowers to the same latch schema as the `LATA/B` primitives (Fix 81, [`latch_demo`](../../examples/rtl2asp/latch_demo)); opt-in via `allow_latches`. Only that shape: an active-low enable, a non-net enable/data, or any other body refuses loudly (`[latch_transparent]` in the sweep: transparent timing matched against Icarus) |
| `initial` | 🔲 | out of scope — not functional RTL (state comes from reset; sim/testbench init) |
| nonblocking `<=` | ✅ | the sequential-assignment operator: RHS read at `T`, LHS updated at `T+1` (vs blocking `=` = same-`T`). Required inside `always_ff` (blocking there is rejected — corporate convention) |
| array reset by a `for` loop | ✅ | `if (!rst_n) for (i...) tab[i] <= C;` — how an array of REGISTERS is reset (VerilogEval's gshare does it to its PHT). Lowered as a per-cell LEVEL force, the array's power-on comes from it (no `__xinit` entry), and the edge is gated on the reset at BOTH ends. Was DROPPED SILENTLY until 2026-08-20 (F25). A loop that does not cover the whole array is a NAMED refusal. (`test_idiom_sweep_matches_icarus[array_reset_by_for_loop]`) |
| array reset with MORE THAN ONE write port | ✅ | the same reset beside two guarded writes (`if (up) tab[wa] <= tab[wa]+1; else tab[wa] <= tab[wa]-1;`) takes the coordinated "last-write-wins + joint hold" path, which never consulted the reset: no force, no edge gating, and the joint hold told every cell to HOLD under reset. DROPPED SILENTLY until 2026-08-20 (F26). Write ports that DISAGREE about the reset are a named refusal. (`test_idiom_sweep_matches_icarus[array_reset_two_write_ports]`) |
| `mem[a][b]` bit select of a memory CELL | ✅ | one index for the array, the next INSIDE the cell's packed value — how a table of saturating counters is read (`pht[idx][1]`: the MSB is the prediction). `@slc` composes over the cell read. Refused as a rank mismatch until 2026-08-20, which it never was — the ranks agree. ≥3-D arrays are still deferred, and a RUNTIME bit index into a cell refuses by name. |
| `{n{1'bx}}` replication of `x` | ✅ | `{7{1'bx}}` **is** `7'bx` — a whole value that is unconstrained, how a reference says an output means nothing when it is not valid. Folded to one `XVal`, so it takes the assigned-x path below. A MIXED concat (`{a, 1'bx}`) is NOT folded and stays refused: it says some bits are unconstrained and others are not, and `dontcare_at` is a whole-signal declaration. |
| `x`/`z` literal ASSIGNED as a value | ✅ | UNCONSTRAINED (2026-08-20): in a case/ternary arm inside an always block AND as an arm of a CONTINUOUS-ASSIGN ternary (`assign y = valid ? v : 'x;`) — the second position was wired up on 2026-08-20; before that the whole assign was refused, taking the valid arm's content with it. no design rule, a value-free `dontcare_at(Sig, T)` declaration of WHERE, and the CHOICE in the boundary companion (`{ val(y,V,T) : V = 0..2^w-1 } = 1 :- dontcare_at(y,T).`) — so a property must hold for EVERY resolution instead of an invented 0. An enum's domain is its member pool; too wide to enumerate gets guidance, not a blow-up. (`test_x_dontcare_is_a_real_choice`, `test_idiom_sweep_matches_icarus[x_dontcare_unreachable_arm]`) |
| `x`/`z` used as a value to COMPUTE with | ❌ | `a === 4'bxxxx`, `a + 8'bxx01`: refused by name in BOTH modes (`ir/enumval.py::x_misused`, run at the single Design site) — a 2-state model cannot say what `x` equals. (`test_refusal_sweep[x_literal_compared]`) |
| `{a,b,c} <= v` concat TARGET | ✅ | a concatenation on the LEFT of an assignment: distributed MSB-first into one ordinary write per target (`{pm,hh,mm,ss} <= v` -> `pm <= v[24]`, `hh <= v[23:16]`, ...), including the implicit hold and a reset-branch constant, which is split per target. An operand may also be a CONSTANT part-select (`{q[3:0], r, q[7:4]} <= v`): a whole signal becomes an ordinary write, a part-select a SLICE write, and the RMW machinery assembles them. An operand may also be RUNTIME-indexed (`{q[i], r} <= v`): a concatenation operand has a statically known width, so the SOURCE split is fixed and only where the bit lands is dynamic — it decodes like a bare `q[i] <= b`. (`test_idiom_sweep_matches_icarus[concat_assign_target, concat_target_part_selects, concat_target_dynamic_bit]`) |
| `q[i] <= b` runtime bit-write to a PACKED vector | ✅ | a decoder: one GUARDED single-bit write per position (`q[k] <= (i==k) ? b : q[k]`), composed by the slice-write RMW, so the target stays an ordinary register — word reads, the implicit hold and the power-on policy all follow. Previously took the MEMORY path and emitted addressed cells for a signal that is not an array (`addr(q,A)` never emitted, no power-on) — a loud refusal, so it did not translate at all. Width is the cost, so above 64 bits it refuses by name. (`test_idiom_sweep_matches_icarus[dynamic_bit_write_packed]`, `test_refusals[runtime_bit_write_over_budget]`) |
| several guarded writes to ONE register | ✅ | whole and part-select writes to a register compose as a PRIORITY CHAIN — last write whose guard holds wins, an unguarded write replaces the chain below it, no guard means self-hold (`_priority_chain`). Covers a guarded whole write beside slice writes, and one region written repeatedly (`if (c) q[3:0] <= 0; else q[3:0] <= q[3:0]+1;`). Writes to DIFFERENT OVERLAPPING regions in one block (`q[3:0]`, then `q[7:0]`, then `q[7:4]`) are folded in SOURCE ORDER instead — "replace this region if the guard holds, else keep" (`_ordered_rmw`), the LRM's nonblocking semantics; the disjoint case keeps the one-expression mask/or form. (`test_idiom_sweep_matches_icarus[slice_writes_same_region_priority, guarded_whole_write_beside_slices, slice_writes_overlapping_regions]`) |
| blocking `=` | 🟡 | accepted in comb context; rejected in `always_ff` (corporate convention) |

## 4. Procedural control flow
| Feature | Status | Notes / next |
|---|---|---|
| `if`/`else` (priority) | ✅ | else-negation, per-register grouping (fixed the sync-reset bug) |
| `if` condition = comparison / `&&` / compound | ✅ | hoisted into a synthetic combinational bit `<lhs>__cN`; a BARE condition wider than one bit or enum-typed (`if (n)`, `if (!n)`, `if (state)`) is the LRM's non-zero test, hoisted as `(n != 0)` — it used to be the guard `n == 1` (`test_idiom_sweep_matches_icarus[wide_bare_if_condition]`) |
| `case` | ✅ | per-arm rules + per-arm hold (FSM, §2.5) |
| `case` `default` | ✅ | default arm covers remaining tags |
| `casex` / `casez` | ✅ | priority chain of masked equalities `(sel & care_mask)==pattern`, hoisted gconds ([`casez_demo`](../../examples/rtl2asp/casez_demo)); a FULLY-specified arm (no wildcard, e.g. `4'b0001`) handled via an all-cared mask (`test_casez_fully_specified_arm`, the Goldschmidt LZD) |
| reset: sync | ✅ | plain `if(rst)` priority (no special-casing) |
| reset: async | ✅ | head-at-T clear (rst in sensitivity); the clocked update is gated on the reset deasserted at BOTH ends of the edge and an edge under reset keeps the reset value (`test_idiom_sweep_matches_icarus[lfsr8]`, `[counter_wrap]` — reset pulsed mid-run, matched against Icarus cycle by cycle) |
| enable | ✅ | `if(en) q<=d;` → update branch (`val(en,1,T), val(d,V,T)` ⇒ `q<=d`) + explicit hold branch (`en=0` ⇒ `q<=q`); exactly one value per cycle (`test_unconditional_update_has_no_spurious_hold`) |
| `for` (procedural, in always) | ✅ | loop var rolled to a lane index (like generate); always_comb + always_ff ([`proc_for_demo`](../../examples/rtl2asp/proc_for_demo)). Any constant arithmetic progression `for (i = L; i < N; i += S)` — the rule takes the loop's own index set `I = L..N-1[, (I - L) \ S = 0]`, so a loop from 1 leaves lane 0 to its own statement, a partial loop from 0 leaves the rest alone, and a stride skips the lanes between (`test_lane_roll_over_a_partial_index_set`, arbitrated against Icarus in both modes). Over an unpacked MEMORY the loop may start above 0 too (a `below`-the-start hold; a lane-rolled port is coordinated with the memory's other ports). A write target at the loop variable offset by a constant (`r[i+1] <= r[i] ^ p[i]`) has head lane `I+1`. REFUSES loudly: a runtime bound (`i < n`), a multiplied index on the write target (`y[2*i] <= …`), a strided memory loop |
| blocking accumulation / default-override (always_comb) | ✅ | a signal assigned unconditionally + elsewhere (`s=s+x` reduction, `y=0; if(c) y=a`) → SSA via the function executor ([`blocking_accum_demo`](../../examples/rtl2asp/blocking_accum_demo), default-override test) |
| combinational memory (array of wires) | ✅ | written/read at the SAME T — `val(mem(A),V,T) :- time(_,T), ...` (no clock, no T+1) ([`comb_memory_demo`](../../examples/rtl2asp/comb_memory_demo)). Write-enable form (defaults + trailing guarded override `if(we) mem[addr]=data`, **dynamic** addr) is last-write-wins: the default at the overridden cell is suppressed via `mem_def_ok` so no cell is multi-valued (`test_dynamic_comb_memory_write`); 2+ overrides flag |
| `repeat (N)` (procedural) | ✅ | unrolled to N body copies (N constant) |
| `while` / `foreach` in always_comb | ✅ | blocking loop → SSA unroll via the executor (loop counter folds to literal indices); `s=0; while(i<N) s=s+mem[i];`; `foreach(a[i])` unrolls over each dim's range; loop step `i=i+1` OR `i++`/`i--` (`test_foreach_and_postincrement_in_always_comb`) |
| `for` / `while` over an **array/memory** | ✅ | `for(i) q[i]<=expr` (and for-shaped `while`) lane-rolls over the address domain — `val(q(I),V,T+1) :- addr(q,I), …` (one rule); `q[i]<=src[i]` reads `val(src(I),..)`; partial range / guarded hold the rest; loop var never a signal (`test_loop_over_memory`, [`loop_mem_demo`](../../examples/rtl2asp/loop_mem_demo)). Fixed a prior silent miss |
| `while` (always_ff, for-shaped, indexed) | ✅ | statically-bounded for-shape lane-rolls like `for` (the `i=i+1` increment is swallowed); see row above |
| runtime-bounded loop / `forever` | 🔲 | **not synthesizable** (a hardware loop needs a constant trip count) → out of scope; flagged loud, never to be supported |

## 5. Functions & tasks
| Feature | Status | Notes / next |
|---|---|---|
| `function` (pure, single return-expr) | ✅ | inlined at call site (§1.11), incl. package functions |
| `function` with locals / multi-statement | ✅ | inlined by symbolic execution — blocking assigns bind locals (SSA via substitution), body collapses to one expr ([`func_locals_demo`](../../examples/rtl2asp/func_locals_demo)) |
| `function` with `if`/`else` body | ✅ | branches merged per assigned variable into a `Cond`; default-then-override + chained `else if` (nested, hoisted) ([`func_if_demo`](../../examples/rtl2asp/func_if_demo)) |
| `function` with `case` body | ✅ | first-match priority `Cond` chain; multi-label arm → OR gcond ([`func_case_demo`](../../examples/rtl2asp/func_case_demo), CPU opcode decode) |
| `function` with `for`/`while`/`repeat` loop | ✅ | statically-bounded loop UNROLLED — `for`/`while` fold the condition, `repeat(N)` is N copies ([`func_loop_demo`](../../examples/rtl2asp/func_loop_demo) popcount). A runtime-bounded loop flags (sound) |
| `function` with enum-selector `case` | ✅ | each arm a TAG compare (`st == IDLE`) → first-match `Cond` chain ([`func_enum_case_demo`](../../examples/rtl2asp/func_enum_case_demo)). `forever`/`do-while` still flagged |
| `task` | 🔲 | out of scope — a DV/testbench construct, not functional/design RTL (functions cover synth reuse) |
| system fns `$clog2`/`$bits` | ✅ | elaboration-time constants |
| `$signed`/`$unsigned` | ✅ | reinterpret cast (same bits); pass-through, signedness flows to downstream ops; widening `$signed` sign-extends via `@sext` ([`signed_demo`](../../examples/rtl2asp/signed_demo)) |
| `$display`/`$finish`/… | 🔲 | non-synthesisable |

## 6. Structural / hierarchy
| Feature | Status | Notes / next |
|---|---|---|
| module instantiation (user submodule) | ✅ | flattened, instance-path qualified (§4.3) |
| named port connection | ✅ | `.formal(actual)` → port bridge: flat aliases the formal onto the connected net; modular emits a manifest bridge rule (struct ports per field, interface ports per signal by modport direction) |
| positional port connection | ✅ | pyslang normalizes positional → named by order; the emitted rules are IDENTICAL to the named form (only the `%` provenance comment differs) — `test_positional_port_connection` (rule-set equality + clingo) |
| primitive/stdcell instances | ✅ | registry: flops, gates, AOI/OAI, mux2/3/4, latches, VFF. Each lane is a FUNCTOR signal `val(q(I), V, T)`; a `VFF #(.WIDTH(W>1))` keeps the same one-rule shape with the per-lane value a whole W-bit WORD (so word arithmetic on a lane works), self-described by `lane_shape(q, lanes(N), width(W))` (`test_vff_width`) |
| parameterized instance (per-instance params) | ✅ | each `(module, param-tuple)` resolved concretely; in modular mode → one spec file per distinct tuple (`acc_unit__w4` / `acc_unit__w8`), §3.10/§4.4 ([`deep_hier_demo`](../../examples/rtl2asp/deep_hier_demo)) |
| `generate for` | ✅ | rolled to indexed rules (§4.6, [`generate_demo`](../../examples/rtl2asp/generate_demo)); its body uses the full module-body dispatch, so it may contain a conditional generate, an `always` block (a generate of registers), instances, and nested generates — all lane-rolled (`test_conditional_generate`). A signal read WHOLE in the body (`y[i] = a[i] & en`) is a per-lane BROADCAST, read bare (`test_generate_lane_broadcast_is_read_whole`). The genvar may take any constant arithmetic progression (`for (i = 1; …)` → `I = 1..N-1`, lane 0 to its own `assign`; `i += 2` → `I \ 2 = 0`), and a genvar-DEPENDENT conditional (`if (i == 0) : first … else : rest`, `if (i % 2 == 0)`) is partitioned into classes of equal structure, one rule per class over its own progression — with a neighbouring-lane read `c[i-1]` as the lane term `c(I-1)`, so a ripple chain is a founded chain (`test_lane_roll_over_a_partial_index_set`, arbitrated against Icarus in both modes; also two AGREEMENT probes in `proofs/gen_ieee_diff.py`). The byte-lane idiom `y[i*8 +: 8] = a[i*8 +: 8] ^ b[i*8 +: 8]` (also `8*i`, `i*8+7 -: 8`, clocked) is lane `i` of each signal as 8-bit lanes — the same shape a packed 2-D gets from `y[i]`, bridged at `I * 8` (`test_byte_lane_slices_are_lanes`, Icarus-arbitrated both modes; a `gen_ieee_diff` probe). A write target at the genvar OFFSET by a constant — the carry-lookahead `c[i+1] = g[i] \| (p[i] & c[i])`, or `r[i+1] <= r[i] ^ p[i]` — has head lane `I+1` while the domain stays the loop's own (`test_lane_roll_over_a_partial_index_set`, `gen_ieee_diff` probe). A neighbouring-lane read `x[i-1]` / `x[i+1]` of a MULTI-BIT packed lane (a shift register on a packed 2-D, `sh_d[i] = sh_q[i-1]`) is a lane read `x(I-1)` regardless of where in the file `x` becomes a lane, and a BARE such read is a lane comb (F17 — the order-dependent version read lane I silently); a lane register's async clear carries the lane domain; a `logic` DECLARED INSIDE the generate body is per-iteration and so a lane of the loop's extent (`logic t; assign t = !any[i-1];`); the per-lane boolean-conjunct form (`(a[i] == 1) && v[i]`) takes the loop's own range like every other lane path (all Icarus-arbitrated in `test_lane_roll_over_a_partial_index_set`). REFUSES loudly: a class that is not an arithmetic progression (`if (i != 2)`), a MULTIPLIED index on the write target (`y[2*i] = …`), a slice whose base is not exactly `genvar * width` (`a[i*8 + 4 +: 4]`), one signal viewed with two lane widths (`a[i]` and `a[i*8 +: 8]`), an array/struct/enum or a NESTED-generate local declaration |
| **a FIELD of a lane's word at an affine position** (`pp[i][((i-1)*2)+2 +: 65]`, `[hi:lo]` with affine bounds, constant fields `y[i][3:0]`) | ✅ | the fields of one word compose into ONE lane definition (masked, shifted to a position the rule computes from `I`), checked disjoint and covering over the loop's range; a moving-width field takes a fill (`'0`/`'1`) or one replicated bit (the sign extension) -- the Booth partial-product stitch (2026-09-04); other genvar-dependent targets stay refused by name |
| **a lane read at a sub-element** (`enc[i][2]`, `enc[i][1:0]` on `logic [N][3] enc`) | ✅ | a slice of the lane's element -- not a second lane width (2026-09-04) |
| **a window read at an affine offset** (`m[2*i+2 : 2*i]`, `m[2*i+1 +: 2]`) | ✅ | shift-and-mask by the affine amount, the lane index as the amount; the width must be the same at every iteration (2026-09-04) |
| **a lane element built from comparisons** (`enc[i] = {(w[i]==3) \| (w[i]==4), (w[i]!=0) & (w[i]!=7), w[i][0]}`, the Booth digit bits) | ✅ | one-bit bitwise and/or over boolean nodes is the logical connective; the per-lane path takes any one-bit boolean over lane leaves, the leaves read the lane's element (2026-09-04) |
| **a hand-wired fan-in from many lanes** (`out[0] = {pp[2][1:0], pp[1][5:2], pp[0][7:6]}`, a Wallace-stage wiring, no genvar) | ✅ | the per-bit flattener reads slices of lane members and slices of slices (2026-09-04); a per-bit refusal names the leaf it could not read |
| **a primitive mux instantiated inside a generate** (its output a per-iteration local, arms `a[i]`/`b[i]`, a concatenated selector) | ✅ | the mux rule is per lane, the selector read by its per-bit atoms (2026-09-04) |
| **nested `generate for`** | ✅ | rolls to ONE rule with N functor lane indices `val(sig(I,J),V,T)`; per-signal lane-dim count ([`nested_generate_demo`](../../examples/rtl2asp/nested_generate_demo)). Covers comb, registers, AND **a 2-D grid of module INSTANCES** (`for(i)for(j) pe u(.a(a[i][j]),…)` — the systolic/PE-array idiom: lane-rolls over a 2-D lane domain `lane(owner,0..N-1,0..M-1)`, flat + modular; [`pe_grid_demo`](../../examples/rtl2asp/pe_grid_demo), `test_nested_generate_of_instances_matches_flat`) |
| `generate if` / `generate case` | ✅ | param condition resolved at elaboration; inline the TAKEN `GenerateBlock` ([`generate_if_demo`](../../examples/rtl2asp/generate_if_demo)) |
| arrays of instances | ✅ | lane-rolled: array index = lane I, sliced ports → INDEXED parent net, internals → `u(sig)`, `lane(u,0..N-1)` ([`inst_array_demo`](../../examples/rtl2asp/inst_array_demo)). Arrays of PRIMITIVE cells too — a gate array → one lane comb rule, a flop array → a lane register (shared/no en → guard) or VFF (per-lane en) ([`prim_array_demo`](../../examples/rtl2asp/prim_array_demo), `test_primitive_array`); non-uniform (fixed-bit/strided/non-uniform params) flagged |
| interfaces / modports | ✅ | interface = bundle of SHARED wires → flat nets `inst(sig)`; hierarchical ref `b.data`→`b(data)`; submodule interface port aliases to the connected instance (no copy), so modules unify on the shared net ([`interface_demo`](../../examples/rtl2asp/interface_demo), producer→consumer). Modports recognized (structural) |
| multi-level hierarchical reference | ✅ | `top.u_mid.u_leaf.acc` (any depth) → nested functor `u_mid(u_leaf(acc))`, matching the flattened signal; read-only, top lead stripped (`test_multi_level_hier_ref`) |
| indexed hierarchical reference | ✅ | `u_l[1].acc` → per-lane read `val(u_l(acc), 1, V, T)`: array index = lane (§4.6), same INDEXED signal the lane-rolled body drives; constant index (runtime index is illegal SV → flags) (`test_indexed_hier_ref`) |
| hierarchical submodule **memory** | ✅ | a memory inside a submodule flattens instance-qualified — `val(u_ram(mem(A)), V, T)`, decl/write/hold/read carried, clock substituted to the parent; submodule loop-over-memory carries the lane-roll (`test_hierarchical_memory`) |
| partially-connected instance | ✅ | an unconnected port `.x()` gets no bridge — an output is unobserved, an input stays undriven (`test_unconnected_port`) |
| nested multi-level hierarchy | ✅ | composable via functor nesting, 3–4 levels deep, tested flat + modular; per-instance params through 2 levels, clock/enum/reset/memory all bridged across every boundary ([`deep_hier_demo`](../../examples/rtl2asp/deep_hier_demo) top→lane→acc_unit→FF, `test_deep_hier_demo`, `test_multi_level_hier_ref`, `test_modular_matches_flat`); indexed hier-refs `arr[i].sig` flagged (deferred) |
| struct-return function | ✅ | a fn whose implicit return var is written field-by-field (`mk.hi=a`) inlines + assembles the packed return MSB-first from per-field subsignals (`test_struct_return_function`) |
| array-member-of-struct `s.arr[i]` | ✅ | an unpacked-array struct field → a struct-field memory `s(arr)` with its own addr domain, `val(s(arr(A)), V, T)`; const + dynamic index (`test_array_member_of_struct`). 1-D scalar cells; deeper/nested flag |
| generate-for stamping instances | ✅ | `for(i) sub u(.a(d[i]),…)` lane-rolls like the `sub u[N]` instance array (shared `_lift_instance_lanes`): comb / clocked / primitive-cell arrays (`test_generate_for_instances`) |

## 7. Verification layer — OUT OF SCOPE (handled separately)
| Feature | Status |
|---|---|
| `assert`/`assume`/`cover property` | 🔲 recognized as `property`, not translated (hand-authored property layer) |
| `sequence` / `property` blocks | 🔲 |
| immediate assertions | 🔲 |
| `covergroup` / functional coverage | 🔲 |

---

## Compositionality / recursion (SV expressions nest arbitrarily)
The word-expression emitter (`_word_body`) is **fully recursive**: arithmetic, `/`,`%`, shifts,
bitwise, slices/part-selects, and concatenation nest to any depth (`{a+b, c[5:2]} & d` works).
But a few forms are handled only as a **top-level rhs shape**, so they FLAG (never mistranslate)
when nested inside another expression — be aware:

| Form | Top-level rhs | Nested in an expression |
|---|---|---|
| ternary `?:` | ✅ | ✅ (hoisted into a synthetic `<lhs>__tN` signal) |
| reduction `\|x`/`&x`/`^x` | ✅ | ✅ — word/expr reduction (`\|(a&b)`) handled |
| element-select → scalar bit | ✅ | ✅ — `a[i]` on a packed WORD is a bit/element SLICE: const `@slc`, dynamic `(a>>i)` ([`word_elem_select_demo`](../../examples/rtl2asp/word_elem_select_demo)); `a[i]` on a VFF/lane signal stays a lane read |
| enum tag compare | ✅ | ✅ — a compare/tag-compare in a WORD context (concat part, arithmetic operand) hoists to a 1-bit `gcond`, read shape-aware ([`concat_compare_demo`](../../examples/rtl2asp/concat_compare_demo), `{(s==IDLE),x}`) |
| 1-bit logic via `always_comb` | ✅ | ✅ — an unconditional combinational assign of an expression routes to a CombItem, so `always_comb g=c0&c1;` reaches the Group-1 bit/word emitter (was `assign`-only) |

## Modular mode coverage (the default compile)

Modular (`-o out/`) translates each `(module, param-tuple)` once into an instance-parameterised spec
(rules over the instance variable **`Inst`**, guarded by `isa(Inst, spec)`), wired by a `<top>__inst.lp`
manifest (`isa`/`clkof`/port-bridges + an atom legend). Spec files carry the same `% file:line` provenance
as flat. **Parity with flat is a standing invariant** (`_assert_modular_matches_flat`). Status:

| Construct (in modular) | Status |
|---|---|
| combinational, sequential, FSM/enum-tag, struct/interface/reset/enum **ports** | ✅ |
| multi-clock (master-tick) + ICG **clock gating** (per-instance `time(gclk(Inst),T)`) | ✅ |
| **memory** — scalar (dynamic addr), lane-rolled `for(i) q[i]<=…`, **multi-dimensional** | ✅ — per-instance `addr(Inst,mem,A[,A2])` + init/write/hold (`test_modular_memory_matches_flat`, [`array2d_demo`](../../examples/rtl2asp/array2d_demo)/[`loop_mem_demo`](../../examples/rtl2asp/loop_mem_demo) parity) |
| **lane / VFF / array-instance** state | ✅ — per-instance `lane(Inst,owner,K)` domain; VFF + genvar lanes fan over operand reads (`test_modular_lane_constructs_match_flat`, `test_modular_vff_matches_flat`) |
| numeric ↔ enum **cast** (`op_t'(x)`) | ✅ — the global `enum_value(…)` facts are emitted once in the manifest (`test_modular_enum_cast_computes`); modular even handles a cast in a submodule, which *flat* can't (EnumCast doesn't wrap across the flatten boundary) |
| **multi-clock master-tick holds** for lane / VFF / **memory** | ✅ — `_spec_holds` mirrors `_emit_multiclock` per-instance (a slow-clock memory holds across idle ticks: [`mc_mem_demo`](../../examples/rtl2asp/mc_mem_demo), `test_modular_multiclock_memory_matches_flat`); building it fixed a *flat* bug (the hierarchical memory hold emitted the invalid curried `u_a(mem)(A)`) |
| **multiple clock domains WITHIN one module** (incl. cross-domain ICG) | ✅ — the manifest emits a **per-clock-port** `clkof(Inst, Port, Clk)`, so each flop / gated clock resolves to its own domain ([`intra_mc_demo`](../../examples/rtl2asp/intra_mc_demo), `test_modular_intra_module_multiclock_matches_flat`); building it fixed a 2nd *flat* bug (an ICG base clock that isn't a flop clock was wrapped `u(clk2)` instead of substituted) |

With per-port `clkof`, modular has no known flat-only gap. The instance variable is `Inst` precisely so it
never collides with the lane/address indices `I`/`J`… (a single-letter `I` would unify with
`addr(…, I)`/`lane(…, I)` and silently break lane-rolled / multi-dim / lane constructs). Every spec carries
`% file:line` provenance; the manifest opens with an atom legend.

**Self-describing specs.** Each spec file also emits its own **schema** — `type(Inst,Sig,Kind,W)` /
`port(Inst,Sig,Dir)` / `reg(Inst,Sig)` / `clock(Inst,Sig,Clk)`, guarded by `isa(Inst, spec)` — so a
consumer can read a signal's shape/direction/register-ness/clock straight from the modular set, with no
flat cross-map. This is what lets `scripts/cds.py` (control/data separation, `docs/ASP_HARDWARE_VERIFICATION.md`
§5.8) classify the modular output directly and fan the result over `isa`.

## Forward-looking work → see `notes/WORKLIST.md`

What's *next* — essentially the two methodology-level capability items (**capacity** — wide-datapath
∀-input proofs via completion → Lean (`BitVec`/`bv_decide`); the `&bv` theory-atom boundary is deferred
to the foundedness+wide-data niche; **liveness** — via the completion / well-founded route), plus the
deliberate **out-of-scope** list — all live in **`notes/WORKLIST.md`**. This file stays the per-construct
*status* (✅/🟡/⚠️/❌); the worklist is the *plan*. Everything unhandled is flagged loud, never
silently mistranslated.

**By design (NOT a gap):** combinational *partial-coverage* writes (undriven bits) stay flagged —
positive-definite design layer, no choice rules; rolled up as a "SIGNALS WITH UNDRIVEN BITS" audit list.
