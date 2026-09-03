"""spec2rtl VERSION 2 (`sv2asp.aspfirst2`) -- the v2 verification core. The governing
document is docs/spec2rtl2/ROUTE_METHODOLOGY.md: properties on external symbols (the ports
directly, linked symbols for the rest), induction in NORMAL form (no spec-side ghost machinery
-- the linkage lint refuses ghost state outside `refmodel`), composition assume-guarantee
(units proven standalone). The stable front (loader, composer, lint, printer, round trip,
expand, flow) is carried from v1 unchanged; v1 is frozen at `src/sv2asp/aspfirst/`.

The library (`lib/aspfirst/aspfirst.lp`) gives the facts their semantics with rules that mirror
the translator's PROVEN emitted shapes -- the FF capture/hold pair, ARFF's four async-reset rules,
the memory write + `mem_hold` partition -- so hold/set semantics fall out of the primitives and
are never re-authored per design. See `docs/guide/ASP_FIRST_DESIGN.md`.

    python -m sv2asp.aspfirst2 lint      design.lp
    python -m sv2asp.aspfirst2 print     design.lp [--mode cells|behav] [-o design.sv]
    python -m sv2asp.aspfirst2 roundtrip design.lp scenario.lp [--mode ...] [--icarus]
"""
