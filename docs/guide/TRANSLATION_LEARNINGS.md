# Translating existing RTL — what the field has taught this tool

This document is for someone pointing the translator at a real block: a design with vendor
cells, memory wrappers, macros and include files, none of which the tool's own corpus
contains. It is not a manual. `docs/guide/SOURCES_MANIFEST.md` is the manifest reference and
the `/release-v2` skill is the procedure; this is the shorter and more useful thing, which is
the list of ways a real tree has actually gone wrong, each with what the run looked like at the
time and what to do about it.

Every entry below came from a REPORT: a translation run against a design the tool's maintainer
never sees, sent back as the `--report` file, the coverage file and a description. Nothing of
any reported design appears here. Each was reconstructed under invented names, fixed, and
pinned by a test that fails if the defect returns.

## How to read a run at all

Three outputs, and they answer different questions. Conflating them wastes the most time.

**The `coverage:` line** answers *did every source construct lower?* It counts declared,
emitted and structural lines and ends in `OK (no design omissions)` or names what was missed.

**The exit status** answers *is this program safe to reason over?* It is NOT the same question.
A run can print `coverage: OK` and still exit non-zero, because coverage is about constructs
and the exit status also covers unsafe rules, dark reads and state with no power-on policy. A
clean coverage line is necessary and not sufficient.

**`--report FILE`** is the raw detail for the maintainer and **`--log FILE`** is the stable
verdict with the findings grouped. Read the log; send the report. `--coverage FILE` writes the
per-line map, which is what settles an argument about a single header line or port declaration.

`--allow-problems` forces a zero exit so you can look at an incomplete translation. Nothing
produced under it may be used for a proof, and the flag exists to be read as that admission.

## A PROBLEM with no bracketed reason is the classifier talking, not a refusal

A problem line that carries a construct's message in brackets is a refusal: the tool met
something it will not lower, and it says what. A problem line with no bracketed reason — a
comment, a port name, a loop header — is the coverage MAP's own reading of the file, not a
refusal. The two look alike in a summary and mean opposite things.

The reason this happens is that the map resolves macro locations and include members, so a
block whose header comes from an include can have lines attributed to a file the module does
not own. When you report one of these, keep the module's include files and header macros in the
probe: those are what the map is reading, and without them the shape does not reproduce.

## A declared stub or black box that binds is not always reported as binding

**The defect, found 2026-09-11.** A stub declared in the manifest was applied — its rules were
in the output — and the run reported it as `never bound: no instance of that module was found,
so it was NOT stubbed`, then exited non-zero saying the program was incomplete. The stub was
fine. The check was wrong.

It came from a global question being asked at a per-module moment. "Did this declared stub ever
bind to any instance?" has an answer only after every module is lowered, and the check ran from
the lowering of each module, against a set that fills up as instances are visited. Flattening a
child instantiated *before* the stubbed instance answered the question with an empty set. So it
depended on the source order of two instance lines, and it appeared in flat mode only.

**What to do if you see anything like it.** Verify against the output rather than the message.
A stub that bound leaves a marked section and rules over the instance's ports:

    rg -n "FUNCTIONAL STUBS|functional stub: <module>|<inst>\(" out/translation.lp

A black box that bound leaves `blackbox(<inst>(<port>), <width>)` and a `dontcare_at` for it. If
those are present, the model is sealed as you asked, whatever the summary said.

**The lesson, which is older than this defect.** An order-dependent decision is wrong for the
order nobody wrote. The tool has paid for this shape before, in lane reads whose meaning
depended on whether a signal had been seen yet. Any check that compares "declared" against
"used" has to run where the second half is complete.

**And the reason it mattered more than a cosmetic warning.** That check guards the worst-shaped
defect this tool can have: a block you asked to SEAL behind a functional model, translated in
full instead, silently, with coverage happy because every line really was translated — after
which any proof runs against the very implementation the stub was there to abstract away. A
false alarm on that check is not noise. It teaches a reader to ignore the one message that
stands between them and a meaningless proof, which is why it was fixed rather than suppressed.

## Stub or black box is your choice, never the tool's

A stub replaces a module with a model you wrote, when you know what the block does. A black box
replaces it with nothing: every output is free at every instant, so a property over its
consumers holds for every value the box could produce. Both are declared in the manifest.

The tool never promotes a module to either one on its own — not a memory wrapper, not a vendor
hard macro, not a module whose definition is missing. A module with no definition in scope stays
a loud refusal until you say which treatment it gets. This is deliberate: both choices weaken
what a proof says, in different ways, so both belong to the person who signs the proof.

## Reporting a gap

Send the `--report` file, the `--coverage` file, and a MINIMISED probe under invented names.
Never the design. A probe that reproduces the shape in fifteen lines is worth more than the
block, and it is what the fix is built against — every entry in this document was fixed that
way, and the test that keeps it fixed uses the probe, not the original.

Two failure modes in reporting, both of which have cost a round trip:

* **A probe that does not go through the real entry point reproduces itself.** A harness built
  around an internal class, configured by hand, tests the harness. Drive the probe with the
  command you actually ran.
* **Absent output is not evidence.** A command that printed nothing may not have run. Check the
  exit status and the argument shape before concluding that a check is silent; the modular mode
  writes a file SET and refuses a single-file `-o`, which is easy to miss in a pipeline whose
  output is being grepped.
