# sv2asp2 — start here

This folder is the **tools** folder for the spec2rtl route: a way to take a block's
requirements in English all the way to SystemVerilog, with a machine-checked proof in the
middle. If you are a coding agent, you are probably reading this because someone pointed
you here from their own working folder next door.

## Where things live

    parent/
      tools/        <- you are here: the tool, the skill, the documentation, two examples
      myBlock/      <- the WORKING FOLDER: the user's session runs here
        SPECIFICATION.md    <- their starting point, written by them
        myBlock.yaml        <- then the signature and the controlled English
        myBlock.cnl
        spec.lp  l1.lp  ...   <- then everything the route generates, all of it here

**Nothing is ever written into this tools folder.** Every artifact of a block belongs to
the working folder beside it; this folder supplies the tool and the knowledge. Run the
tool from the working folder with the environment `setup.sh` built here:

    ../tools/.venv/bin/python -m sv2asp.aspfirst2 <verb> ...

(or `. ../tools/.venv/bin/activate` once, then `sv2asp2 <verb>`). If `setup.sh` has not
been run yet, run it in this folder first — it assumes nothing about the machine.

## Starting from a specification

The user's `SPECIFICATION.md` is the beginning: the English in force, with its
ambiguities resolved and recorded. From it come the signature and the controlled English,
and from those the contract, the design, the certificate and the RTL — each a rung of the
ladder, each approved by the user before the next begins. The skill
(`.claude/skills/spec2rtl-dsl/SKILL.md`) is the procedure; follow it rather than
improvising, and read `examples/spec2rtl2/rv_missq/` as the worked pattern — it carries
every artifact a finished block has, including its `ladder.yaml`.

## What the route is

    English (resolved)  ->  controlled English + a signature  ->  the ASP contract
                        ->  a design written against that contract
                        ->  a certificate (proved for all time, not simulated)
                        ->  printed SystemVerilog, round-tripped against a simulator

The contract is the anchor: everything below it is proved against it, and the design is
written *by you or by a model in the loop*, judged by the certificate rather than by
opinion.

## The rules that are not negotiable

1. **The ladder.** Every artifact is a rung: it is built, explained in plain language,
   and then **approved by a person** before the next begins. No command sets `approved` —
   a human edits `ladder.yaml`. If you are an agent: stop at each rung and ask.
2. **Never hand-edit a generated file.** The core, the contract, the printed RTL and the
   logs are regenerated from their sources by a command. Edit the source and re-run.
3. **A refusal is information.** The tool refuses by name rather than guessing; the fix
   is to change the input, never to work around the tool.
4. **Read a report's exclusion lines.** "reset held released", "NOT EXERCISED",
   "bounded-only" bound what a verdict claims.

## Where to look

| you want | read |
|---|---|
| **to start — a guide for a hardware engineer, from zero** | **`docs/spec2rtl2/GETTING_STARTED.md`** |
| the commands and the setup detail | `docs/spec2rtl2/SUITE.md` Part C |
| what every command does, and what is still open | `docs/spec2rtl2/AUTOMATION.md` |
| how to build an entry, step by step | `.claude/skills/spec2rtl-dsl/SKILL.md` |
| the same route starting DIRECTLY from a hand-written `spec.lp` | `.claude/skills/release-v2/SKILL.md` |
| the route's reasoning, and the language reference | `docs/spec2rtl2/ROUTE_METHODOLOGY.md` |
| a complete worked entry | `examples/spec2rtl2/rv_missq/` (and `examples/spec2rtl2/fifo/`, smaller, with a hand-written contract) |

## Support

This tool is maintained centrally. If it refuses something it should accept, or accepts
something it should refuse, re-run the command with `--report issue.txt` and send that
file to the maintainer — it carries the tool version, the resolved toolchain, the command
and the output, and nothing from your design. Attach a *minimised* probe if you can make
one; never your block. Do not modify the installed tool: a certificate from a modified
tool means nothing.
