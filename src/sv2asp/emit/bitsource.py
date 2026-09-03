"""Typed per-bit source ADT for the bitvec (per-bit) emitter.

``_bitvec_flatten`` lowers a bit-structural RHS into a list of per-bit *sources*, LSB-first: for each
output bit, where its value comes from. The original representation was a tuple whose first element
was a magic string (``"@indexed"``, ``"@shift"``, ``"@cond"``, ``"@or2"``, …); dispatch was string
comparison with positional field access (``entry[1]``, ``entry[2]``). That is the "sentinel string"
debt called out in the re-architecture plan — no type safety, and a typo in a tag silently skips a
bit.

This module replaces those tuples with a frozen-dataclass union. The emitter dispatches with
``isinstance`` / ``match`` and reads named fields. The set of variants and their meaning is a 1:1
map of the old sentinels (so the emitted ASP is byte-for-byte identical):

  old tuple                              -> variant
  ("", 0|1)                              -> ConstBit(v)          constant bit
  (base_name, src_bit)                   -> WordBit(base, bit)   read bit of a packed-word signal (@slc)
  ("@indexed", src_name, src_bit)        -> Indexed(src, bit)    read a per-bit signal directly (no @slc)
  ("@bool1", expr)                       -> Bool1(expr)          a 1-bit boolean expression
  ("@replicated_bool1", count, expr)     -> ReplBool1(count, expr)  N identical Bool1 (coalesced)
  ("@shift", data, op, amount, W)        -> Shift(data, op, amount, w)   index remap (data per-bit)
  ("@cond", sel, bits_a, bits_b, W)      -> CondBits(sel, a, b, w)   masked-mux of two per-bit exprs
  ("@or2", bits_a, bits_b, W)            -> Or2Bits(a, b, w)     OR of two per-bit sub-exprs

The *coalescing* pass (merging consecutive bits that share a rule) keys on ``base_key`` and reads
``cbit`` — the per-variant "coalescing bit" (a source-bit index for WordBit/Indexed, the bit VALUE
for ConstBit, which only ever coalesces equal-valued runs). Variants that never coalesce
(Bool1/Shift/CondBits/Or2Bits) leave those unimplemented.
"""

from __future__ import annotations

from dataclasses import dataclass


class BitSrc:
    """Base of the per-bit source union. Concrete variants below."""
    __slots__ = ()

    # coalescing interface (overridden by the few variants that participate)
    @property
    def base_key(self):
        raise TypeError(f"{type(self).__name__} does not coalesce")

    @property
    def cbit(self) -> int:
        raise TypeError(f"{type(self).__name__} does not coalesce")


@dataclass(frozen=True)
class ConstBit(BitSrc):
    """A constant output bit (0 or 1)."""
    v: int

    @property
    def base_key(self):
        return ""            # all const bits share one key; only equal VALUES coalesce (step 0)

    @property
    def cbit(self) -> int:
        return self.v        # the "bit" used for run-stepping is the value itself


@dataclass(frozen=True)
class WordBit(BitSrc):
    """Output bit reads bit ``bit`` of packed-word signal ``base`` (word form + @slc)."""
    base: str
    bit: int

    @property
    def base_key(self):
        return self.base

    @property
    def cbit(self) -> int:
        return self.bit


@dataclass(frozen=True)
class Indexed(BitSrc):
    """Output bit reads bit ``bit`` of per-bit signal ``src`` directly: val(src(bit), B, T)."""
    src: str
    bit: int

    @property
    def base_key(self):
        return ("@indexed", self.src)

    @property
    def cbit(self) -> int:
        return self.bit


@dataclass(frozen=True)
class Bool1(BitSrc):
    """A 1-bit boolean expression; emitted via _emit_bool (or inline when range-guarded)."""
    expr: object


@dataclass(frozen=True)
class ReplBool1(BitSrc):
    """``count`` consecutive identical Bool1 entries — one range-guarded rule covers all of them."""
    count: int
    expr: object


@dataclass(frozen=True)
class Shift(BitSrc):
    """Variable shift of a per-bit signal (index remap): op in {shl,shr,ashr}; covers all ``w`` bits."""
    data: str
    op: str
    amount: object       # a word-valued Expr
    w: int


@dataclass(frozen=True)
class CondBits(BitSrc):
    """Masked-mux Cond(sel, a, b) of two per-bit arm lists; covers all ``w`` bits."""
    sel: object
    a: list
    b: list
    w: int


@dataclass(frozen=True)
class Or2Bits(BitSrc):
    """OR of two per-bit arm lists (no selector; may be multi-valued); covers all ``w`` bits."""
    a: list
    b: list
    w: int
