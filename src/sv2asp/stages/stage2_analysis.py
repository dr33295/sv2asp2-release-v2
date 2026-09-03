"""Stage 2 — use-site analysis (compatibility shim).

The classification logic now lives in :mod:`sv2asp.analysis.classify`, restructured into explicit
named phases with the per-bit bridge direction carried as first-class data (see that module). This
module re-exports ``Analysis`` and ``analyze`` so existing importers
(``from .stage2_analysis import Analysis, analyze``) keep working.
"""

from __future__ import annotations

from ..analysis.classify import Analysis, analyze

__all__ = ["Analysis", "analyze"]
