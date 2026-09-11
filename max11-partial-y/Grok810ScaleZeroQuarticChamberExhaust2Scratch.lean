import Grok810ScaleZeroQuarticChamberExhaust2Part101Scratch
import Grok810ScaleZeroQuarticChamberExhaust2Part102Scratch
import Grok810ScaleZeroQuarticChamberExhaust2Part103Scratch
import Grok810ScaleZeroQuarticChamberExhaust2Part104Scratch

/-! # Cost-argmin chamber exhaust (2/4), `(8,10)` scale zero

The 15 live-letter sets with |S| ∈ {4}.  Each theorem runs the case tree
of `CHAMBERS.md` §1: a linear tournament for `β = min s|_{B,C}`,
`q = min s|_{D,E}`, `r = min s|_{F,G}`, then `μ₂ = min(q,r)`,
`ω = min(β,q)`, then the three cost types `2μ₂`, `β+r`, `2β+ω`
against each other.  Branches no chamber matches are ℚ-infeasible
(exact Farkas certificates in
`scripts/check_810_quartic_chambers_lean.py`) and close by `omega`.
Untracked working note.
-/

/-! This module is now a pure import aggregator: its declarations live in the
`Part..` modules above, one per file, so that no single module elaborates them
all at once.  Every statement, name, binder and section context is unchanged. -/
