import Grok810ScaleZeroQuarticChamberDefs4Scratch

/-! # Cost-argmin chamber exhaust (3/4), `(8,10)` scale zero

The 6 live-letter sets with |S| ∈ {5}.  Each theorem runs the case tree
of `CHAMBERS.md` §1: a linear tournament for `β = min s|_{B,C}`,
`q = min s|_{D,E}`, `r = min s|_{F,G}`, then `μ₂ = min(q,r)`,
`ω = min(β,q)`, then the three cost types `2μ₂`, `β+r`, `2β+ω`
against each other.  Branches no chamber matches are ℚ-infeasible
(exact Farkas certificates in
`scripts/check_810_quartic_chambers_lean.py`) and close by `omega`.
Untracked working note.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

variable {k : Type*} [Field k] [CharZero k]

section QuarticChamberExhaust810

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEG0
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hs : g < a + 2 * b ∧
      4 * d < a + 6 * b ∧
      4 * e < 3 * a + 6 * b ∧
      2 * c < a + 2 * b) :
    g < a + 2 * b ∧
    2 * c + 2 * g < 3 * a + 6 * b ∧
    4 * d < a + 6 * b ∧
    d + e < a + 3 * b ∧
    d + g < 2 * a + 3 * b ∧
    4 * e < 3 * a + 6 * b ∧
    2 * e + 2 * g < 5 * a + 6 * b ∧
    4 * g < 7 * a + 6 * b ∧
    2 * c < a + 2 * b ∧
    d < a + b ∧
    2 * e < 3 * a + 2 * b ∧
    2 * c < a + 2 * b ∧
    2 * c + 2 * d < 3 * a + 4 * b ∧
    c + e < 2 * a + 2 * b ∧
    2 * c < a + 2 * b ∧
    2 * c + d < 2 * a + 3 * b ∧
    4 * c + 2 * e < 5 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEG1
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hs : a + 2 * b = 2 * c ∧
      2 * c + 2 * g < 3 * a + 6 * b ∧
      4 * d < a + 6 * b ∧
      4 * e < 3 * a + 6 * b) :
    a + 2 * b = 2 * c ∧
    a + 2 * b = 2 * c ∧
    a + 2 * b = 2 * c ∧
    g < a + 2 * b ∧
    2 * c + 2 * g < 3 * a + 6 * b ∧
    4 * d < a + 6 * b ∧
    d + e < a + 3 * b ∧
    d + g < 2 * a + 3 * b ∧
    4 * e < 3 * a + 6 * b ∧
    2 * e + 2 * g < 5 * a + 6 * b ∧
    4 * g < 7 * a + 6 * b ∧
    d < a + b ∧
    2 * e < 3 * a + 2 * b ∧
    2 * c + 2 * d < 3 * a + 4 * b ∧
    c + e < 2 * a + 2 * b ∧
    2 * c + d < 2 * a + 3 * b ∧
    4 * c + 2 * e < 5 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEG15
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hs : a + 2 * b = 2 * c ∧
      5 * a + 2 * b = 2 * g ∧
      d < a + b ∧
      2 * e < 3 * a + 2 * b) :
    a + 2 * b = 2 * c ∧
    5 * a + 2 * b = 2 * g ∧
    a + 4 * d < 2 * b + 2 * g ∧
    d + e < b + g ∧
    d < a + b ∧
    4 * e < a + 2 * b + 2 * g ∧
    2 * e < 3 * a + 2 * b ∧
    a + 2 * b < g ∧
    a + 2 * b + 2 * c < 2 * g ∧
    b + d < g ∧
    2 * b + 2 * e < a + 2 * g ∧
    2 * c < g ∧
    2 * c + 2 * d < a + 2 * g ∧
    c + e < a + g ∧
    6 * c < a + 2 * b + 2 * g ∧
    2 * c + d < a + b + g ∧
    4 * c + 2 * e < 3 * a + 2 * b + 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEG2
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hs : 2 * c < a + 2 * b ∧
      a + 4 * d < 2 * b + 2 * g ∧
      4 * e < a + 2 * b + 2 * g ∧
      2 * g < 5 * a + 2 * b ∧
      a + 2 * b < g) :
    2 * c < a + 2 * b ∧
    a + 4 * d < 2 * b + 2 * g ∧
    d + e < b + g ∧
    d < a + b ∧
    4 * e < a + 2 * b + 2 * g ∧
    2 * e < 3 * a + 2 * b ∧
    2 * g < 5 * a + 2 * b ∧
    a + 2 * b < g ∧
    a + 2 * b + 2 * c < 2 * g ∧
    b + d < g ∧
    2 * b + 2 * e < a + 2 * g ∧
    2 * c < g ∧
    2 * c + 2 * d < a + 2 * g ∧
    c + e < a + g ∧
    6 * c < a + 2 * b + 2 * g ∧
    2 * c + d < a + b + g ∧
    4 * c + 2 * e < 3 * a + 2 * b + 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEG25
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hs : 5 * a + 2 * b = 2 * g ∧
      2 * c < a + 2 * b ∧
      d < a + b ∧
      2 * e < 3 * a + 2 * b) :
    5 * a + 2 * b = 2 * g ∧
    2 * c < a + 2 * b ∧
    a + 4 * d < 2 * b + 2 * g ∧
    d + e < b + g ∧
    d < a + b ∧
    4 * e < a + 2 * b + 2 * g ∧
    2 * e < 3 * a + 2 * b ∧
    a + 2 * b < g ∧
    a + 2 * b + 2 * c < 2 * g ∧
    b + d < g ∧
    2 * b + 2 * e < a + 2 * g ∧
    2 * c < g ∧
    2 * c + 2 * d < a + 2 * g ∧
    c + e < a + g ∧
    6 * c < a + 2 * b + 2 * g ∧
    2 * c + d < a + b + g ∧
    4 * c + 2 * e < 3 * a + 2 * b + 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEG26
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hs : g < 2 * c ∧
      a + 2 * d < 3 * c ∧
      2 * e < 3 * c ∧
      a + 2 * b < 2 * c) :
    a + 2 * b + 2 * g < 6 * c ∧
    g < 2 * c ∧
    a + 2 * d < 3 * c ∧
    a + 2 * d + 2 * e < 6 * c ∧
    2 * d + 2 * g < a + 6 * c ∧
    2 * e < 3 * c ∧
    e + g < a + 3 * c ∧
    2 * g < 2 * a + 3 * c ∧
    a + 2 * b < 2 * c ∧
    a + 2 * b < 2 * c ∧
    a + 4 * b + 2 * d < 6 * c ∧
    2 * b + e < 3 * c ∧
    a + 2 * b < 2 * c ∧
    b + d < 2 * c ∧
    2 * b + 2 * e < a + 4 * c ∧
    2 * d < a + 2 * c ∧
    e < a + c := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEG27
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hs : a + 2 * b < 2 * c ∧
      a + 2 * d < c + g ∧
      2 * e < c + g ∧
      g < 2 * a + c ∧
      2 * c < g) :
    a + 2 * b < 2 * c ∧
    a + 2 * d < c + g ∧
    a + 2 * d + 2 * e < 2 * c + 2 * g ∧
    2 * d < a + 2 * c ∧
    2 * e < c + g ∧
    e < a + c ∧
    g < 2 * a + c ∧
    3 * a + 6 * b < 2 * c + 2 * g ∧
    a + 2 * b < g ∧
    a + 4 * b + 2 * d < 2 * c + 2 * g ∧
    2 * b + e < c + g ∧
    a + 2 * b + 2 * c < 2 * g ∧
    b + d < g ∧
    2 * b + 2 * e < a + 2 * g ∧
    2 * c < g ∧
    2 * c + 2 * d < a + 2 * g ∧
    c + e < a + g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEG28
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hs : g = 2 * c ∧
      a + 2 * d < c + g ∧
      2 * e < c + g ∧
      a + 2 * b + 2 * c < 2 * g) :
    g = 2 * c ∧
    a + 2 * b < 2 * c ∧
    a + 2 * d < c + g ∧
    a + 2 * d + 2 * e < 2 * c + 2 * g ∧
    2 * d < a + 2 * c ∧
    2 * e < c + g ∧
    e < a + c ∧
    g < 2 * a + c ∧
    3 * a + 6 * b < 2 * c + 2 * g ∧
    a + 2 * b < g ∧
    a + 4 * b + 2 * d < 2 * c + 2 * g ∧
    2 * b + e < c + g ∧
    a + 2 * b + 2 * c < 2 * g ∧
    b + d < g ∧
    2 * b + 2 * e < a + 2 * g ∧
    2 * c + 2 * d < a + 2 * g ∧
    c + e < a + g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEG3
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hs : g = a + 2 * b ∧
      a + 4 * d < 2 * b + 2 * g ∧
      4 * e < a + 2 * b + 2 * g ∧
      6 * c < a + 2 * b + 2 * g) :
    g = a + 2 * b ∧
    2 * c < a + 2 * b ∧
    a + 4 * d < 2 * b + 2 * g ∧
    d + e < b + g ∧
    d < a + b ∧
    4 * e < a + 2 * b + 2 * g ∧
    2 * e < 3 * a + 2 * b ∧
    2 * g < 5 * a + 2 * b ∧
    a + 2 * b + 2 * c < 2 * g ∧
    b + d < g ∧
    2 * b + 2 * e < a + 2 * g ∧
    2 * c < g ∧
    2 * c + 2 * d < a + 2 * g ∧
    c + e < a + g ∧
    6 * c < a + 2 * b + 2 * g ∧
    2 * c + d < a + b + g ∧
    4 * c + 2 * e < 3 * a + 2 * b + 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEG38
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hs : 2 * a + c = g ∧
      a + 2 * b < 2 * c ∧
      2 * d < a + 2 * c ∧
      e < a + c) :
    2 * a + c = g ∧
    a + 2 * b < 2 * c ∧
    a + 2 * d < c + g ∧
    a + 2 * d + 2 * e < 2 * c + 2 * g ∧
    2 * d < a + 2 * c ∧
    2 * e < c + g ∧
    e < a + c ∧
    3 * a + 6 * b < 2 * c + 2 * g ∧
    a + 2 * b < g ∧
    a + 4 * b + 2 * d < 2 * c + 2 * g ∧
    2 * b + e < c + g ∧
    a + 2 * b + 2 * c < 2 * g ∧
    b + d < g ∧
    2 * b + 2 * e < a + 2 * g ∧
    2 * c < g ∧
    2 * c + 2 * d < a + 2 * g ∧
    c + e < a + g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEG39
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hs : 2 * b + 2 * g < a + 4 * d ∧
      c + g < a + 2 * d ∧
      2 * e < a + 2 * d ∧
      2 * g < 3 * a + 2 * d ∧
      a + 6 * b < 4 * d ∧
      3 * c < a + 2 * d) :
    2 * b + 2 * g < a + 4 * d ∧
    c + g < a + 2 * d ∧
    2 * e < a + 2 * d ∧
    2 * g < 3 * a + 2 * d ∧
    2 * e < a + 2 * d ∧
    e + g < 2 * a + 2 * d ∧
    2 * g < 3 * a + 2 * d ∧
    a + 6 * b < 4 * d ∧
    2 * b + c < 2 * d ∧
    4 * b < a + 2 * d ∧
    2 * b + e < a + 2 * d ∧
    2 * b + 4 * c < a + 4 * d ∧
    b + c < a + d ∧
    2 * b + 2 * c + 2 * e < 3 * a + 4 * d ∧
    3 * c < a + 2 * d ∧
    4 * c < 3 * a + 2 * d ∧
    2 * c + e < 2 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEG4
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hs : a + 2 * b = 2 * c ∧
      a + 4 * d < 2 * b + 2 * g ∧
      4 * e < a + 2 * b + 2 * g ∧
      2 * g < 5 * a + 2 * b ∧
      6 * c < a + 2 * b + 2 * g) :
    a + 2 * b = 2 * c ∧
    a + 4 * d < 2 * b + 2 * g ∧
    d + e < b + g ∧
    d < a + b ∧
    4 * e < a + 2 * b + 2 * g ∧
    2 * e < 3 * a + 2 * b ∧
    2 * g < 5 * a + 2 * b ∧
    a + 2 * b < g ∧
    a + 2 * b + 2 * c < 2 * g ∧
    b + d < g ∧
    2 * b + 2 * e < a + 2 * g ∧
    2 * c < g ∧
    2 * c + 2 * d < a + 2 * g ∧
    c + e < a + g ∧
    6 * c < a + 2 * b + 2 * g ∧
    2 * c + d < a + b + g ∧
    4 * c + 2 * e < 3 * a + 2 * b + 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEG43
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hs : 3 * a + 2 * d = 2 * g ∧
      2 * a + 2 * d = e + g ∧
      2 * b + 2 * g < a + 4 * d ∧
      c + g < a + 2 * d) :
    a + 2 * d = 2 * e ∧
    3 * a + 2 * d = 2 * g ∧
    a + 2 * d = 2 * e ∧
    2 * a + 2 * d = e + g ∧
    3 * a + 2 * d = 2 * g ∧
    2 * b + 2 * g < a + 4 * d ∧
    c + g < a + 2 * d ∧
    a + 6 * b < 4 * d ∧
    2 * b + c < 2 * d ∧
    4 * b < a + 2 * d ∧
    2 * b + e < a + 2 * d ∧
    2 * b + 4 * c < a + 4 * d ∧
    b + c < a + d ∧
    2 * b + 2 * c + 2 * e < 3 * a + 4 * d ∧
    3 * c < a + 2 * d ∧
    4 * c < 3 * a + 2 * d ∧
    2 * c + e < 2 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEG44
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hs : a + 2 * d = 2 * e ∧
      2 * b + 2 * g < a + 4 * d ∧
      c + g < a + 2 * d ∧
      e + g < 2 * a + 2 * d ∧
      a + 6 * b < 4 * d ∧
      3 * c < a + 2 * d) :
    a + 2 * d = 2 * e ∧
    a + 2 * d = 2 * e ∧
    2 * b + 2 * g < a + 4 * d ∧
    c + g < a + 2 * d ∧
    2 * g < 3 * a + 2 * d ∧
    e + g < 2 * a + 2 * d ∧
    2 * g < 3 * a + 2 * d ∧
    a + 6 * b < 4 * d ∧
    2 * b + c < 2 * d ∧
    4 * b < a + 2 * d ∧
    2 * b + e < a + 2 * d ∧
    2 * b + 4 * c < a + 4 * d ∧
    b + c < a + d ∧
    2 * b + 2 * c + 2 * e < 3 * a + 4 * d ∧
    3 * c < a + 2 * d ∧
    4 * c < 3 * a + 2 * d ∧
    2 * c + e < 2 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEG48
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hs : 3 * a + 2 * d = 2 * g ∧
      2 * b + 2 * g < a + 4 * d ∧
      c + g < a + 2 * d ∧
      e + g < 2 * a + 2 * d) :
    3 * a + 2 * d = 2 * g ∧
    3 * a + 2 * d = 2 * g ∧
    2 * b + 2 * g < a + 4 * d ∧
    c + g < a + 2 * d ∧
    2 * e < a + 2 * d ∧
    2 * e < a + 2 * d ∧
    e + g < 2 * a + 2 * d ∧
    a + 6 * b < 4 * d ∧
    2 * b + c < 2 * d ∧
    4 * b < a + 2 * d ∧
    2 * b + e < a + 2 * d ∧
    2 * b + 4 * c < a + 4 * d ∧
    b + c < a + d ∧
    2 * b + 2 * c + 2 * e < 3 * a + 4 * d ∧
    3 * c < a + 2 * d ∧
    4 * c < 3 * a + 2 * d ∧
    2 * c + e < 2 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEG49
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hs : a + 2 * b + 2 * g < 4 * e ∧
      c + g < 2 * e ∧
      a + 2 * d < 2 * e ∧
      g < a + e ∧
      3 * a + 6 * b < 4 * e ∧
      3 * c < 2 * e) :
    a + 2 * b + 2 * g < 4 * e ∧
    c + g < 2 * e ∧
    a + 2 * d < 2 * e ∧
    a + 2 * d < 2 * e ∧
    2 * d + 2 * g < a + 4 * e ∧
    g < a + e ∧
    g < a + e ∧
    3 * a + 6 * b < 4 * e ∧
    a + 2 * b + c < 2 * e ∧
    a + 4 * b + 2 * d < 4 * e ∧
    2 * b < e ∧
    a + 2 * b + 4 * c < 4 * e ∧
    b + c + d < 2 * e ∧
    2 * b + 2 * c < a + 2 * e ∧
    3 * c < 2 * e ∧
    4 * c + 2 * d < a + 4 * e ∧
    2 * c < a + e := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEG5
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hs : g = 2 * c ∧
      a + 2 * b + 2 * g = 6 * c ∧
      a + 4 * d < 2 * b + 2 * g ∧
      4 * e < a + 2 * b + 2 * g) :
    a + 2 * b = 2 * c ∧
    g = a + 2 * b ∧
    2 * g = a + 2 * b + 2 * c ∧
    g = 2 * c ∧
    a + 2 * b + 2 * g = 6 * c ∧
    a + 4 * d < 2 * b + 2 * g ∧
    d + e < b + g ∧
    d < a + b ∧
    4 * e < a + 2 * b + 2 * g ∧
    2 * e < 3 * a + 2 * b ∧
    2 * g < 5 * a + 2 * b ∧
    b + d < g ∧
    2 * b + 2 * e < a + 2 * g ∧
    2 * c + 2 * d < a + 2 * g ∧
    c + e < a + g ∧
    2 * c + d < a + b + g ∧
    4 * c + 2 * e < 3 * a + 2 * b + 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEG53
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hs : a + e = g ∧
      a + 2 * b + 2 * g < 4 * e ∧
      c + g < 2 * e ∧
      2 * d + 2 * g < a + 4 * e) :
    a + e = g ∧
    a + e = g ∧
    a + 2 * b + 2 * g < 4 * e ∧
    c + g < 2 * e ∧
    a + 2 * d < 2 * e ∧
    a + 2 * d < 2 * e ∧
    2 * d + 2 * g < a + 4 * e ∧
    3 * a + 6 * b < 4 * e ∧
    a + 2 * b + c < 2 * e ∧
    a + 4 * b + 2 * d < 4 * e ∧
    2 * b < e ∧
    a + 2 * b + 4 * c < 4 * e ∧
    b + c + d < 2 * e ∧
    2 * b + 2 * c < a + 2 * e ∧
    3 * c < 2 * e ∧
    4 * c + 2 * d < a + 4 * e ∧
    2 * c < a + e := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEG54
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hs : 5 * a + 2 * b < 2 * g ∧
      2 * a + c < g ∧
      3 * a + 2 * d < 2 * g ∧
      a + e < g) :
    5 * a + 2 * b < 2 * g ∧
    2 * a + c < g ∧
    3 * a + 2 * d < 2 * g ∧
    5 * a + 2 * d + 2 * e < 4 * g ∧
    3 * a + 2 * d < 2 * g ∧
    a + e < g ∧
    a + e < g ∧
    7 * a + 6 * b < 4 * g ∧
    3 * a + 2 * b + c < 2 * g ∧
    5 * a + 4 * b + 2 * d < 4 * g ∧
    2 * a + 2 * b + e < 2 * g ∧
    5 * a + 2 * b + 4 * c < 4 * g ∧
    2 * a + b + c + d < 2 * g ∧
    3 * a + 2 * b + 2 * c + 2 * e < 4 * g ∧
    2 * a + 3 * c < 2 * g ∧
    3 * a + 4 * c + 2 * d < 4 * g ∧
    a + 2 * c + e < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BCDEG`. -/
theorem quarticChamberSupport810_of_live_BCDEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFz : F = 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG39 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG39 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG40 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG16 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG17 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG39 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG39 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG39 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG39 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG21 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG48 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG48 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG25 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
    · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG44 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG44 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG45 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG19 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG20 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG44 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG44 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG44 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG44 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG18 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG43 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG43 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG25 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
    · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht2a | ht2b | ht2c
      · -- G.natDegree < A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG49 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG49 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG50 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG22 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG23 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG49 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG49 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG49 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG49 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
      · -- G.natDegree = A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG24 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG53 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
      · -- G.natDegree > A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG25 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG39 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG39 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG41 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG6 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG7 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG5 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG39 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG39 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG39 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG39 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG5 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG11 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG48 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG48 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG15 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG15 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG5 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
    · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG44 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG44 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG46 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG9 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG10 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG5 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG44 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG44 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG44 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG44 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG5 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG8 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG43 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG43 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG15 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG15 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG5 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
    · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht2a | ht2b | ht2c
      · -- G.natDegree < A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG49 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG49 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG51 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG12 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG13 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG5 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG49 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG49 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG49 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG49 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
      · -- G.natDegree = A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG5 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG14 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG53 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
      · -- G.natDegree > A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG15 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG15 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG5 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG39 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG39 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG42 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG29 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG30 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG27 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG28 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG28 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG39 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG39 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG39 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG39 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG27 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG28 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG28 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG34 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG48 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG48 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG38 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG27 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG28 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG28 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
    · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG44 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG44 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG47 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG32 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG33 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG27 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG28 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG28 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG44 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG44 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG44 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG44 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG27 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG28 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG28 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG31 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG43 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG43 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG38 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG27 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG28 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG28 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
    · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht2a | ht2b | ht2c
      · -- G.natDegree < A.natDegree + E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG49 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG49 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG52 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- C.natDegree + G.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG35 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG36 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- C.natDegree + G.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG27 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG28 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG28 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG49 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG49 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG49 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG49 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
      · -- G.natDegree = A.natDegree + E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG27 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG28 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG28 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG37 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG53 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
      · -- G.natDegree > A.natDegree + E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG38 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG27 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG27 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG28 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG28 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG26 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDEG54 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailBCDEG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn (by omega)⟩)
end QuarticChamberExhaust810

end Max11DegreeRoutes
