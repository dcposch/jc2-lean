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
private theorem astra4zExhaustTailBCDFG0
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : 2 * f < a + 4 * b ∧
      g < a + 2 * b ∧
      4 * d < a + 6 * b ∧
      2 * c < a + 2 * b) :
    2 * f < a + 4 * b ∧
    g < a + 2 * b ∧
    c + f < a + 3 * b ∧
    2 * c + 2 * g < 3 * a + 6 * b ∧
    4 * d < a + 6 * b ∧
    2 * d + 2 * f < 3 * a + 6 * b ∧
    d + g < 2 * a + 3 * b ∧
    4 * f < 5 * a + 6 * b ∧
    f + g < 3 * a + 3 * b ∧
    4 * g < 7 * a + 6 * b ∧
    2 * c < a + 2 * b ∧
    d < a + b ∧
    2 * c < a + 2 * b ∧
    2 * c + 2 * d < 3 * a + 4 * b ∧
    2 * c < a + 2 * b ∧
    2 * c + d < 2 * a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG1
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : a + 2 * b = 2 * c ∧
      c + f < a + 3 * b ∧
      2 * c + 2 * g < 3 * a + 6 * b ∧
      4 * d < a + 6 * b) :
    a + 2 * b = 2 * c ∧
    a + 2 * b = 2 * c ∧
    a + 2 * b = 2 * c ∧
    2 * f < a + 4 * b ∧
    g < a + 2 * b ∧
    c + f < a + 3 * b ∧
    2 * c + 2 * g < 3 * a + 6 * b ∧
    4 * d < a + 6 * b ∧
    2 * d + 2 * f < 3 * a + 6 * b ∧
    d + g < 2 * a + 3 * b ∧
    4 * f < 5 * a + 6 * b ∧
    f + g < 3 * a + 3 * b ∧
    4 * g < 7 * a + 6 * b ∧
    d < a + b ∧
    2 * c + 2 * d < 3 * a + 4 * b ∧
    2 * c + d < 2 * a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG16
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : a + 2 * b = 2 * c ∧
      c + g < a + b + f ∧
      2 * d < b + f ∧
      f < 2 * a + b ∧
      3 * c < a + b + f) :
    a + 2 * b = 2 * c ∧
    2 * g < a + 2 * f ∧
    c + g < a + b + f ∧
    2 * d < b + f ∧
    d < a + b ∧
    2 * d + 2 * g < 3 * a + 2 * b + 2 * f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    a + 4 * b < 2 * f ∧
    b + c < f ∧
    2 * b + 2 * d < a + 2 * f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f ∧
    3 * c < a + b + f ∧
    4 * c + 2 * d < 3 * a + 2 * b + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG17
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : a + 2 * f = 4 * c ∧
      a + b + f = 3 * c ∧
      c + g < a + b + f ∧
      2 * d < b + f) :
    a + 2 * b = 2 * c ∧
    2 * f = a + 4 * b ∧
    f = b + c ∧
    a + 2 * f = 4 * c ∧
    a + b + f = 3 * c ∧
    2 * g < a + 2 * f ∧
    c + g < a + b + f ∧
    2 * d < b + f ∧
    d < a + b ∧
    2 * d + 2 * g < 3 * a + 2 * b + 2 * f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    2 * b + 2 * d < a + 2 * f ∧
    c + d < a + f ∧
    4 * c + 2 * d < 3 * a + 2 * b + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG2
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : 2 * g < a + 2 * f ∧
      2 * c < a + 2 * b ∧
      2 * d < b + f ∧
      f < 2 * a + b ∧
      a + 4 * b < 2 * f) :
    2 * g < a + 2 * f ∧
    2 * c < a + 2 * b ∧
    c + g < a + b + f ∧
    2 * d < b + f ∧
    d < a + b ∧
    2 * d + 2 * g < 3 * a + 2 * b + 2 * f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    a + 4 * b < 2 * f ∧
    b + c < f ∧
    2 * b + 2 * d < a + 2 * f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f ∧
    3 * c < a + b + f ∧
    4 * c + 2 * d < 3 * a + 2 * b + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG26
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : a + 2 * f < 2 * g ∧
      2 * c < a + 2 * b ∧
      a + 4 * d < 2 * b + 2 * g ∧
      2 * g < 5 * a + 2 * b ∧
      a + 2 * b < g) :
    a + 2 * f < 2 * g ∧
    c + f < b + g ∧
    2 * c < a + 2 * b ∧
    a + 4 * d < 2 * b + 2 * g ∧
    2 * d + 2 * f < a + 2 * b + 2 * g ∧
    d < a + b ∧
    4 * f < 3 * a + 2 * b + 2 * g ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    a + 2 * b < g ∧
    a + 2 * b + 2 * c < 2 * g ∧
    b + d < g ∧
    2 * c < g ∧
    2 * c + 2 * d < a + 2 * g ∧
    6 * c < a + 2 * b + 2 * g ∧
    2 * c + d < a + b + g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG27
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : g = a + 2 * b ∧
      a + 2 * f < 2 * g ∧
      a + 4 * d < 2 * b + 2 * g ∧
      6 * c < a + 2 * b + 2 * g) :
    g = a + 2 * b ∧
    a + 2 * f < 2 * g ∧
    c + f < b + g ∧
    2 * c < a + 2 * b ∧
    a + 4 * d < 2 * b + 2 * g ∧
    2 * d + 2 * f < a + 2 * b + 2 * g ∧
    d < a + b ∧
    4 * f < 3 * a + 2 * b + 2 * g ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    a + 2 * b + 2 * c < 2 * g ∧
    b + d < g ∧
    2 * c < g ∧
    2 * c + 2 * d < a + 2 * g ∧
    6 * c < a + 2 * b + 2 * g ∧
    2 * c + d < a + b + g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG28
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : a + 2 * b = 2 * c ∧
      c + f < b + g ∧
      a + 4 * d < 2 * b + 2 * g ∧
      2 * g < 5 * a + 2 * b ∧
      6 * c < a + 2 * b + 2 * g) :
    a + 2 * b = 2 * c ∧
    a + 2 * f < 2 * g ∧
    c + f < b + g ∧
    a + 4 * d < 2 * b + 2 * g ∧
    2 * d + 2 * f < a + 2 * b + 2 * g ∧
    d < a + b ∧
    4 * f < 3 * a + 2 * b + 2 * g ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    a + 2 * b < g ∧
    a + 2 * b + 2 * c < 2 * g ∧
    b + d < g ∧
    2 * c < g ∧
    2 * c + 2 * d < a + 2 * g ∧
    6 * c < a + 2 * b + 2 * g ∧
    2 * c + d < a + b + g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG29
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : g = 2 * c ∧
      a + 2 * b + 2 * g = 6 * c ∧
      c + f < b + g ∧
      a + 4 * d < 2 * b + 2 * g) :
    a + 2 * b = 2 * c ∧
    g = a + 2 * b ∧
    2 * g = a + 2 * b + 2 * c ∧
    g = 2 * c ∧
    a + 2 * b + 2 * g = 6 * c ∧
    a + 2 * f < 2 * g ∧
    c + f < b + g ∧
    a + 4 * d < 2 * b + 2 * g ∧
    2 * d + 2 * f < a + 2 * b + 2 * g ∧
    d < a + b ∧
    4 * f < 3 * a + 2 * b + 2 * g ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    b + d < g ∧
    2 * c + 2 * d < a + 2 * g ∧
    2 * c + d < a + b + g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG3
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : 2 * f = a + 4 * b ∧
      2 * g < a + 2 * f ∧
      2 * d < b + f ∧
      3 * c < a + b + f) :
    2 * f = a + 4 * b ∧
    2 * g < a + 2 * f ∧
    2 * c < a + 2 * b ∧
    c + g < a + b + f ∧
    2 * d < b + f ∧
    d < a + b ∧
    2 * d + 2 * g < 3 * a + 2 * b + 2 * f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    b + c < f ∧
    2 * b + 2 * d < a + 2 * f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f ∧
    3 * c < a + b + f ∧
    4 * c + 2 * d < 3 * a + 2 * b + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG38
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : a + 2 * f < 4 * c ∧
      g < 2 * c ∧
      a + 2 * d < 3 * c ∧
      a + 2 * b < 2 * c) :
    a + b + f < 3 * c ∧
    a + 2 * b + 2 * g < 6 * c ∧
    a + 2 * f < 4 * c ∧
    g < 2 * c ∧
    a + 2 * d < 3 * c ∧
    d + f < 3 * c ∧
    2 * d + 2 * g < a + 6 * c ∧
    2 * f < a + 3 * c ∧
    2 * f + 2 * g < 3 * a + 6 * c ∧
    2 * g < 2 * a + 3 * c ∧
    a + 2 * b < 2 * c ∧
    a + 2 * b < 2 * c ∧
    a + 4 * b + 2 * d < 6 * c ∧
    a + 2 * b < 2 * c ∧
    b + d < 2 * c ∧
    2 * d < a + 2 * c := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG39
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : a + 2 * b < 2 * c ∧
      2 * g < a + 2 * f ∧
      a + 4 * d < 2 * c + 2 * f ∧
      2 * f < 3 * a + 2 * c ∧
      4 * c < a + 2 * f) :
    a + 2 * b < 2 * c ∧
    b + g < c + f ∧
    2 * g < a + 2 * f ∧
    a + 4 * d < 2 * c + 2 * f ∧
    2 * d < a + 2 * c ∧
    d + g < a + c + f ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    4 * g < 5 * a + 2 * c + 2 * f ∧
    a + 3 * b < c + f ∧
    a + 4 * b < 2 * f ∧
    2 * b + d < c + f ∧
    b + c < f ∧
    2 * b + 2 * d < a + 2 * f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG4
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : a + 2 * f = 2 * g ∧
      c + g < a + b + f ∧
      2 * d < b + f ∧
      2 * g < 3 * a + b + f ∧
      a + 4 * b < 2 * f) :
    a + 2 * f = 2 * g ∧
    2 * c < a + 2 * b ∧
    c + g < a + b + f ∧
    2 * d < b + f ∧
    d < a + b ∧
    2 * d + 2 * g < 3 * a + 2 * b + 2 * f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    a + 4 * b < 2 * f ∧
    b + c < f ∧
    2 * b + 2 * d < a + 2 * f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f ∧
    3 * c < a + b + f ∧
    4 * c + 2 * d < 3 * a + 2 * b + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG40
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : a + 2 * f = 4 * c ∧
      2 * g < a + 2 * f ∧
      a + 4 * d < 2 * c + 2 * f ∧
      b + c < f) :
    a + 2 * f = 4 * c ∧
    a + 2 * b < 2 * c ∧
    b + g < c + f ∧
    2 * g < a + 2 * f ∧
    a + 4 * d < 2 * c + 2 * f ∧
    2 * d < a + 2 * c ∧
    d + g < a + c + f ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    4 * g < 5 * a + 2 * c + 2 * f ∧
    a + 3 * b < c + f ∧
    a + 4 * b < 2 * f ∧
    2 * b + d < c + f ∧
    b + c < f ∧
    2 * b + 2 * d < a + 2 * f ∧
    c + d < a + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG41
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : a + 2 * f = 2 * g ∧
      b + g < c + f ∧
      a + 4 * d < 2 * c + 2 * f ∧
      4 * g < 5 * a + 2 * c + 2 * f ∧
      4 * c < a + 2 * f) :
    a + 2 * f = 2 * g ∧
    a + 2 * b < 2 * c ∧
    b + g < c + f ∧
    a + 4 * d < 2 * c + 2 * f ∧
    2 * d < a + 2 * c ∧
    d + g < a + c + f ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    4 * g < 5 * a + 2 * c + 2 * f ∧
    a + 3 * b < c + f ∧
    a + 4 * b < 2 * f ∧
    2 * b + d < c + f ∧
    b + c < f ∧
    2 * b + 2 * d < a + 2 * f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG42
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : a + 2 * f = 2 * g ∧
      a + 2 * f = 4 * c ∧
      a + 4 * d < 2 * c + 2 * f ∧
      b + c < f) :
    a + 2 * f = 2 * g ∧
    a + 2 * f = 4 * c ∧
    a + 2 * b < 2 * c ∧
    b + g < c + f ∧
    a + 4 * d < 2 * c + 2 * f ∧
    2 * d < a + 2 * c ∧
    d + g < a + c + f ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    4 * g < 5 * a + 2 * c + 2 * f ∧
    a + 3 * b < c + f ∧
    a + 4 * b < 2 * f ∧
    2 * b + d < c + f ∧
    b + c < f ∧
    2 * b + 2 * d < a + 2 * f ∧
    c + d < a + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG5
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : a + 2 * f = 2 * g ∧
      2 * f = a + 4 * b ∧
      2 * d < b + f ∧
      3 * c < a + b + f) :
    a + 2 * f = 2 * g ∧
    2 * f = a + 4 * b ∧
    2 * c < a + 2 * b ∧
    c + g < a + b + f ∧
    2 * d < b + f ∧
    d < a + b ∧
    2 * d + 2 * g < 3 * a + 2 * b + 2 * f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    b + c < f ∧
    2 * b + 2 * d < a + 2 * f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f ∧
    3 * c < a + b + f ∧
    4 * c + 2 * d < 3 * a + 2 * b + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG51
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : a + 2 * b < 2 * c ∧
      a + 2 * f < 2 * g ∧
      a + 2 * d < c + g ∧
      g < 2 * a + c ∧
      2 * c < g) :
    a + b + f < c + g ∧
    a + 2 * b < 2 * c ∧
    a + 2 * f < 2 * g ∧
    a + 2 * d < c + g ∧
    d + f < c + g ∧
    2 * d < a + 2 * c ∧
    2 * f < a + c + g ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    3 * a + 6 * b < 2 * c + 2 * g ∧
    a + 2 * b < g ∧
    a + 4 * b + 2 * d < 2 * c + 2 * g ∧
    a + 2 * b + 2 * c < 2 * g ∧
    b + d < g ∧
    2 * c < g ∧
    2 * c + 2 * d < a + 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG52
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : g = 2 * c ∧
      a + 2 * f < 2 * g ∧
      a + 2 * d < c + g ∧
      a + 2 * b + 2 * c < 2 * g) :
    g = 2 * c ∧
    a + b + f < c + g ∧
    a + 2 * b < 2 * c ∧
    a + 2 * f < 2 * g ∧
    a + 2 * d < c + g ∧
    d + f < c + g ∧
    2 * d < a + 2 * c ∧
    2 * f < a + c + g ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    3 * a + 6 * b < 2 * c + 2 * g ∧
    a + 2 * b < g ∧
    a + 4 * b + 2 * d < 2 * c + 2 * g ∧
    a + 2 * b + 2 * c < 2 * g ∧
    b + d < g ∧
    2 * c + 2 * d < a + 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG57
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : b + f < 2 * d ∧
      2 * b + 2 * g < a + 4 * d ∧
      2 * c + 2 * f < a + 4 * d ∧
      c + g < a + 2 * d ∧
      f < a + d ∧
      2 * g < 3 * a + 2 * d ∧
      a + 6 * b < 4 * d ∧
      3 * c < a + 2 * d) :
    b + f < 2 * d ∧
    2 * b + 2 * g < a + 4 * d ∧
    2 * c + 2 * f < a + 4 * d ∧
    c + g < a + 2 * d ∧
    f < a + d ∧
    2 * g < 3 * a + 2 * d ∧
    f < a + d ∧
    2 * f + 2 * g < 5 * a + 4 * d ∧
    2 * g < 3 * a + 2 * d ∧
    a + 6 * b < 4 * d ∧
    2 * b + c < 2 * d ∧
    4 * b < a + 2 * d ∧
    2 * b + 4 * c < a + 4 * d ∧
    b + c < a + d ∧
    3 * c < a + 2 * d ∧
    4 * c < 3 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG58
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : 4 * d = a + 6 * b ∧
      b + f < 2 * d ∧
      2 * b + 2 * g < a + 4 * d ∧
      3 * c < a + 2 * d) :
    4 * d = a + 6 * b ∧
    b + f < 2 * d ∧
    2 * b + 2 * g < a + 4 * d ∧
    2 * c + 2 * f < a + 4 * d ∧
    c + g < a + 2 * d ∧
    f < a + d ∧
    2 * g < 3 * a + 2 * d ∧
    f < a + d ∧
    2 * f + 2 * g < 5 * a + 4 * d ∧
    2 * g < 3 * a + 2 * d ∧
    2 * b + c < 2 * d ∧
    4 * b < a + 2 * d ∧
    2 * b + 4 * c < a + 4 * d ∧
    b + c < a + d ∧
    3 * c < a + 2 * d ∧
    4 * c < 3 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG59
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : a + 4 * d = 2 * b + 4 * c ∧
      a + 2 * d = 3 * c ∧
      2 * c + 2 * f < a + 4 * d ∧
      c + g < a + 2 * d) :
    4 * d = a + 6 * b ∧
    2 * d = 2 * b + c ∧
    a + 4 * d = 2 * b + 4 * c ∧
    a + 2 * d = 3 * c ∧
    b + f < 2 * d ∧
    2 * b + 2 * g < a + 4 * d ∧
    2 * c + 2 * f < a + 4 * d ∧
    c + g < a + 2 * d ∧
    f < a + d ∧
    2 * g < 3 * a + 2 * d ∧
    f < a + d ∧
    2 * f + 2 * g < 5 * a + 4 * d ∧
    2 * g < 3 * a + 2 * d ∧
    4 * b < a + 2 * d ∧
    b + c < a + d ∧
    4 * c < 3 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG6
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : a + 2 * b = 2 * c ∧
      a + b + f = c + g ∧
      2 * d < b + f ∧
      2 * g < 3 * a + b + f ∧
      3 * c < a + b + f) :
    a + 2 * f = 2 * g ∧
    a + 2 * b = 2 * c ∧
    a + b + f = c + g ∧
    2 * d < b + f ∧
    d < a + b ∧
    2 * d + 2 * g < 3 * a + 2 * b + 2 * f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    a + 4 * b < 2 * f ∧
    b + c < f ∧
    2 * b + 2 * d < a + 2 * f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f ∧
    3 * c < a + b + f ∧
    4 * c + 2 * d < 3 * a + 2 * b + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG60
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : a + 2 * d = 3 * c ∧
      2 * c + 2 * f < a + 4 * d ∧
      c + g < a + 2 * d ∧
      2 * b + 4 * c < a + 4 * d) :
    a + 2 * d = 3 * c ∧
    b + f < 2 * d ∧
    2 * b + 2 * g < a + 4 * d ∧
    2 * c + 2 * f < a + 4 * d ∧
    c + g < a + 2 * d ∧
    f < a + d ∧
    2 * g < 3 * a + 2 * d ∧
    f < a + d ∧
    2 * f + 2 * g < 5 * a + 4 * d ∧
    2 * g < 3 * a + 2 * d ∧
    a + 6 * b < 4 * d ∧
    2 * b + c < 2 * d ∧
    4 * b < a + 2 * d ∧
    2 * b + 4 * c < a + 4 * d ∧
    b + c < a + d ∧
    4 * c < 3 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG61
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : 3 * a + 2 * d = 2 * g ∧
      5 * a + 4 * d = 2 * f + 2 * g ∧
      2 * b + 2 * g < a + 4 * d ∧
      c + g < a + 2 * d) :
    a + d = f ∧
    3 * a + 2 * d = 2 * g ∧
    a + d = f ∧
    5 * a + 4 * d = 2 * f + 2 * g ∧
    3 * a + 2 * d = 2 * g ∧
    b + f < 2 * d ∧
    2 * b + 2 * g < a + 4 * d ∧
    2 * c + 2 * f < a + 4 * d ∧
    c + g < a + 2 * d ∧
    a + 6 * b < 4 * d ∧
    2 * b + c < 2 * d ∧
    4 * b < a + 2 * d ∧
    2 * b + 4 * c < a + 4 * d ∧
    b + c < a + d ∧
    3 * c < a + 2 * d ∧
    4 * c < 3 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG62
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : a + d = f ∧
      b + f < 2 * d ∧
      2 * c + 2 * f < a + 4 * d ∧
      2 * f + 2 * g < 5 * a + 4 * d) :
    a + d = f ∧
    a + d = f ∧
    b + f < 2 * d ∧
    2 * b + 2 * g < a + 4 * d ∧
    2 * c + 2 * f < a + 4 * d ∧
    c + g < a + 2 * d ∧
    2 * g < 3 * a + 2 * d ∧
    2 * f + 2 * g < 5 * a + 4 * d ∧
    2 * g < 3 * a + 2 * d ∧
    a + 6 * b < 4 * d ∧
    2 * b + c < 2 * d ∧
    4 * b < a + 2 * d ∧
    2 * b + 4 * c < a + 4 * d ∧
    b + c < a + d ∧
    3 * c < a + 2 * d ∧
    4 * c < 3 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG63
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : 3 * a + 2 * d = 2 * g ∧
      2 * b + 2 * g < a + 4 * d ∧
      c + g < a + 2 * d ∧
      2 * f + 2 * g < 5 * a + 4 * d) :
    3 * a + 2 * d = 2 * g ∧
    3 * a + 2 * d = 2 * g ∧
    b + f < 2 * d ∧
    2 * b + 2 * g < a + 4 * d ∧
    2 * c + 2 * f < a + 4 * d ∧
    c + g < a + 2 * d ∧
    f < a + d ∧
    f < a + d ∧
    2 * f + 2 * g < 5 * a + 4 * d ∧
    a + 6 * b < 4 * d ∧
    2 * b + c < 2 * d ∧
    4 * b < a + 2 * d ∧
    2 * b + 4 * c < a + 4 * d ∧
    b + c < a + d ∧
    3 * c < a + 2 * d ∧
    4 * c < 3 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG64
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : 2 * a + b < f ∧
      3 * a + 2 * c < 2 * f ∧
      a + d < f ∧
      2 * g < a + 2 * f) :
    2 * a + b < f ∧
    3 * a + 2 * b + 2 * g < 4 * f ∧
    3 * a + 2 * c < 2 * f ∧
    a + c + g < 2 * f ∧
    a + d < f ∧
    a + d < f ∧
    a + 2 * d + 2 * g < 4 * f ∧
    2 * g < a + 2 * f ∧
    2 * g < a + 2 * f ∧
    5 * a + 6 * b < 4 * f ∧
    2 * a + 2 * b + c < 2 * f ∧
    3 * a + 4 * b + 2 * d < 4 * f ∧
    3 * a + 2 * b + 4 * c < 4 * f ∧
    a + b + c + d < 2 * f ∧
    a + 3 * c < 2 * f ∧
    a + 4 * c + 2 * d < 4 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG65
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : a + 2 * f = 2 * g ∧
      3 * a + 2 * b + 2 * g < 4 * f ∧
      a + c + g < 2 * f ∧
      a + 2 * d + 2 * g < 4 * f) :
    a + 2 * f = 2 * g ∧
    a + 2 * f = 2 * g ∧
    2 * a + b < f ∧
    3 * a + 2 * b + 2 * g < 4 * f ∧
    3 * a + 2 * c < 2 * f ∧
    a + c + g < 2 * f ∧
    a + d < f ∧
    a + d < f ∧
    a + 2 * d + 2 * g < 4 * f ∧
    5 * a + 6 * b < 4 * f ∧
    2 * a + 2 * b + c < 2 * f ∧
    3 * a + 4 * b + 2 * d < 4 * f ∧
    3 * a + 2 * b + 4 * c < 4 * f ∧
    a + b + c + d < 2 * f ∧
    a + 3 * c < 2 * f ∧
    a + 4 * c + 2 * d < 4 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG66
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : 5 * a + 2 * b < 2 * g ∧
      2 * a + c < g ∧
      3 * a + 2 * d < 2 * g ∧
      a + 2 * f < 2 * g) :
    3 * a + b + f < 2 * g ∧
    5 * a + 2 * b < 2 * g ∧
    5 * a + 2 * c + 2 * f < 4 * g ∧
    2 * a + c < g ∧
    3 * a + 2 * d < 2 * g ∧
    2 * a + d + f < 2 * g ∧
    3 * a + 2 * d < 2 * g ∧
    a + 2 * f < 2 * g ∧
    a + 2 * f < 2 * g ∧
    7 * a + 6 * b < 4 * g ∧
    3 * a + 2 * b + c < 2 * g ∧
    5 * a + 4 * b + 2 * d < 4 * g ∧
    5 * a + 2 * b + 4 * c < 4 * g ∧
    2 * a + b + c + d < 2 * g ∧
    2 * a + 3 * c < 2 * g ∧
    3 * a + 4 * c + 2 * d < 4 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDFG7
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hs : a + b + f = c + g ∧
      a + 2 * f = 4 * c ∧
      a + b + f = 3 * c ∧
      2 * d < b + f) :
    a + 2 * f = 2 * g ∧
    a + 2 * b = 2 * c ∧
    a + b + f = c + g ∧
    2 * f = a + 4 * b ∧
    f = b + c ∧
    a + 2 * f = 4 * c ∧
    a + b + f = 3 * c ∧
    2 * d < b + f ∧
    d < a + b ∧
    2 * d + 2 * g < 3 * a + 2 * b + 2 * f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    2 * b + 2 * d < a + 2 * f ∧
    c + d < a + f ∧
    4 * c + 2 * d < 3 * a + 2 * b + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BCDFG`. -/
theorem quarticChamberSupport810_of_live_BCDFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEz : E = 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG58 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG58 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG22 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG23 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG2 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG3 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG2 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG3 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG24 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG62 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG62 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG64 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG64 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG25 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG2 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG3 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG64 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG64 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG64 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG64 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG58 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG58 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG12 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG13 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG4 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG5 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG4 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG5 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG14 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG61 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG61 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG65 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG65 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG15 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG4 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG5 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG65 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG65 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG65 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG65 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG58 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG58 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG34 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG35 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG27 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG27 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG27 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG27 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG36 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG63 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG63 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG66 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG66 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG37 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG27 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG27 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG66 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG66 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG66 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG66 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG59 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG59 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG18 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG19 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG16 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG17 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG17 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG16 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG17 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG17 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG20 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG62 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG62 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG64 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG64 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG21 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG16 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG17 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG17 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG64 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG64 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG64 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG64 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG59 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG59 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG8 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG9 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG6 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG6 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG7 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG7 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG6 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG6 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG7 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG7 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG10 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG61 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG61 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG65 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG65 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG11 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG6 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG6 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG7 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG7 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG65 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG65 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG65 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG65 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG59 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG59 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG30 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG31 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG28 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG28 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG29 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG29 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG28 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG28 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG29 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG29 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG32 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG63 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG63 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG66 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG66 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG33 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG28 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG28 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG29 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG29 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG66 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG66 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG66 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG66 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG60 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG60 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG47 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG48 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG39 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG39 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG40 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG40 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG39 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG39 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG40 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG40 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG49 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG62 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG62 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG64 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG64 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG50 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG39 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG39 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG40 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG40 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG64 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG64 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG64 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG64 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG60 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG60 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG43 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG44 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG41 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG41 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG42 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG42 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG41 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG41 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG42 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG42 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG45 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG61 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG61 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG65 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG65 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG46 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG41 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG41 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG42 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG42 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG65 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG65 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG65 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG65 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG60 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG60 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG53 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG54 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG51 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG51 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG52 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG57 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG51 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG51 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG52 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG55 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG63 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG63 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG66 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG66 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG56 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG51 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG51 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG52 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG38 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG66 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG66 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCDFG66 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailBCDFG66 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn (by omega)⟩)
end QuarticChamberExhaust810

end Max11DegreeRoutes
