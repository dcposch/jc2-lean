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
private theorem astra4zExhaustTailBCEFG0
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : 2 * f < a + 4 * b ∧
      g < a + 2 * b ∧
      4 * e < 3 * a + 6 * b ∧
      2 * c < a + 2 * b) :
    2 * f < a + 4 * b ∧
    g < a + 2 * b ∧
    c + f < a + 3 * b ∧
    2 * c + 2 * g < 3 * a + 6 * b ∧
    4 * e < 3 * a + 6 * b ∧
    e + f < 2 * a + 3 * b ∧
    2 * e + 2 * g < 5 * a + 6 * b ∧
    4 * f < 5 * a + 6 * b ∧
    f + g < 3 * a + 3 * b ∧
    4 * g < 7 * a + 6 * b ∧
    2 * c < a + 2 * b ∧
    2 * e < 3 * a + 2 * b ∧
    2 * c < a + 2 * b ∧
    c + e < 2 * a + 2 * b ∧
    2 * c < a + 2 * b ∧
    4 * c + 2 * e < 5 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG1
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : a + 2 * b = 2 * c ∧
      c + f < a + 3 * b ∧
      2 * c + 2 * g < 3 * a + 6 * b ∧
      4 * e < 3 * a + 6 * b) :
    a + 2 * b = 2 * c ∧
    a + 2 * b = 2 * c ∧
    a + 2 * b = 2 * c ∧
    2 * f < a + 4 * b ∧
    g < a + 2 * b ∧
    c + f < a + 3 * b ∧
    2 * c + 2 * g < 3 * a + 6 * b ∧
    4 * e < 3 * a + 6 * b ∧
    e + f < 2 * a + 3 * b ∧
    2 * e + 2 * g < 5 * a + 6 * b ∧
    4 * f < 5 * a + 6 * b ∧
    f + g < 3 * a + 3 * b ∧
    4 * g < 7 * a + 6 * b ∧
    2 * e < 3 * a + 2 * b ∧
    c + e < 2 * a + 2 * b ∧
    4 * c + 2 * e < 5 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG16
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : a + 2 * b = 2 * c ∧
      c + g < a + b + f ∧
      2 * e < a + b + f ∧
      f < 2 * a + b ∧
      3 * c < a + b + f) :
    a + 2 * b = 2 * c ∧
    2 * g < a + 2 * f ∧
    c + g < a + b + f ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    e + g < 2 * a + b + f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    a + 4 * b < 2 * f ∧
    b + c < f ∧
    b + e < a + f ∧
    4 * c < a + 2 * f ∧
    2 * c + 2 * e < 3 * a + 2 * f ∧
    3 * c < a + b + f ∧
    2 * c + e < 2 * a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG17
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : a + 2 * f = 4 * c ∧
      a + b + f = 3 * c ∧
      c + g < a + b + f ∧
      2 * e < a + b + f) :
    a + 2 * b = 2 * c ∧
    2 * f = a + 4 * b ∧
    f = b + c ∧
    a + 2 * f = 4 * c ∧
    a + b + f = 3 * c ∧
    2 * g < a + 2 * f ∧
    c + g < a + b + f ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    e + g < 2 * a + b + f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    b + e < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f ∧
    2 * c + e < 2 * a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG2
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : 2 * g < a + 2 * f ∧
      2 * c < a + 2 * b ∧
      2 * e < a + b + f ∧
      f < 2 * a + b ∧
      a + 4 * b < 2 * f) :
    2 * g < a + 2 * f ∧
    2 * c < a + 2 * b ∧
    c + g < a + b + f ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    e + g < 2 * a + b + f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    a + 4 * b < 2 * f ∧
    b + c < f ∧
    b + e < a + f ∧
    4 * c < a + 2 * f ∧
    2 * c + 2 * e < 3 * a + 2 * f ∧
    3 * c < a + b + f ∧
    2 * c + e < 2 * a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG26
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : a + 2 * f < 2 * g ∧
      2 * c < a + 2 * b ∧
      4 * e < a + 2 * b + 2 * g ∧
      2 * g < 5 * a + 2 * b ∧
      a + 2 * b < g) :
    a + 2 * f < 2 * g ∧
    c + f < b + g ∧
    2 * c < a + 2 * b ∧
    4 * e < a + 2 * b + 2 * g ∧
    e + f < a + b + g ∧
    2 * e < 3 * a + 2 * b ∧
    4 * f < 3 * a + 2 * b + 2 * g ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    a + 2 * b < g ∧
    a + 2 * b + 2 * c < 2 * g ∧
    2 * b + 2 * e < a + 2 * g ∧
    2 * c < g ∧
    c + e < a + g ∧
    6 * c < a + 2 * b + 2 * g ∧
    4 * c + 2 * e < 3 * a + 2 * b + 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG27
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : g = a + 2 * b ∧
      a + 2 * f < 2 * g ∧
      4 * e < a + 2 * b + 2 * g ∧
      6 * c < a + 2 * b + 2 * g) :
    g = a + 2 * b ∧
    a + 2 * f < 2 * g ∧
    c + f < b + g ∧
    2 * c < a + 2 * b ∧
    4 * e < a + 2 * b + 2 * g ∧
    e + f < a + b + g ∧
    2 * e < 3 * a + 2 * b ∧
    4 * f < 3 * a + 2 * b + 2 * g ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    a + 2 * b + 2 * c < 2 * g ∧
    2 * b + 2 * e < a + 2 * g ∧
    2 * c < g ∧
    c + e < a + g ∧
    6 * c < a + 2 * b + 2 * g ∧
    4 * c + 2 * e < 3 * a + 2 * b + 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG28
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : a + 2 * b = 2 * c ∧
      c + f < b + g ∧
      4 * e < a + 2 * b + 2 * g ∧
      2 * g < 5 * a + 2 * b ∧
      6 * c < a + 2 * b + 2 * g) :
    a + 2 * b = 2 * c ∧
    a + 2 * f < 2 * g ∧
    c + f < b + g ∧
    4 * e < a + 2 * b + 2 * g ∧
    e + f < a + b + g ∧
    2 * e < 3 * a + 2 * b ∧
    4 * f < 3 * a + 2 * b + 2 * g ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    a + 2 * b < g ∧
    a + 2 * b + 2 * c < 2 * g ∧
    2 * b + 2 * e < a + 2 * g ∧
    2 * c < g ∧
    c + e < a + g ∧
    6 * c < a + 2 * b + 2 * g ∧
    4 * c + 2 * e < 3 * a + 2 * b + 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG29
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : g = 2 * c ∧
      a + 2 * b + 2 * g = 6 * c ∧
      c + f < b + g ∧
      4 * e < a + 2 * b + 2 * g) :
    a + 2 * b = 2 * c ∧
    g = a + 2 * b ∧
    2 * g = a + 2 * b + 2 * c ∧
    g = 2 * c ∧
    a + 2 * b + 2 * g = 6 * c ∧
    a + 2 * f < 2 * g ∧
    c + f < b + g ∧
    4 * e < a + 2 * b + 2 * g ∧
    e + f < a + b + g ∧
    2 * e < 3 * a + 2 * b ∧
    4 * f < 3 * a + 2 * b + 2 * g ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * b + 2 * e < a + 2 * g ∧
    c + e < a + g ∧
    4 * c + 2 * e < 3 * a + 2 * b + 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG3
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : 2 * f = a + 4 * b ∧
      2 * g < a + 2 * f ∧
      2 * e < a + b + f ∧
      3 * c < a + b + f) :
    2 * f = a + 4 * b ∧
    2 * g < a + 2 * f ∧
    2 * c < a + 2 * b ∧
    c + g < a + b + f ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    e + g < 2 * a + b + f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    b + c < f ∧
    b + e < a + f ∧
    4 * c < a + 2 * f ∧
    2 * c + 2 * e < 3 * a + 2 * f ∧
    3 * c < a + b + f ∧
    2 * c + e < 2 * a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG38
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : a + 2 * f < 4 * c ∧
      g < 2 * c ∧
      2 * e < 3 * c ∧
      a + 2 * b < 2 * c) :
    a + b + f < 3 * c ∧
    a + 2 * b + 2 * g < 6 * c ∧
    a + 2 * f < 4 * c ∧
    g < 2 * c ∧
    2 * e < 3 * c ∧
    2 * e + 2 * f < a + 6 * c ∧
    e + g < a + 3 * c ∧
    2 * f < a + 3 * c ∧
    2 * f + 2 * g < 3 * a + 6 * c ∧
    2 * g < 2 * a + 3 * c ∧
    a + 2 * b < 2 * c ∧
    a + 2 * b < 2 * c ∧
    2 * b + e < 3 * c ∧
    a + 2 * b < 2 * c ∧
    2 * b + 2 * e < a + 4 * c ∧
    e < a + c := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG39
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : a + 2 * b < 2 * c ∧
      2 * g < a + 2 * f ∧
      4 * e < a + 2 * c + 2 * f ∧
      2 * f < 3 * a + 2 * c ∧
      4 * c < a + 2 * f) :
    a + 2 * b < 2 * c ∧
    b + g < c + f ∧
    2 * g < a + 2 * f ∧
    4 * e < a + 2 * c + 2 * f ∧
    e < a + c ∧
    2 * e + 2 * g < 3 * a + 2 * c + 2 * f ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    4 * g < 5 * a + 2 * c + 2 * f ∧
    a + 3 * b < c + f ∧
    a + 4 * b < 2 * f ∧
    4 * b + 2 * e < a + 2 * c + 2 * f ∧
    b + c < f ∧
    b + e < a + f ∧
    4 * c < a + 2 * f ∧
    2 * c + 2 * e < 3 * a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG4
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : a + 2 * f = 2 * g ∧
      c + g < a + b + f ∧
      2 * e < a + b + f ∧
      2 * g < 3 * a + b + f ∧
      a + 4 * b < 2 * f) :
    a + 2 * f = 2 * g ∧
    2 * c < a + 2 * b ∧
    c + g < a + b + f ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    e + g < 2 * a + b + f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    a + 4 * b < 2 * f ∧
    b + c < f ∧
    b + e < a + f ∧
    4 * c < a + 2 * f ∧
    2 * c + 2 * e < 3 * a + 2 * f ∧
    3 * c < a + b + f ∧
    2 * c + e < 2 * a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG40
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : a + 2 * f = 4 * c ∧
      2 * g < a + 2 * f ∧
      4 * e < a + 2 * c + 2 * f ∧
      b + c < f) :
    a + 2 * f = 4 * c ∧
    a + 2 * b < 2 * c ∧
    b + g < c + f ∧
    2 * g < a + 2 * f ∧
    4 * e < a + 2 * c + 2 * f ∧
    e < a + c ∧
    2 * e + 2 * g < 3 * a + 2 * c + 2 * f ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    4 * g < 5 * a + 2 * c + 2 * f ∧
    a + 3 * b < c + f ∧
    a + 4 * b < 2 * f ∧
    4 * b + 2 * e < a + 2 * c + 2 * f ∧
    b + c < f ∧
    b + e < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG41
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : a + 2 * f = 2 * g ∧
      b + g < c + f ∧
      4 * e < a + 2 * c + 2 * f ∧
      4 * g < 5 * a + 2 * c + 2 * f ∧
      4 * c < a + 2 * f) :
    a + 2 * f = 2 * g ∧
    a + 2 * b < 2 * c ∧
    b + g < c + f ∧
    4 * e < a + 2 * c + 2 * f ∧
    e < a + c ∧
    2 * e + 2 * g < 3 * a + 2 * c + 2 * f ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    4 * g < 5 * a + 2 * c + 2 * f ∧
    a + 3 * b < c + f ∧
    a + 4 * b < 2 * f ∧
    4 * b + 2 * e < a + 2 * c + 2 * f ∧
    b + c < f ∧
    b + e < a + f ∧
    4 * c < a + 2 * f ∧
    2 * c + 2 * e < 3 * a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG42
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : a + 2 * f = 2 * g ∧
      a + 2 * f = 4 * c ∧
      4 * e < a + 2 * c + 2 * f ∧
      b + c < f) :
    a + 2 * f = 2 * g ∧
    a + 2 * f = 4 * c ∧
    a + 2 * b < 2 * c ∧
    b + g < c + f ∧
    4 * e < a + 2 * c + 2 * f ∧
    e < a + c ∧
    2 * e + 2 * g < 3 * a + 2 * c + 2 * f ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    4 * g < 5 * a + 2 * c + 2 * f ∧
    a + 3 * b < c + f ∧
    a + 4 * b < 2 * f ∧
    4 * b + 2 * e < a + 2 * c + 2 * f ∧
    b + c < f ∧
    b + e < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG5
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : a + 2 * f = 2 * g ∧
      2 * f = a + 4 * b ∧
      2 * e < a + b + f ∧
      3 * c < a + b + f) :
    a + 2 * f = 2 * g ∧
    2 * f = a + 4 * b ∧
    2 * c < a + 2 * b ∧
    c + g < a + b + f ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    e + g < 2 * a + b + f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    b + c < f ∧
    b + e < a + f ∧
    4 * c < a + 2 * f ∧
    2 * c + 2 * e < 3 * a + 2 * f ∧
    3 * c < a + b + f ∧
    2 * c + e < 2 * a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG51
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : a + 2 * b < 2 * c ∧
      a + 2 * f < 2 * g ∧
      2 * e < c + g ∧
      g < 2 * a + c ∧
      2 * c < g) :
    a + b + f < c + g ∧
    a + 2 * b < 2 * c ∧
    a + 2 * f < 2 * g ∧
    2 * e < c + g ∧
    2 * e + 2 * f < a + 2 * c + 2 * g ∧
    e < a + c ∧
    2 * f < a + c + g ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    3 * a + 6 * b < 2 * c + 2 * g ∧
    a + 2 * b < g ∧
    2 * b + e < c + g ∧
    a + 2 * b + 2 * c < 2 * g ∧
    2 * b + 2 * e < a + 2 * g ∧
    2 * c < g ∧
    c + e < a + g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG52
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : g = 2 * c ∧
      a + 2 * f < 2 * g ∧
      2 * e < c + g ∧
      a + 2 * b + 2 * c < 2 * g) :
    g = 2 * c ∧
    a + b + f < c + g ∧
    a + 2 * b < 2 * c ∧
    a + 2 * f < 2 * g ∧
    2 * e < c + g ∧
    2 * e + 2 * f < a + 2 * c + 2 * g ∧
    e < a + c ∧
    2 * f < a + c + g ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    3 * a + 6 * b < 2 * c + 2 * g ∧
    a + 2 * b < g ∧
    2 * b + e < c + g ∧
    a + 2 * b + 2 * c < 2 * g ∧
    2 * b + 2 * e < a + 2 * g ∧
    c + e < a + g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG57
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : a + b + f < 2 * e ∧
      a + 2 * b + 2 * g < 4 * e ∧
      a + 2 * c + 2 * f < 4 * e ∧
      c + g < 2 * e ∧
      2 * f < a + 2 * e ∧
      g < a + e ∧
      3 * a + 6 * b < 4 * e ∧
      3 * c < 2 * e) :
    a + b + f < 2 * e ∧
    a + 2 * b + 2 * g < 4 * e ∧
    a + 2 * c + 2 * f < 4 * e ∧
    c + g < 2 * e ∧
    2 * f < a + 2 * e ∧
    g < a + e ∧
    2 * f < a + 2 * e ∧
    2 * f + 2 * g < 3 * a + 4 * e ∧
    g < a + e ∧
    3 * a + 6 * b < 4 * e ∧
    a + 2 * b + c < 2 * e ∧
    2 * b < e ∧
    a + 2 * b + 4 * c < 4 * e ∧
    2 * b + 2 * c < a + 2 * e ∧
    3 * c < 2 * e ∧
    2 * c < a + e := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG58
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : 4 * e = 3 * a + 6 * b ∧
      a + b + f < 2 * e ∧
      a + 2 * b + 2 * g < 4 * e ∧
      3 * c < 2 * e) :
    4 * e = 3 * a + 6 * b ∧
    a + b + f < 2 * e ∧
    a + 2 * b + 2 * g < 4 * e ∧
    a + 2 * c + 2 * f < 4 * e ∧
    c + g < 2 * e ∧
    2 * f < a + 2 * e ∧
    g < a + e ∧
    2 * f < a + 2 * e ∧
    2 * f + 2 * g < 3 * a + 4 * e ∧
    g < a + e ∧
    a + 2 * b + c < 2 * e ∧
    2 * b < e ∧
    a + 2 * b + 4 * c < 4 * e ∧
    2 * b + 2 * c < a + 2 * e ∧
    3 * c < 2 * e ∧
    2 * c < a + e := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG59
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : 4 * e = a + 2 * b + 4 * c ∧
      2 * e = 3 * c ∧
      a + 2 * c + 2 * f < 4 * e ∧
      c + g < 2 * e) :
    4 * e = 3 * a + 6 * b ∧
    2 * e = a + 2 * b + c ∧
    4 * e = a + 2 * b + 4 * c ∧
    2 * e = 3 * c ∧
    a + b + f < 2 * e ∧
    a + 2 * b + 2 * g < 4 * e ∧
    a + 2 * c + 2 * f < 4 * e ∧
    c + g < 2 * e ∧
    2 * f < a + 2 * e ∧
    g < a + e ∧
    2 * f < a + 2 * e ∧
    2 * f + 2 * g < 3 * a + 4 * e ∧
    g < a + e ∧
    2 * b < e ∧
    2 * b + 2 * c < a + 2 * e ∧
    2 * c < a + e := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG6
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : a + 2 * b = 2 * c ∧
      a + b + f = c + g ∧
      2 * e < a + b + f ∧
      2 * g < 3 * a + b + f ∧
      3 * c < a + b + f) :
    a + 2 * f = 2 * g ∧
    a + 2 * b = 2 * c ∧
    a + b + f = c + g ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    e + g < 2 * a + b + f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    a + 4 * b < 2 * f ∧
    b + c < f ∧
    b + e < a + f ∧
    4 * c < a + 2 * f ∧
    2 * c + 2 * e < 3 * a + 2 * f ∧
    3 * c < a + b + f ∧
    2 * c + e < 2 * a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG60
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : 2 * e = 3 * c ∧
      a + 2 * c + 2 * f < 4 * e ∧
      c + g < 2 * e ∧
      a + 2 * b + 4 * c < 4 * e) :
    2 * e = 3 * c ∧
    a + b + f < 2 * e ∧
    a + 2 * b + 2 * g < 4 * e ∧
    a + 2 * c + 2 * f < 4 * e ∧
    c + g < 2 * e ∧
    2 * f < a + 2 * e ∧
    g < a + e ∧
    2 * f < a + 2 * e ∧
    2 * f + 2 * g < 3 * a + 4 * e ∧
    g < a + e ∧
    3 * a + 6 * b < 4 * e ∧
    a + 2 * b + c < 2 * e ∧
    2 * b < e ∧
    a + 2 * b + 4 * c < 4 * e ∧
    2 * b + 2 * c < a + 2 * e ∧
    2 * c < a + e := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG61
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : a + e = g ∧
      3 * a + 4 * e = 2 * f + 2 * g ∧
      a + 2 * b + 2 * g < 4 * e ∧
      c + g < 2 * e) :
    a + 2 * e = 2 * f ∧
    a + e = g ∧
    a + 2 * e = 2 * f ∧
    3 * a + 4 * e = 2 * f + 2 * g ∧
    a + e = g ∧
    a + b + f < 2 * e ∧
    a + 2 * b + 2 * g < 4 * e ∧
    a + 2 * c + 2 * f < 4 * e ∧
    c + g < 2 * e ∧
    3 * a + 6 * b < 4 * e ∧
    a + 2 * b + c < 2 * e ∧
    2 * b < e ∧
    a + 2 * b + 4 * c < 4 * e ∧
    2 * b + 2 * c < a + 2 * e ∧
    3 * c < 2 * e ∧
    2 * c < a + e := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG62
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : a + 2 * e = 2 * f ∧
      a + b + f < 2 * e ∧
      a + 2 * c + 2 * f < 4 * e ∧
      2 * f + 2 * g < 3 * a + 4 * e) :
    a + 2 * e = 2 * f ∧
    a + 2 * e = 2 * f ∧
    a + b + f < 2 * e ∧
    a + 2 * b + 2 * g < 4 * e ∧
    a + 2 * c + 2 * f < 4 * e ∧
    c + g < 2 * e ∧
    g < a + e ∧
    2 * f + 2 * g < 3 * a + 4 * e ∧
    g < a + e ∧
    3 * a + 6 * b < 4 * e ∧
    a + 2 * b + c < 2 * e ∧
    2 * b < e ∧
    a + 2 * b + 4 * c < 4 * e ∧
    2 * b + 2 * c < a + 2 * e ∧
    3 * c < 2 * e ∧
    2 * c < a + e := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG63
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : a + e = g ∧
      a + 2 * b + 2 * g < 4 * e ∧
      c + g < 2 * e ∧
      2 * f + 2 * g < 3 * a + 4 * e) :
    a + e = g ∧
    a + e = g ∧
    a + b + f < 2 * e ∧
    a + 2 * b + 2 * g < 4 * e ∧
    a + 2 * c + 2 * f < 4 * e ∧
    c + g < 2 * e ∧
    2 * f < a + 2 * e ∧
    2 * f < a + 2 * e ∧
    2 * f + 2 * g < 3 * a + 4 * e ∧
    3 * a + 6 * b < 4 * e ∧
    a + 2 * b + c < 2 * e ∧
    2 * b < e ∧
    a + 2 * b + 4 * c < 4 * e ∧
    2 * b + 2 * c < a + 2 * e ∧
    3 * c < 2 * e ∧
    2 * c < a + e := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG64
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : 2 * a + b < f ∧
      3 * a + 2 * c < 2 * f ∧
      a + 2 * e < 2 * f ∧
      2 * g < a + 2 * f) :
    2 * a + b < f ∧
    3 * a + 2 * b + 2 * g < 4 * f ∧
    3 * a + 2 * c < 2 * f ∧
    a + c + g < 2 * f ∧
    a + 2 * e < 2 * f ∧
    a + 2 * e < 2 * f ∧
    e + g < 2 * f ∧
    2 * g < a + 2 * f ∧
    2 * g < a + 2 * f ∧
    5 * a + 6 * b < 4 * f ∧
    2 * a + 2 * b + c < 2 * f ∧
    a + 2 * b + e < 2 * f ∧
    3 * a + 2 * b + 4 * c < 4 * f ∧
    a + 2 * b + 2 * c + 2 * e < 4 * f ∧
    a + 3 * c < 2 * f ∧
    2 * c + e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG65
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : a + 2 * f = 2 * g ∧
      3 * a + 2 * b + 2 * g < 4 * f ∧
      a + c + g < 2 * f ∧
      e + g < 2 * f) :
    a + 2 * f = 2 * g ∧
    a + 2 * f = 2 * g ∧
    2 * a + b < f ∧
    3 * a + 2 * b + 2 * g < 4 * f ∧
    3 * a + 2 * c < 2 * f ∧
    a + c + g < 2 * f ∧
    a + 2 * e < 2 * f ∧
    a + 2 * e < 2 * f ∧
    e + g < 2 * f ∧
    5 * a + 6 * b < 4 * f ∧
    2 * a + 2 * b + c < 2 * f ∧
    a + 2 * b + e < 2 * f ∧
    3 * a + 2 * b + 4 * c < 4 * f ∧
    a + 2 * b + 2 * c + 2 * e < 4 * f ∧
    a + 3 * c < 2 * f ∧
    2 * c + e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG66
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : 5 * a + 2 * b < 2 * g ∧
      2 * a + c < g ∧
      a + e < g ∧
      a + 2 * f < 2 * g) :
    3 * a + b + f < 2 * g ∧
    5 * a + 2 * b < 2 * g ∧
    5 * a + 2 * c + 2 * f < 4 * g ∧
    2 * a + c < g ∧
    a + e < g ∧
    3 * a + 2 * e + 2 * f < 4 * g ∧
    a + e < g ∧
    a + 2 * f < 2 * g ∧
    a + 2 * f < 2 * g ∧
    7 * a + 6 * b < 4 * g ∧
    3 * a + 2 * b + c < 2 * g ∧
    2 * a + 2 * b + e < 2 * g ∧
    5 * a + 2 * b + 4 * c < 4 * g ∧
    3 * a + 2 * b + 2 * c + 2 * e < 4 * g ∧
    2 * a + 3 * c < 2 * g ∧
    a + 2 * c + e < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEFG7
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hs : a + b + f = c + g ∧
      a + 2 * f = 4 * c ∧
      a + b + f = 3 * c ∧
      2 * e < a + b + f) :
    a + 2 * f = 2 * g ∧
    a + 2 * b = 2 * c ∧
    a + b + f = c + g ∧
    2 * f = a + 4 * b ∧
    f = b + c ∧
    a + 2 * f = 4 * c ∧
    a + b + f = 3 * c ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    e + g < 2 * a + b + f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    b + e < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f ∧
    2 * c + e < 2 * a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BCEFG`. -/
theorem quarticChamberSupport810_of_live_BCEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDz : D = 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG58 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG58 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG22 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG23 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG2 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG3 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
      · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG2 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG3 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG24 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG62 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG62 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
      · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG64 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG64 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG25 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG2 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG3 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG64 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG64 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG64 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG64 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG58 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG58 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG12 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG13 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG4 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG5 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
      · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG4 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG5 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG14 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG61 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG61 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
      · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG65 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG65 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG15 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG4 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG5 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG65 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG65 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG65 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG65 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht2a | ht2b | ht2c
      · -- G.natDegree < A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG58 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG58 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG34 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG35 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG27 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG27 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
      · -- G.natDegree = A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG27 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG27 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG36 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG63 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG63 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
      · -- G.natDegree > A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG66 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG66 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG37 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG27 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG27 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG66 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG66 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG66 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG66 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG59 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG59 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG18 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG19 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG16 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG17 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG17 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
      · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG16 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG17 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG17 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG20 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG62 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG62 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
      · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG64 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG64 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG21 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG16 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG17 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG17 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG64 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG64 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG64 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG64 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG59 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG59 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG8 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG9 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG6 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG6 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG7 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG7 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
      · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG6 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG6 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG7 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG7 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG10 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG61 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG61 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
      · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG65 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG65 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG11 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG6 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG6 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG7 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG7 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG65 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG65 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG65 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG65 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht2a | ht2b | ht2c
      · -- G.natDegree < A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG59 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG59 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG30 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG31 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG28 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG28 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG29 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG29 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
      · -- G.natDegree = A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG28 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG28 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG29 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG29 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG32 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG63 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG63 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
      · -- G.natDegree > A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG66 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG66 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG33 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG28 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG28 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG29 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG29 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG66 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG66 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG66 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG66 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG60 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG60 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG47 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG48 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG39 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG39 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG40 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG40 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
      · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG39 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG39 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG40 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG40 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG49 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG62 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG62 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
      · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG64 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG64 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG50 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG39 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG39 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG40 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG40 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG64 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG64 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG64 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG64 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG60 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG60 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG43 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG44 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG41 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG41 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG42 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG42 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
      · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG41 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG41 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG42 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG42 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG45 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG61 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG61 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
      · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG65 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG65 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG46 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG41 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG41 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG42 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG42 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG65 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG65 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG65 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG65 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht2a | ht2b | ht2c
      · -- G.natDegree < A.natDegree + E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG60 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG60 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · -- C.natDegree + G.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG53 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG54 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · -- C.natDegree + G.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG51 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG51 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG52 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG57 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG57 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
      · -- G.natDegree = A.natDegree + E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG51 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG51 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG52 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG55 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG63 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG63 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
      · -- G.natDegree > A.natDegree + E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG66 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG66 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG56 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG51 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG51 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG52 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG38 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG66 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG66 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBCEFG66 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailBCEFG66 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn (by omega)⟩)
end QuarticChamberExhaust810

end Max11DegreeRoutes
