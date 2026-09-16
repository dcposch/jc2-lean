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
private theorem astra4zExhaustTailCDEFG0
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hs : a + 2 * f < 4 * c ∧
      g < 2 * c ∧
      a + 2 * d < 3 * c ∧
      2 * e < 3 * c) :
    a + 2 * f < 4 * c ∧
    g < 2 * c ∧
    a + 2 * d < 3 * c ∧
    a + 2 * d + 2 * e < 6 * c ∧
    d + f < 3 * c ∧
    2 * d + 2 * g < a + 6 * c ∧
    2 * e < 3 * c ∧
    2 * e + 2 * f < a + 6 * c ∧
    e + g < a + 3 * c ∧
    2 * f < a + 3 * c ∧
    2 * f + 2 * g < 3 * a + 6 * c ∧
    2 * g < 2 * a + 3 * c ∧
    2 * d < a + 2 * c ∧
    e < a + c := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEFG1
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hs : 2 * g < a + 2 * f ∧
      a + 4 * d < 2 * c + 2 * f ∧
      4 * e < a + 2 * c + 2 * f ∧
      2 * f < 3 * a + 2 * c ∧
      4 * c < a + 2 * f) :
    2 * g < a + 2 * f ∧
    a + 4 * d < 2 * c + 2 * f ∧
    d + e < c + f ∧
    2 * d < a + 2 * c ∧
    d + g < a + c + f ∧
    4 * e < a + 2 * c + 2 * f ∧
    e < a + c ∧
    2 * e + 2 * g < 3 * a + 2 * c + 2 * f ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    4 * g < 5 * a + 2 * c + 2 * f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEFG14
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hs : 2 * a + c = g ∧
      5 * a + 2 * c + 2 * f = 4 * g ∧
      d + g < a + c + f ∧
      2 * e + 2 * g < 3 * a + 2 * c + 2 * f) :
    a + 2 * f = 2 * g ∧
    3 * a + 2 * c = 2 * f ∧
    2 * a + c = g ∧
    5 * a + 2 * c + 2 * f = 4 * g ∧
    a + 4 * d < 2 * c + 2 * f ∧
    d + e < c + f ∧
    2 * d < a + 2 * c ∧
    d + g < a + c + f ∧
    4 * e < a + 2 * c + 2 * f ∧
    e < a + c ∧
    2 * e + 2 * g < 3 * a + 2 * c + 2 * f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEFG2
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hs : a + 2 * f = 4 * c ∧
      2 * g < a + 2 * f ∧
      a + 4 * d < 2 * c + 2 * f ∧
      4 * e < a + 2 * c + 2 * f) :
    a + 2 * f = 4 * c ∧
    2 * g < a + 2 * f ∧
    a + 4 * d < 2 * c + 2 * f ∧
    d + e < c + f ∧
    2 * d < a + 2 * c ∧
    d + g < a + c + f ∧
    4 * e < a + 2 * c + 2 * f ∧
    e < a + c ∧
    2 * e + 2 * g < 3 * a + 2 * c + 2 * f ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    4 * g < 5 * a + 2 * c + 2 * f ∧
    c + d < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEFG24
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hs : 3 * a + 2 * c = 2 * f ∧
      2 * d < a + 2 * c ∧
      e < a + c ∧
      4 * g < 5 * a + 2 * c + 2 * f) :
    3 * a + 2 * c = 2 * f ∧
    2 * g < a + 2 * f ∧
    a + 4 * d < 2 * c + 2 * f ∧
    d + e < c + f ∧
    2 * d < a + 2 * c ∧
    d + g < a + c + f ∧
    4 * e < a + 2 * c + 2 * f ∧
    e < a + c ∧
    2 * e + 2 * g < 3 * a + 2 * c + 2 * f ∧
    g < 2 * a + c ∧
    4 * g < 5 * a + 2 * c + 2 * f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEFG25
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hs : a + 2 * f < 2 * g ∧
      a + 2 * d < c + g ∧
      2 * e < c + g ∧
      g < 2 * a + c ∧
      2 * c < g) :
    a + 2 * f < 2 * g ∧
    a + 2 * d < c + g ∧
    a + 2 * d + 2 * e < 2 * c + 2 * g ∧
    d + f < c + g ∧
    2 * d < a + 2 * c ∧
    2 * e < c + g ∧
    2 * e + 2 * f < a + 2 * c + 2 * g ∧
    e < a + c ∧
    2 * f < a + c + g ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    2 * c < g ∧
    2 * c + 2 * d < a + 2 * g ∧
    c + e < a + g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEFG26
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hs : g = 2 * c ∧
      a + 2 * f < 2 * g ∧
      a + 2 * d < c + g ∧
      2 * e < c + g) :
    g = 2 * c ∧
    a + 2 * f < 2 * g ∧
    a + 2 * d < c + g ∧
    a + 2 * d + 2 * e < 2 * c + 2 * g ∧
    d + f < c + g ∧
    2 * d < a + 2 * c ∧
    2 * e < c + g ∧
    2 * e + 2 * f < a + 2 * c + 2 * g ∧
    e < a + c ∧
    2 * f < a + c + g ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    2 * c + 2 * d < a + 2 * g ∧
    c + e < a + g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEFG3
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hs : a + 2 * f = 2 * g ∧
      a + 4 * d < 2 * c + 2 * f ∧
      4 * e < a + 2 * c + 2 * f ∧
      4 * g < 5 * a + 2 * c + 2 * f ∧
      4 * c < a + 2 * f) :
    a + 2 * f = 2 * g ∧
    a + 4 * d < 2 * c + 2 * f ∧
    d + e < c + f ∧
    2 * d < a + 2 * c ∧
    d + g < a + c + f ∧
    4 * e < a + 2 * c + 2 * f ∧
    e < a + c ∧
    2 * e + 2 * g < 3 * a + 2 * c + 2 * f ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    4 * g < 5 * a + 2 * c + 2 * f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEFG36
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hs : 2 * a + c = g ∧
      2 * d < a + 2 * c ∧
      e < a + c ∧
      2 * f < 3 * a + 2 * c) :
    2 * a + c = g ∧
    a + 2 * f < 2 * g ∧
    a + 2 * d < c + g ∧
    a + 2 * d + 2 * e < 2 * c + 2 * g ∧
    d + f < c + g ∧
    2 * d < a + 2 * c ∧
    2 * e < c + g ∧
    2 * e + 2 * f < a + 2 * c + 2 * g ∧
    e < a + c ∧
    2 * f < a + c + g ∧
    2 * f < 3 * a + 2 * c ∧
    2 * c < g ∧
    2 * c + 2 * d < a + 2 * g ∧
    c + e < a + g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEFG37
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hs : 2 * c + 2 * f < a + 4 * d ∧
      c + g < a + 2 * d ∧
      2 * e < a + 2 * d ∧
      f < a + d ∧
      2 * g < 3 * a + 2 * d ∧
      3 * c < a + 2 * d) :
    2 * c + 2 * f < a + 4 * d ∧
    c + g < a + 2 * d ∧
    2 * e < a + 2 * d ∧
    f < a + d ∧
    2 * g < 3 * a + 2 * d ∧
    2 * e < a + 2 * d ∧
    2 * e + 2 * f < 3 * a + 4 * d ∧
    e + g < 2 * a + 2 * d ∧
    f < a + d ∧
    2 * f + 2 * g < 5 * a + 4 * d ∧
    2 * g < 3 * a + 2 * d ∧
    3 * c < a + 2 * d ∧
    4 * c < 3 * a + 2 * d ∧
    2 * c + e < 2 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEFG38
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hs : a + 2 * d = 3 * c ∧
      2 * c + 2 * f < a + 4 * d ∧
      c + g < a + 2 * d ∧
      2 * e < a + 2 * d) :
    a + 2 * d = 3 * c ∧
    2 * c + 2 * f < a + 4 * d ∧
    c + g < a + 2 * d ∧
    2 * e < a + 2 * d ∧
    f < a + d ∧
    2 * g < 3 * a + 2 * d ∧
    2 * e < a + 2 * d ∧
    2 * e + 2 * f < 3 * a + 4 * d ∧
    e + g < 2 * a + 2 * d ∧
    f < a + d ∧
    2 * f + 2 * g < 5 * a + 4 * d ∧
    2 * g < 3 * a + 2 * d ∧
    4 * c < 3 * a + 2 * d ∧
    2 * c + e < 2 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEFG4
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hs : a + 2 * f = 2 * g ∧
      a + 2 * f = 4 * c ∧
      a + 4 * d < 2 * c + 2 * f ∧
      4 * e < a + 2 * c + 2 * f) :
    a + 2 * f = 2 * g ∧
    a + 2 * f = 4 * c ∧
    a + 4 * d < 2 * c + 2 * f ∧
    d + e < c + f ∧
    2 * d < a + 2 * c ∧
    d + g < a + c + f ∧
    4 * e < a + 2 * c + 2 * f ∧
    e < a + c ∧
    2 * e + 2 * g < 3 * a + 2 * c + 2 * f ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    4 * g < 5 * a + 2 * c + 2 * f ∧
    c + d < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEFG42
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hs : a + 2 * d = 2 * e ∧
      2 * c + 2 * f < a + 4 * d ∧
      c + g < a + 2 * d ∧
      2 * e + 2 * f < 3 * a + 4 * d ∧
      e + g < 2 * a + 2 * d ∧
      3 * c < a + 2 * d) :
    a + 2 * d = 2 * e ∧
    a + 2 * d = 2 * e ∧
    2 * c + 2 * f < a + 4 * d ∧
    c + g < a + 2 * d ∧
    f < a + d ∧
    2 * g < 3 * a + 2 * d ∧
    2 * e + 2 * f < 3 * a + 4 * d ∧
    e + g < 2 * a + 2 * d ∧
    f < a + d ∧
    2 * f + 2 * g < 5 * a + 4 * d ∧
    2 * g < 3 * a + 2 * d ∧
    3 * c < a + 2 * d ∧
    4 * c < 3 * a + 2 * d ∧
    2 * c + e < 2 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEFG43
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hs : a + 2 * d = 2 * e ∧
      a + 2 * d = 3 * c ∧
      2 * c + 2 * f < a + 4 * d ∧
      c + g < a + 2 * d) :
    a + 2 * d = 2 * e ∧
    a + 2 * d = 2 * e ∧
    a + 2 * d = 3 * c ∧
    2 * c + 2 * f < a + 4 * d ∧
    c + g < a + 2 * d ∧
    f < a + d ∧
    2 * g < 3 * a + 2 * d ∧
    2 * e + 2 * f < 3 * a + 4 * d ∧
    e + g < 2 * a + 2 * d ∧
    f < a + d ∧
    2 * f + 2 * g < 5 * a + 4 * d ∧
    2 * g < 3 * a + 2 * d ∧
    4 * c < 3 * a + 2 * d ∧
    2 * c + e < 2 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEFG47
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hs : a + 2 * c + 2 * f < 4 * e ∧
      c + g < 2 * e ∧
      a + 2 * d < 2 * e ∧
      2 * f < a + 2 * e ∧
      g < a + e ∧
      3 * c < 2 * e) :
    a + 2 * c + 2 * f < 4 * e ∧
    c + g < 2 * e ∧
    a + 2 * d < 2 * e ∧
    a + 2 * d < 2 * e ∧
    d + f < 2 * e ∧
    2 * d + 2 * g < a + 4 * e ∧
    2 * f < a + 2 * e ∧
    g < a + e ∧
    2 * f < a + 2 * e ∧
    2 * f + 2 * g < 3 * a + 4 * e ∧
    g < a + e ∧
    3 * c < 2 * e ∧
    4 * c + 2 * d < a + 4 * e ∧
    2 * c < a + e := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEFG48
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hs : 2 * e = 3 * c ∧
      a + 2 * c + 2 * f < 4 * e ∧
      c + g < 2 * e ∧
      a + 2 * d < 2 * e) :
    2 * e = 3 * c ∧
    a + 2 * c + 2 * f < 4 * e ∧
    c + g < 2 * e ∧
    a + 2 * d < 2 * e ∧
    a + 2 * d < 2 * e ∧
    d + f < 2 * e ∧
    2 * d + 2 * g < a + 4 * e ∧
    2 * f < a + 2 * e ∧
    g < a + e ∧
    2 * f < a + 2 * e ∧
    2 * f + 2 * g < 3 * a + 4 * e ∧
    g < a + e ∧
    4 * c + 2 * d < a + 4 * e ∧
    2 * c < a + e := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEFG52
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hs : 3 * a + 2 * c < 2 * f ∧
      a + d < f ∧
      a + 2 * e < 2 * f ∧
      2 * g < a + 2 * f) :
    3 * a + 2 * c < 2 * f ∧
    a + c + g < 2 * f ∧
    a + d < f ∧
    3 * a + 2 * d + 2 * e < 4 * f ∧
    a + d < f ∧
    a + 2 * d + 2 * g < 4 * f ∧
    a + 2 * e < 2 * f ∧
    a + 2 * e < 2 * f ∧
    e + g < 2 * f ∧
    2 * g < a + 2 * f ∧
    2 * g < a + 2 * f ∧
    a + 3 * c < 2 * f ∧
    a + 4 * c + 2 * d < 4 * f ∧
    2 * c + e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEFG53
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hs : a + 2 * f = 2 * g ∧
      a + c + g < 2 * f ∧
      a + 2 * d + 2 * g < 4 * f ∧
      e + g < 2 * f) :
    a + 2 * f = 2 * g ∧
    a + 2 * f = 2 * g ∧
    3 * a + 2 * c < 2 * f ∧
    a + c + g < 2 * f ∧
    a + d < f ∧
    3 * a + 2 * d + 2 * e < 4 * f ∧
    a + d < f ∧
    a + 2 * d + 2 * g < 4 * f ∧
    a + 2 * e < 2 * f ∧
    a + 2 * e < 2 * f ∧
    e + g < 2 * f ∧
    a + 3 * c < 2 * f ∧
    a + 4 * c + 2 * d < 4 * f ∧
    2 * c + e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEFG54
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hs : 2 * a + c < g ∧
      3 * a + 2 * d < 2 * g ∧
      a + e < g ∧
      a + 2 * f < 2 * g) :
    5 * a + 2 * c + 2 * f < 4 * g ∧
    2 * a + c < g ∧
    3 * a + 2 * d < 2 * g ∧
    5 * a + 2 * d + 2 * e < 4 * g ∧
    2 * a + d + f < 2 * g ∧
    3 * a + 2 * d < 2 * g ∧
    a + e < g ∧
    3 * a + 2 * e + 2 * f < 4 * g ∧
    a + e < g ∧
    a + 2 * f < 2 * g ∧
    a + 2 * f < 2 * g ∧
    2 * a + 3 * c < 2 * g ∧
    3 * a + 4 * c + 2 * d < 4 * g ∧
    a + 2 * c + e < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `CDEFG`. -/
theorem quarticChamberSupport810_of_live_CDEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG37 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG37 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG38 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG15 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG16 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG37 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG37 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG37 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG37 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG20 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG45 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG52 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG24 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG24 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG52 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG52 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG37 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG37 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG38 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG5 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG6 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG4 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG37 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG37 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG37 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG37 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG4 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG10 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG44 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG53 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG14 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG4 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG53 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG53 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG37 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG37 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG38 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG27 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG28 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG26 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG37 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG37 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG37 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG37 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG26 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG32 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG46 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG54 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG36 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG36 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG26 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG54 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG54 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
  · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG42 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG42 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG43 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG43 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG18 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG19 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG42 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG42 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG42 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG42 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG17 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG40 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG52 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG24 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG24 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG52 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG52 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG42 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG42 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG43 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG43 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG8 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG9 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG4 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG42 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG42 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG42 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG42 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG4 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG7 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG39 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG53 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG14 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG4 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG53 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG53 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG42 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG42 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG43 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG43 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG30 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG31 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG26 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG42 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG42 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG42 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG42 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG26 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG29 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG41 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG54 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG36 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG36 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG26 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG54 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG54 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
  · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG47 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG47 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG48 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG48 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG21 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG22 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG47 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG47 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG47 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG47 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
      · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG23 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG50 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
      · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG52 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG24 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG24 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG52 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG52 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG47 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG47 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG48 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG48 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG11 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG12 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG4 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG47 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG47 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG47 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG47 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
      · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG4 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG13 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG49 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
      · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG53 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG14 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
            rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG4 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG53 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG53 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht2a | ht2b | ht2c
      · -- G.natDegree < A.natDegree + E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- C.natDegree + G.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG47 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG47 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG48 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG48 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- C.natDegree + G.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG33 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG34 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- C.natDegree + G.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG26 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG47 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG47 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG47 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG47 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
      · -- G.natDegree = A.natDegree + E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- C.natDegree + G.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG26 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG35 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG51 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, by omega⟩)
      · -- G.natDegree > A.natDegree + E.natDegree
        rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht3a | ht3b | ht3c
        · -- E.natDegree < A.natDegree + C.natDegree
          rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG54 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG36 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG36 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
          · -- 2 * A.natDegree + C.natDegree > G.natDegree
            rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG25 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG26 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG54 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cCDEFG54 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailCDEFG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn (by omega)⟩)
end QuarticChamberExhaust810

end Max11DegreeRoutes
