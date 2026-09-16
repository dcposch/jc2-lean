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
private theorem astra4zExhaustTailBDEFG0
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hs : 2 * f < a + 4 * b ∧
      g < a + 2 * b ∧
      4 * d < a + 6 * b ∧
      4 * e < 3 * a + 6 * b) :
    2 * f < a + 4 * b ∧
    g < a + 2 * b ∧
    4 * d < a + 6 * b ∧
    d + e < a + 3 * b ∧
    2 * d + 2 * f < 3 * a + 6 * b ∧
    d + g < 2 * a + 3 * b ∧
    4 * e < 3 * a + 6 * b ∧
    e + f < 2 * a + 3 * b ∧
    2 * e + 2 * g < 5 * a + 6 * b ∧
    4 * f < 5 * a + 6 * b ∧
    f + g < 3 * a + 3 * b ∧
    4 * g < 7 * a + 6 * b ∧
    d < a + b ∧
    2 * e < 3 * a + 2 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEFG1
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hs : 2 * g < a + 2 * f ∧
      2 * d < b + f ∧
      2 * e < a + b + f ∧
      f < 2 * a + b ∧
      a + 4 * b < 2 * f) :
    2 * g < a + 2 * f ∧
    2 * d < b + f ∧
    2 * d + 2 * e < a + 2 * b + 2 * f ∧
    d < a + b ∧
    2 * d + 2 * g < 3 * a + 2 * b + 2 * f ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    e + g < 2 * a + b + f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    a + 4 * b < 2 * f ∧
    2 * b + 2 * d < a + 2 * f ∧
    b + e < a + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEFG14
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hs : 5 * a + 2 * b = 2 * g ∧
      3 * a + b + f = 2 * g ∧
      2 * d + 2 * g < 3 * a + 2 * b + 2 * f ∧
      e + g < 2 * a + b + f) :
    a + 2 * f = 2 * g ∧
    2 * a + b = f ∧
    5 * a + 2 * b = 2 * g ∧
    3 * a + b + f = 2 * g ∧
    2 * d < b + f ∧
    2 * d + 2 * e < a + 2 * b + 2 * f ∧
    d < a + b ∧
    2 * d + 2 * g < 3 * a + 2 * b + 2 * f ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    e + g < 2 * a + b + f ∧
    a + 4 * b < 2 * f ∧
    2 * b + 2 * d < a + 2 * f ∧
    b + e < a + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEFG2
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hs : 2 * f = a + 4 * b ∧
      2 * g < a + 2 * f ∧
      2 * d < b + f ∧
      2 * e < a + b + f) :
    2 * f = a + 4 * b ∧
    2 * g < a + 2 * f ∧
    2 * d < b + f ∧
    2 * d + 2 * e < a + 2 * b + 2 * f ∧
    d < a + b ∧
    2 * d + 2 * g < 3 * a + 2 * b + 2 * f ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    e + g < 2 * a + b + f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    2 * b + 2 * d < a + 2 * f ∧
    b + e < a + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEFG24
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hs : 2 * a + b = f ∧
      d < a + b ∧
      2 * e < 3 * a + 2 * b ∧
      2 * g < 3 * a + b + f) :
    2 * a + b = f ∧
    2 * g < a + 2 * f ∧
    2 * d < b + f ∧
    2 * d + 2 * e < a + 2 * b + 2 * f ∧
    d < a + b ∧
    2 * d + 2 * g < 3 * a + 2 * b + 2 * f ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    e + g < 2 * a + b + f ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    a + 4 * b < 2 * f ∧
    2 * b + 2 * d < a + 2 * f ∧
    b + e < a + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEFG25
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hs : a + 2 * f < 2 * g ∧
      a + 4 * d < 2 * b + 2 * g ∧
      4 * e < a + 2 * b + 2 * g ∧
      2 * g < 5 * a + 2 * b ∧
      a + 2 * b < g) :
    a + 2 * f < 2 * g ∧
    a + 4 * d < 2 * b + 2 * g ∧
    d + e < b + g ∧
    2 * d + 2 * f < a + 2 * b + 2 * g ∧
    d < a + b ∧
    4 * e < a + 2 * b + 2 * g ∧
    e + f < a + b + g ∧
    2 * e < 3 * a + 2 * b ∧
    4 * f < 3 * a + 2 * b + 2 * g ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    a + 2 * b < g ∧
    b + d < g ∧
    2 * b + 2 * e < a + 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEFG26
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hs : g = a + 2 * b ∧
      a + 2 * f < 2 * g ∧
      a + 4 * d < 2 * b + 2 * g ∧
      4 * e < a + 2 * b + 2 * g) :
    g = a + 2 * b ∧
    a + 2 * f < 2 * g ∧
    a + 4 * d < 2 * b + 2 * g ∧
    d + e < b + g ∧
    2 * d + 2 * f < a + 2 * b + 2 * g ∧
    d < a + b ∧
    4 * e < a + 2 * b + 2 * g ∧
    e + f < a + b + g ∧
    2 * e < 3 * a + 2 * b ∧
    4 * f < 3 * a + 2 * b + 2 * g ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    b + d < g ∧
    2 * b + 2 * e < a + 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEFG3
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hs : a + 2 * f = 2 * g ∧
      2 * d < b + f ∧
      2 * e < a + b + f ∧
      2 * g < 3 * a + b + f ∧
      a + 4 * b < 2 * f) :
    a + 2 * f = 2 * g ∧
    2 * d < b + f ∧
    2 * d + 2 * e < a + 2 * b + 2 * f ∧
    d < a + b ∧
    2 * d + 2 * g < 3 * a + 2 * b + 2 * f ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    e + g < 2 * a + b + f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    a + 4 * b < 2 * f ∧
    2 * b + 2 * d < a + 2 * f ∧
    b + e < a + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEFG36
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hs : 5 * a + 2 * b = 2 * g ∧
      d < a + b ∧
      2 * e < 3 * a + 2 * b ∧
      f < 2 * a + b) :
    5 * a + 2 * b = 2 * g ∧
    a + 2 * f < 2 * g ∧
    a + 4 * d < 2 * b + 2 * g ∧
    d + e < b + g ∧
    2 * d + 2 * f < a + 2 * b + 2 * g ∧
    d < a + b ∧
    4 * e < a + 2 * b + 2 * g ∧
    e + f < a + b + g ∧
    2 * e < 3 * a + 2 * b ∧
    4 * f < 3 * a + 2 * b + 2 * g ∧
    f < 2 * a + b ∧
    a + 2 * b < g ∧
    b + d < g ∧
    2 * b + 2 * e < a + 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEFG37
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hs : b + f < 2 * d ∧
      2 * b + 2 * g < a + 4 * d ∧
      2 * e < a + 2 * d ∧
      f < a + d ∧
      2 * g < 3 * a + 2 * d ∧
      a + 6 * b < 4 * d) :
    b + f < 2 * d ∧
    2 * b + 2 * g < a + 4 * d ∧
    2 * e < a + 2 * d ∧
    f < a + d ∧
    2 * g < 3 * a + 2 * d ∧
    2 * e < a + 2 * d ∧
    2 * e + 2 * f < 3 * a + 4 * d ∧
    e + g < 2 * a + 2 * d ∧
    f < a + d ∧
    2 * f + 2 * g < 5 * a + 4 * d ∧
    2 * g < 3 * a + 2 * d ∧
    a + 6 * b < 4 * d ∧
    4 * b < a + 2 * d ∧
    2 * b + e < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEFG38
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hs : 4 * d = a + 6 * b ∧
      b + f < 2 * d ∧
      2 * b + 2 * g < a + 4 * d ∧
      2 * e < a + 2 * d) :
    4 * d = a + 6 * b ∧
    b + f < 2 * d ∧
    2 * b + 2 * g < a + 4 * d ∧
    2 * e < a + 2 * d ∧
    f < a + d ∧
    2 * g < 3 * a + 2 * d ∧
    2 * e < a + 2 * d ∧
    2 * e + 2 * f < 3 * a + 4 * d ∧
    e + g < 2 * a + 2 * d ∧
    f < a + d ∧
    2 * f + 2 * g < 5 * a + 4 * d ∧
    2 * g < 3 * a + 2 * d ∧
    4 * b < a + 2 * d ∧
    2 * b + e < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEFG4
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hs : a + 2 * f = 2 * g ∧
      2 * f = a + 4 * b ∧
      2 * d < b + f ∧
      2 * e < a + b + f) :
    a + 2 * f = 2 * g ∧
    2 * f = a + 4 * b ∧
    2 * d < b + f ∧
    2 * d + 2 * e < a + 2 * b + 2 * f ∧
    d < a + b ∧
    2 * d + 2 * g < 3 * a + 2 * b + 2 * f ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    e + g < 2 * a + b + f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    2 * b + 2 * d < a + 2 * f ∧
    b + e < a + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEFG42
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hs : a + 2 * d = 2 * e ∧
      b + f < 2 * d ∧
      2 * b + 2 * g < a + 4 * d ∧
      2 * e + 2 * f < 3 * a + 4 * d ∧
      e + g < 2 * a + 2 * d ∧
      a + 6 * b < 4 * d) :
    a + 2 * d = 2 * e ∧
    a + 2 * d = 2 * e ∧
    b + f < 2 * d ∧
    2 * b + 2 * g < a + 4 * d ∧
    f < a + d ∧
    2 * g < 3 * a + 2 * d ∧
    2 * e + 2 * f < 3 * a + 4 * d ∧
    e + g < 2 * a + 2 * d ∧
    f < a + d ∧
    2 * f + 2 * g < 5 * a + 4 * d ∧
    2 * g < 3 * a + 2 * d ∧
    a + 6 * b < 4 * d ∧
    4 * b < a + 2 * d ∧
    2 * b + e < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEFG43
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hs : a + 2 * d = 2 * e ∧
      4 * d = a + 6 * b ∧
      b + f < 2 * d ∧
      2 * b + 2 * g < a + 4 * d) :
    a + 2 * d = 2 * e ∧
    a + 2 * d = 2 * e ∧
    4 * d = a + 6 * b ∧
    b + f < 2 * d ∧
    2 * b + 2 * g < a + 4 * d ∧
    f < a + d ∧
    2 * g < 3 * a + 2 * d ∧
    2 * e + 2 * f < 3 * a + 4 * d ∧
    e + g < 2 * a + 2 * d ∧
    f < a + d ∧
    2 * f + 2 * g < 5 * a + 4 * d ∧
    2 * g < 3 * a + 2 * d ∧
    4 * b < a + 2 * d ∧
    2 * b + e < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEFG47
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hs : a + b + f < 2 * e ∧
      a + 2 * b + 2 * g < 4 * e ∧
      a + 2 * d < 2 * e ∧
      2 * f < a + 2 * e ∧
      g < a + e ∧
      3 * a + 6 * b < 4 * e) :
    a + b + f < 2 * e ∧
    a + 2 * b + 2 * g < 4 * e ∧
    a + 2 * d < 2 * e ∧
    a + 2 * d < 2 * e ∧
    d + f < 2 * e ∧
    2 * d + 2 * g < a + 4 * e ∧
    2 * f < a + 2 * e ∧
    g < a + e ∧
    2 * f < a + 2 * e ∧
    2 * f + 2 * g < 3 * a + 4 * e ∧
    g < a + e ∧
    3 * a + 6 * b < 4 * e ∧
    a + 4 * b + 2 * d < 4 * e ∧
    2 * b < e := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEFG48
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hs : 4 * e = 3 * a + 6 * b ∧
      a + b + f < 2 * e ∧
      a + 2 * b + 2 * g < 4 * e ∧
      a + 2 * d < 2 * e) :
    4 * e = 3 * a + 6 * b ∧
    a + b + f < 2 * e ∧
    a + 2 * b + 2 * g < 4 * e ∧
    a + 2 * d < 2 * e ∧
    a + 2 * d < 2 * e ∧
    d + f < 2 * e ∧
    2 * d + 2 * g < a + 4 * e ∧
    2 * f < a + 2 * e ∧
    g < a + e ∧
    2 * f < a + 2 * e ∧
    2 * f + 2 * g < 3 * a + 4 * e ∧
    g < a + e ∧
    a + 4 * b + 2 * d < 4 * e ∧
    2 * b < e := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEFG52
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hs : 2 * a + b < f ∧
      a + d < f ∧
      a + 2 * e < 2 * f ∧
      2 * g < a + 2 * f) :
    2 * a + b < f ∧
    3 * a + 2 * b + 2 * g < 4 * f ∧
    a + d < f ∧
    3 * a + 2 * d + 2 * e < 4 * f ∧
    a + d < f ∧
    a + 2 * d + 2 * g < 4 * f ∧
    a + 2 * e < 2 * f ∧
    a + 2 * e < 2 * f ∧
    e + g < 2 * f ∧
    2 * g < a + 2 * f ∧
    2 * g < a + 2 * f ∧
    5 * a + 6 * b < 4 * f ∧
    3 * a + 4 * b + 2 * d < 4 * f ∧
    a + 2 * b + e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEFG53
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hs : a + 2 * f = 2 * g ∧
      3 * a + 2 * b + 2 * g < 4 * f ∧
      a + 2 * d + 2 * g < 4 * f ∧
      e + g < 2 * f) :
    a + 2 * f = 2 * g ∧
    a + 2 * f = 2 * g ∧
    2 * a + b < f ∧
    3 * a + 2 * b + 2 * g < 4 * f ∧
    a + d < f ∧
    3 * a + 2 * d + 2 * e < 4 * f ∧
    a + d < f ∧
    a + 2 * d + 2 * g < 4 * f ∧
    a + 2 * e < 2 * f ∧
    a + 2 * e < 2 * f ∧
    e + g < 2 * f ∧
    5 * a + 6 * b < 4 * f ∧
    3 * a + 4 * b + 2 * d < 4 * f ∧
    a + 2 * b + e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEFG54
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hs : 5 * a + 2 * b < 2 * g ∧
      3 * a + 2 * d < 2 * g ∧
      a + e < g ∧
      a + 2 * f < 2 * g) :
    3 * a + b + f < 2 * g ∧
    5 * a + 2 * b < 2 * g ∧
    3 * a + 2 * d < 2 * g ∧
    5 * a + 2 * d + 2 * e < 4 * g ∧
    2 * a + d + f < 2 * g ∧
    3 * a + 2 * d < 2 * g ∧
    a + e < g ∧
    3 * a + 2 * e + 2 * f < 4 * g ∧
    a + e < g ∧
    a + 2 * f < 2 * g ∧
    a + 2 * f < 2 * g ∧
    7 * a + 6 * b < 4 * g ∧
    5 * a + 4 * b + 2 * d < 4 * g ∧
    2 * a + 2 * b + e < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BDEFG`. -/
theorem quarticChamberSupport810_of_live_BDEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCz : C = 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG37 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG37 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG38 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG15 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG16 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG37 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG37 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG37 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG37 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG20 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG45 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG52 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG24 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG24 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG52 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG52 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG37 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG37 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG38 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG5 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG6 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG4 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG37 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG37 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG37 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG37 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG4 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG10 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG44 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG53 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG14 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG4 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG53 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG53 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG37 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG37 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG38 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG38 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG27 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG28 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG26 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG37 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG37 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG37 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG37 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG26 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG32 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG46 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG54 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG36 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG36 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG26 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG54 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG54 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
  · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG42 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG42 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG43 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG43 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG18 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG19 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG42 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG42 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG42 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG42 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG17 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG40 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG52 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG24 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG24 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG52 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG52 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · -- F.natDegree < A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · -- B.natDegree + F.natDegree < 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG42 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG42 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG43 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG43 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- B.natDegree + F.natDegree = 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG8 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG9 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG4 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG42 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG42 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG42 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG42 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
      · -- F.natDegree = A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- B.natDegree + F.natDegree > 2 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG4 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG7 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG39 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · -- F.natDegree > A.natDegree + D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG53 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG14 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG4 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG53 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG53 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG42 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG42 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG43 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG43 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG30 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG31 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG26 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG42 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG42 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG42 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG42 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
      · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG26 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG29 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG41 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht3a | ht3b | ht3c
        · -- D.natDegree < A.natDegree + B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG54 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG36 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG36 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG26 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG54 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG54 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
  · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG47 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG47 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG48 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG48 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG21 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG22 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG47 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG47 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG47 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG47 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
      · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG23 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG50 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG52 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG24 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG24 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG52 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG52 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG47 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG47 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG48 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG48 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG11 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG12 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG4 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG47 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG47 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG47 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG47 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
      · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG4 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG13 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG49 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG53 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG14 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- 2 * A.natDegree + B.natDegree > F.natDegree
            rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG4 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG53 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG53 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht2a | ht2b | ht2c
      · -- G.natDegree < A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG47 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG47 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG48 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG48 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
            rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG33 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG34 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG26 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG47 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG47 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG47 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG47 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
      · -- G.natDegree = A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact (by omega : False).elim
          · exact (by omega : False).elim
          · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG26 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG35 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG51 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · -- G.natDegree > A.natDegree + E.natDegree
        rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
          rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG54 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG36 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG36 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
          · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
            rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG25 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG26 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
            · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG54 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
        · exact QuarticChamberSupport810.size5 (QuarticChamberSupportSize5810.cBDEFG54 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailBDEFG54 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn (by omega)⟩)
end QuarticChamberExhaust810

end Max11DegreeRoutes
