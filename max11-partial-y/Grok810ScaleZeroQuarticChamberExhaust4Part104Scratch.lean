import Grok810ScaleZeroQuarticChamberDefs4Scratch

/-! # Cost-argmin chamber exhaust (4/4), `(8,10)` scale zero

The 1 live-letter sets with |S| ∈ {6}.  Each theorem runs the case tree
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
private theorem astra4zExhaustTailBCDEFG1
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : a + 2 * b = 2 * c ∧
      c + f < a + 3 * b ∧
      2 * c + 2 * g < 3 * a + 6 * b ∧
      4 * d < a + 6 * b ∧
      4 * e < 3 * a + 6 * b) :
    a + 2 * b = 2 * c ∧
    a + 2 * b = 2 * c ∧
    a + 2 * b = 2 * c ∧
    2 * f < a + 4 * b ∧
    g < a + 2 * b ∧
    c + f < a + 3 * b ∧
    2 * c + 2 * g < 3 * a + 6 * b ∧
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
    2 * e < 3 * a + 2 * b ∧
    2 * c + 2 * d < 3 * a + 4 * b ∧
    c + e < 2 * a + 2 * b ∧
    2 * c + d < 2 * a + 3 * b ∧
    4 * c + 2 * e < 5 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEFG100
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : g = 2 * c ∧
      a + 2 * f < 2 * g ∧
      a + 2 * d < c + g ∧
      2 * e < c + g ∧
      a + 2 * b + 2 * c < 2 * g) :
    g = 2 * c ∧
    a + b + f < c + g ∧
    a + 2 * b < 2 * c ∧
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
private theorem astra4zExhaustTailBCDEFG111
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : b + f < 2 * d ∧
      2 * b + 2 * g < a + 4 * d ∧
      2 * c + 2 * f < a + 4 * d ∧
      c + g < a + 2 * d ∧
      2 * e < a + 2 * d ∧
      f < a + d ∧
      2 * g < 3 * a + 2 * d ∧
      a + 6 * b < 4 * d ∧
      3 * c < a + 2 * d) :
    b + f < 2 * d ∧
    2 * b + 2 * g < a + 4 * d ∧
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
private theorem astra4zExhaustTailBCDEFG114
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : a + 2 * d = 3 * c ∧
      2 * c + 2 * f < a + 4 * d ∧
      c + g < a + 2 * d ∧
      2 * e < a + 2 * d ∧
      2 * b + 4 * c < a + 4 * d) :
    a + 2 * d = 3 * c ∧
    b + f < 2 * d ∧
    2 * b + 2 * g < a + 4 * d ∧
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
    a + 6 * b < 4 * d ∧
    2 * b + c < 2 * d ∧
    4 * b < a + 2 * d ∧
    2 * b + e < a + 2 * d ∧
    2 * b + 4 * c < a + 4 * d ∧
    b + c < a + d ∧
    2 * b + 2 * c + 2 * e < 3 * a + 4 * d ∧
    4 * c < 3 * a + 2 * d ∧
    2 * c + e < 2 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEFG118
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : a + 2 * d = 2 * e ∧
      b + f < 2 * d ∧
      2 * b + 2 * g < a + 4 * d ∧
      2 * c + 2 * f < a + 4 * d ∧
      c + g < a + 2 * d ∧
      2 * e + 2 * f < 3 * a + 4 * d ∧
      e + g < 2 * a + 2 * d ∧
      a + 6 * b < 4 * d ∧
      3 * c < a + 2 * d) :
    a + 2 * d = 2 * e ∧
    a + 2 * d = 2 * e ∧
    b + f < 2 * d ∧
    2 * b + 2 * g < a + 4 * d ∧
    2 * c + 2 * f < a + 4 * d ∧
    c + g < a + 2 * d ∧
    f < a + d ∧
    2 * g < 3 * a + 2 * d ∧
    2 * e + 2 * f < 3 * a + 4 * d ∧
    e + g < 2 * a + 2 * d ∧
    f < a + d ∧
    2 * f + 2 * g < 5 * a + 4 * d ∧
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
private theorem astra4zExhaustTailBCDEFG121
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : a + 2 * d = 2 * e ∧
      a + 2 * d = 3 * c ∧
      2 * c + 2 * f < a + 4 * d ∧
      c + g < a + 2 * d ∧
      2 * b + 4 * c < a + 4 * d) :
    a + 2 * d = 2 * e ∧
    a + 2 * d = 2 * e ∧
    a + 2 * d = 3 * c ∧
    b + f < 2 * d ∧
    2 * b + 2 * g < a + 4 * d ∧
    2 * c + 2 * f < a + 4 * d ∧
    c + g < a + 2 * d ∧
    f < a + d ∧
    2 * g < 3 * a + 2 * d ∧
    2 * e + 2 * f < 3 * a + 4 * d ∧
    e + g < 2 * a + 2 * d ∧
    f < a + d ∧
    2 * f + 2 * g < 5 * a + 4 * d ∧
    2 * g < 3 * a + 2 * d ∧
    a + 6 * b < 4 * d ∧
    2 * b + c < 2 * d ∧
    4 * b < a + 2 * d ∧
    2 * b + e < a + 2 * d ∧
    2 * b + 4 * c < a + 4 * d ∧
    b + c < a + d ∧
    2 * b + 2 * c + 2 * e < 3 * a + 4 * d ∧
    4 * c < 3 * a + 2 * d ∧
    2 * c + e < 2 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEFG125
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : a + b + f < 2 * e ∧
      a + 2 * b + 2 * g < 4 * e ∧
      a + 2 * c + 2 * f < 4 * e ∧
      c + g < 2 * e ∧
      a + 2 * d < 2 * e ∧
      2 * f < a + 2 * e ∧
      g < a + e ∧
      3 * a + 6 * b < 4 * e ∧
      3 * c < 2 * e) :
    a + b + f < 2 * e ∧
    a + 2 * b + 2 * g < 4 * e ∧
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
private theorem astra4zExhaustTailBCDEFG132
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : 2 * a + b < f ∧
      3 * a + 2 * c < 2 * f ∧
      a + d < f ∧
      a + 2 * e < 2 * f ∧
      2 * g < a + 2 * f) :
    2 * a + b < f ∧
    3 * a + 2 * b + 2 * g < 4 * f ∧
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
    5 * a + 6 * b < 4 * f ∧
    2 * a + 2 * b + c < 2 * f ∧
    3 * a + 4 * b + 2 * d < 4 * f ∧
    a + 2 * b + e < 2 * f ∧
    3 * a + 2 * b + 4 * c < 4 * f ∧
    a + b + c + d < 2 * f ∧
    a + 2 * b + 2 * c + 2 * e < 4 * f ∧
    a + 3 * c < 2 * f ∧
    a + 4 * c + 2 * d < 4 * f ∧
    2 * c + e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEFG133
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : a + 2 * f = 2 * g ∧
      3 * a + 2 * b + 2 * g < 4 * f ∧
      a + c + g < 2 * f ∧
      a + 2 * d + 2 * g < 4 * f ∧
      e + g < 2 * f) :
    a + 2 * f = 2 * g ∧
    a + 2 * f = 2 * g ∧
    2 * a + b < f ∧
    3 * a + 2 * b + 2 * g < 4 * f ∧
    3 * a + 2 * c < 2 * f ∧
    a + c + g < 2 * f ∧
    a + d < f ∧
    3 * a + 2 * d + 2 * e < 4 * f ∧
    a + d < f ∧
    a + 2 * d + 2 * g < 4 * f ∧
    a + 2 * e < 2 * f ∧
    a + 2 * e < 2 * f ∧
    e + g < 2 * f ∧
    5 * a + 6 * b < 4 * f ∧
    2 * a + 2 * b + c < 2 * f ∧
    3 * a + 4 * b + 2 * d < 4 * f ∧
    a + 2 * b + e < 2 * f ∧
    3 * a + 2 * b + 4 * c < 4 * f ∧
    a + b + c + d < 2 * f ∧
    a + 2 * b + 2 * c + 2 * e < 4 * f ∧
    a + 3 * c < 2 * f ∧
    a + 4 * c + 2 * d < 4 * f ∧
    2 * c + e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEFG134
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : 5 * a + 2 * b < 2 * g ∧
      2 * a + c < g ∧
      3 * a + 2 * d < 2 * g ∧
      a + e < g ∧
      a + 2 * f < 2 * g) :
    3 * a + b + f < 2 * g ∧
    5 * a + 2 * b < 2 * g ∧
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
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEFG52
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : a + 2 * b = 2 * c ∧
      c + f < b + g ∧
      a + 4 * d < 2 * b + 2 * g ∧
      4 * e < a + 2 * b + 2 * g ∧
      2 * g < 5 * a + 2 * b ∧
      6 * c < a + 2 * b + 2 * g) :
    a + 2 * b = 2 * c ∧
    a + 2 * f < 2 * g ∧
    c + f < b + g ∧
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
private theorem astra4zExhaustTailBCDEFG53
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : g = 2 * c ∧
      a + 2 * b + 2 * g = 6 * c ∧
      c + f < b + g ∧
      a + 4 * d < 2 * b + 2 * g ∧
      4 * e < a + 2 * b + 2 * g) :
    a + 2 * b = 2 * c ∧
    g = a + 2 * b ∧
    2 * g = a + 2 * b + 2 * c ∧
    g = 2 * c ∧
    a + 2 * b + 2 * g = 6 * c ∧
    a + 2 * f < 2 * g ∧
    c + f < b + g ∧
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
    2 * b + 2 * e < a + 2 * g ∧
    2 * c + 2 * d < a + 2 * g ∧
    c + e < a + g ∧
    2 * c + d < a + b + g ∧
    4 * c + 2 * e < 3 * a + 2 * b + 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEFG74
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : a + 2 * f < 4 * c ∧
      g < 2 * c ∧
      a + 2 * d < 3 * c ∧
      2 * e < 3 * c ∧
      a + 2 * b < 2 * c) :
    a + b + f < 3 * c ∧
    a + 2 * b + 2 * g < 6 * c ∧
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
private theorem astra4zExhaustTailBCDEFG75
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : a + 2 * b < 2 * c ∧
      2 * g < a + 2 * f ∧
      a + 4 * d < 2 * c + 2 * f ∧
      4 * e < a + 2 * c + 2 * f ∧
      2 * f < 3 * a + 2 * c ∧
      4 * c < a + 2 * f) :
    a + 2 * b < 2 * c ∧
    b + g < c + f ∧
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
    a + 3 * b < c + f ∧
    a + 4 * b < 2 * f ∧
    2 * b + d < c + f ∧
    4 * b + 2 * e < a + 2 * c + 2 * f ∧
    b + c < f ∧
    2 * b + 2 * d < a + 2 * f ∧
    b + e < a + f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEFG76
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : a + 2 * f = 4 * c ∧
      2 * g < a + 2 * f ∧
      a + 4 * d < 2 * c + 2 * f ∧
      4 * e < a + 2 * c + 2 * f ∧
      b + c < f) :
    a + 2 * f = 4 * c ∧
    a + 2 * b < 2 * c ∧
    b + g < c + f ∧
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
    a + 3 * b < c + f ∧
    a + 4 * b < 2 * f ∧
    2 * b + d < c + f ∧
    4 * b + 2 * e < a + 2 * c + 2 * f ∧
    b + c < f ∧
    2 * b + 2 * d < a + 2 * f ∧
    b + e < a + f ∧
    c + d < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEFG77
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : a + 2 * f = 2 * g ∧
      b + g < c + f ∧
      a + 4 * d < 2 * c + 2 * f ∧
      4 * e < a + 2 * c + 2 * f ∧
      4 * g < 5 * a + 2 * c + 2 * f ∧
      4 * c < a + 2 * f) :
    a + 2 * f = 2 * g ∧
    a + 2 * b < 2 * c ∧
    b + g < c + f ∧
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
    a + 3 * b < c + f ∧
    a + 4 * b < 2 * f ∧
    2 * b + d < c + f ∧
    4 * b + 2 * e < a + 2 * c + 2 * f ∧
    b + c < f ∧
    2 * b + 2 * d < a + 2 * f ∧
    b + e < a + f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEFG78
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : a + 2 * f = 2 * g ∧
      a + 2 * f = 4 * c ∧
      a + 4 * d < 2 * c + 2 * f ∧
      4 * e < a + 2 * c + 2 * f ∧
      b + c < f) :
    a + 2 * f = 2 * g ∧
    a + 2 * f = 4 * c ∧
    a + 2 * b < 2 * c ∧
    b + g < c + f ∧
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
    a + 3 * b < c + f ∧
    a + 4 * b < 2 * f ∧
    2 * b + d < c + f ∧
    4 * b + 2 * e < a + 2 * c + 2 * f ∧
    b + c < f ∧
    2 * b + 2 * d < a + 2 * f ∧
    b + e < a + f ∧
    c + d < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEFG88
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : 2 * a + c = g ∧
      5 * a + 2 * c + 2 * f = 4 * g ∧
      b + g < c + f ∧
      d + g < a + c + f ∧
      2 * e + 2 * g < 3 * a + 2 * c + 2 * f) :
    a + 2 * f = 2 * g ∧
    3 * a + 2 * c = 2 * f ∧
    2 * a + c = g ∧
    5 * a + 2 * c + 2 * f = 4 * g ∧
    a + 2 * b < 2 * c ∧
    b + g < c + f ∧
    a + 4 * d < 2 * c + 2 * f ∧
    d + e < c + f ∧
    2 * d < a + 2 * c ∧
    d + g < a + c + f ∧
    4 * e < a + 2 * c + 2 * f ∧
    e < a + c ∧
    2 * e + 2 * g < 3 * a + 2 * c + 2 * f ∧
    a + 3 * b < c + f ∧
    a + 4 * b < 2 * f ∧
    2 * b + d < c + f ∧
    4 * b + 2 * e < a + 2 * c + 2 * f ∧
    b + c < f ∧
    2 * b + 2 * d < a + 2 * f ∧
    b + e < a + f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEFG98
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : 3 * a + 2 * c = 2 * f ∧
      a + 2 * b < 2 * c ∧
      2 * d < a + 2 * c ∧
      e < a + c ∧
      4 * g < 5 * a + 2 * c + 2 * f) :
    3 * a + 2 * c = 2 * f ∧
    a + 2 * b < 2 * c ∧
    b + g < c + f ∧
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
    a + 3 * b < c + f ∧
    a + 4 * b < 2 * f ∧
    2 * b + d < c + f ∧
    4 * b + 2 * e < a + 2 * c + 2 * f ∧
    b + c < f ∧
    2 * b + 2 * d < a + 2 * f ∧
    b + e < a + f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEFG99
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : a + 2 * b < 2 * c ∧
      a + 2 * f < 2 * g ∧
      a + 2 * d < c + g ∧
      2 * e < c + g ∧
      g < 2 * a + c ∧
      2 * c < g) :
    a + b + f < c + g ∧
    a + 2 * b < 2 * c ∧
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
/-- Cost-argmin subtree on the three comparison branches `122`. -/
private theorem chamberExhaustBCDEFGPath122
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0b : (2 * C.natDegree) = (A.natDegree + 2 * B.natDegree))
    (ht1c : (A.natDegree + 2 * D.natDegree) < (2 * E.natDegree))
    (ht2c : (A.natDegree + 2 * F.natDegree) < (2 * G.natDegree)) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht3a | ht3b | ht3c
  · -- G.natDegree < A.natDegree + E.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
      · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG125 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG127 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG60 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG61 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG53 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG125 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG125 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
  · -- G.natDegree = A.natDegree + E.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht5a | ht5b | ht5c
      · exact (by omega : False).elim
      · exact (by omega : False).elim
      · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG53 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG62 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG131 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
  · -- G.natDegree > A.natDegree + E.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG134 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG63 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
      · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG53 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG134 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG134 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
end QuarticChamberExhaust810

end Max11DegreeRoutes
/-! # Cost-argmin chamber exhaust (4/4), `(8,10)` scale zero

The 1 live-letter sets with |S| ∈ {6}.  Each theorem runs the case tree
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
/-- Cost-argmin subtree on the three comparison branches `200`. -/
private theorem chamberExhaustBCDEFGPath200
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0c : (A.natDegree + 2 * B.natDegree) < (2 * C.natDegree))
    (ht1a : (2 * E.natDegree) < (A.natDegree + 2 * D.natDegree))
    (ht2a : (2 * G.natDegree) < (A.natDegree + 2 * F.natDegree)) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht3a | ht3b | ht3c
  · -- F.natDegree < A.natDegree + D.natDegree
    rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
      · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG111 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG114 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG114 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG89 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG90 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG75 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG76 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG76 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG111 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG111 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
  · -- F.natDegree = A.natDegree + D.natDegree
    rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
      · exact (by omega : False).elim
      · exact (by omega : False).elim
      · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG75 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG76 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG76 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG94 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG123 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
  · -- F.natDegree > A.natDegree + D.natDegree
    rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG132 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG98 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG98 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG75 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG76 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG76 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG132 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG132 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
end QuarticChamberExhaust810

end Max11DegreeRoutes
/-! # Cost-argmin chamber exhaust (4/4), `(8,10)` scale zero

The 1 live-letter sets with |S| ∈ {6}.  Each theorem runs the case tree
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
/-- Cost-argmin subtree on the three comparison branches `201`. -/
private theorem chamberExhaustBCDEFGPath201
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0c : (A.natDegree + 2 * B.natDegree) < (2 * C.natDegree))
    (ht1a : (2 * E.natDegree) < (A.natDegree + 2 * D.natDegree))
    (ht2b : (2 * G.natDegree) = (A.natDegree + 2 * F.natDegree)) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht3a | ht3b | ht3c
  · -- F.natDegree < A.natDegree + D.natDegree
    rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
      · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG111 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG114 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG114 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG79 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG80 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG77 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG78 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG78 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG111 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG111 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
  · -- F.natDegree = A.natDegree + D.natDegree
    rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
      · exact (by omega : False).elim
      · exact (by omega : False).elim
      · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG77 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG78 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG78 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG84 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG122 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
  · -- F.natDegree > A.natDegree + D.natDegree
    rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG133 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG88 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG88 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG77 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG78 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG78 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG133 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG133 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
end QuarticChamberExhaust810

end Max11DegreeRoutes
/-! # Cost-argmin chamber exhaust (4/4), `(8,10)` scale zero

The 1 live-letter sets with |S| ∈ {6}.  Each theorem runs the case tree
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
/-- Cost-argmin subtree on the three comparison branches `202`. -/
private theorem chamberExhaustBCDEFGPath202
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0c : (A.natDegree + 2 * B.natDegree) < (2 * C.natDegree))
    (ht1a : (2 * E.natDegree) < (A.natDegree + 2 * D.natDegree))
    (ht2c : (A.natDegree + 2 * F.natDegree) < (2 * G.natDegree)) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
  · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
      · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG111 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG114 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG114 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG101 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG102 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG99 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG100 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG100 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG111 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG111 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
  · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht5a | ht5b | ht5c
      · exact (by omega : False).elim
      · exact (by omega : False).elim
      · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG99 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG100 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG100 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG106 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG124 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
  · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht5a | ht5b | ht5c
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG134 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG110 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
      · -- 2 * A.natDegree + C.natDegree > G.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG99 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG99 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG100 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG100 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG134 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG134 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
end QuarticChamberExhaust810

end Max11DegreeRoutes
/-! # Cost-argmin chamber exhaust (4/4), `(8,10)` scale zero

The 1 live-letter sets with |S| ∈ {6}.  Each theorem runs the case tree
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
/-- Cost-argmin subtree on the three comparison branches `210`. -/
private theorem chamberExhaustBCDEFGPath210
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0c : (A.natDegree + 2 * B.natDegree) < (2 * C.natDegree))
    (ht1b : (2 * E.natDegree) = (A.natDegree + 2 * D.natDegree))
    (ht2a : (2 * G.natDegree) < (A.natDegree + 2 * F.natDegree)) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht3a | ht3b | ht3c
  · -- F.natDegree < A.natDegree + D.natDegree
    rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
      · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG118 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG121 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG121 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG92 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG93 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG75 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG76 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG76 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG118 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG118 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
  · -- F.natDegree = A.natDegree + D.natDegree
    rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
      · exact (by omega : False).elim
      · exact (by omega : False).elim
      · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG75 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG76 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG76 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG91 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG116 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
  · -- F.natDegree > A.natDegree + D.natDegree
    rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG132 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG98 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG98 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG75 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG75 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG76 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG76 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG132 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG132 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
end QuarticChamberExhaust810

end Max11DegreeRoutes
/-! # Cost-argmin chamber exhaust (4/4), `(8,10)` scale zero

The 1 live-letter sets with |S| ∈ {6}.  Each theorem runs the case tree
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
/-- Cost-argmin subtree on the three comparison branches `211`. -/
private theorem chamberExhaustBCDEFGPath211
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0c : (A.natDegree + 2 * B.natDegree) < (2 * C.natDegree))
    (ht1b : (2 * E.natDegree) = (A.natDegree + 2 * D.natDegree))
    (ht2b : (2 * G.natDegree) = (A.natDegree + 2 * F.natDegree)) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht3a | ht3b | ht3c
  · -- F.natDegree < A.natDegree + D.natDegree
    rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
      · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG118 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG121 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG121 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG82 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG83 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG77 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG78 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG78 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG118 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG118 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
  · -- F.natDegree = A.natDegree + D.natDegree
    rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
      · exact (by omega : False).elim
      · exact (by omega : False).elim
      · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG77 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG78 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG78 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG81 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG115 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
  · -- F.natDegree > A.natDegree + D.natDegree
    rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
      rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht5a | ht5b | ht5c
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG133 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG88 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG88 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG77 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG77 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG78 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG78 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG74 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG74 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG133 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG133 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
end QuarticChamberExhaust810

end Max11DegreeRoutes
