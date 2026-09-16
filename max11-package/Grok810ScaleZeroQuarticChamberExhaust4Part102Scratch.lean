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
private theorem astra4zExhaustTailBCDEFG0
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : 2 * f < a + 4 * b ∧
      g < a + 2 * b ∧
      4 * d < a + 6 * b ∧
      4 * e < 3 * a + 6 * b ∧
      2 * c < a + 2 * b) :
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
private theorem astra4zExhaustTailBCDEFG113
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : a + 4 * d = 2 * b + 4 * c ∧
      a + 2 * d = 3 * c ∧
      2 * c + 2 * f < a + 4 * d ∧
      c + g < a + 2 * d ∧
      2 * e < a + 2 * d) :
    4 * d = a + 6 * b ∧
    2 * d = 2 * b + c ∧
    a + 4 * d = 2 * b + 4 * c ∧
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
    4 * b < a + 2 * d ∧
    2 * b + e < a + 2 * d ∧
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
private theorem astra4zExhaustTailBCDEFG126
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : 4 * e = 3 * a + 6 * b ∧
      a + b + f < 2 * e ∧
      a + 2 * b + 2 * g < 4 * e ∧
      a + 2 * d < 2 * e ∧
      3 * c < 2 * e) :
    4 * e = 3 * a + 6 * b ∧
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
private theorem astra4zExhaustTailBCDEFG2
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : 2 * g < a + 2 * f ∧
      2 * c < a + 2 * b ∧
      2 * d < b + f ∧
      2 * e < a + b + f ∧
      f < 2 * a + b ∧
      a + 4 * b < 2 * f) :
    2 * g < a + 2 * f ∧
    2 * c < a + 2 * b ∧
    c + g < a + b + f ∧
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
    b + c < f ∧
    2 * b + 2 * d < a + 2 * f ∧
    b + e < a + f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f ∧
    3 * c < a + b + f ∧
    4 * c + 2 * d < 3 * a + 2 * b + 2 * f ∧
    2 * c + e < 2 * a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEFG28
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : a + 2 * b = 2 * c ∧
      c + g < a + b + f ∧
      2 * d < b + f ∧
      2 * e < a + b + f ∧
      f < 2 * a + b ∧
      3 * c < a + b + f) :
    a + 2 * b = 2 * c ∧
    2 * g < a + 2 * f ∧
    c + g < a + b + f ∧
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
    b + c < f ∧
    2 * b + 2 * d < a + 2 * f ∧
    b + e < a + f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f ∧
    3 * c < a + b + f ∧
    4 * c + 2 * d < 3 * a + 2 * b + 2 * f ∧
    2 * c + e < 2 * a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEFG29
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : a + 2 * f = 4 * c ∧
      a + b + f = 3 * c ∧
      c + g < a + b + f ∧
      2 * d < b + f ∧
      2 * e < a + b + f) :
    a + 2 * b = 2 * c ∧
    2 * f = a + 4 * b ∧
    f = b + c ∧
    a + 2 * f = 4 * c ∧
    a + b + f = 3 * c ∧
    2 * g < a + 2 * f ∧
    c + g < a + b + f ∧
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
    b + e < a + f ∧
    c + d < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f ∧
    4 * c + 2 * d < 3 * a + 2 * b + 2 * f ∧
    2 * c + e < 2 * a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEFG3
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : 2 * f = a + 4 * b ∧
      2 * g < a + 2 * f ∧
      2 * d < b + f ∧
      2 * e < a + b + f ∧
      3 * c < a + b + f) :
    2 * f = a + 4 * b ∧
    2 * g < a + 2 * f ∧
    2 * c < a + 2 * b ∧
    c + g < a + b + f ∧
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
    b + c < f ∧
    2 * b + 2 * d < a + 2 * f ∧
    b + e < a + f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f ∧
    3 * c < a + b + f ∧
    4 * c + 2 * d < 3 * a + 2 * b + 2 * f ∧
    2 * c + e < 2 * a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEFG4
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : a + 2 * f = 2 * g ∧
      c + g < a + b + f ∧
      2 * d < b + f ∧
      2 * e < a + b + f ∧
      2 * g < 3 * a + b + f ∧
      a + 4 * b < 2 * f) :
    a + 2 * f = 2 * g ∧
    2 * c < a + 2 * b ∧
    c + g < a + b + f ∧
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
    b + c < f ∧
    2 * b + 2 * d < a + 2 * f ∧
    b + e < a + f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f ∧
    3 * c < a + b + f ∧
    4 * c + 2 * d < 3 * a + 2 * b + 2 * f ∧
    2 * c + e < 2 * a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEFG5
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : a + 2 * f = 2 * g ∧
      2 * f = a + 4 * b ∧
      2 * d < b + f ∧
      2 * e < a + b + f ∧
      3 * c < a + b + f) :
    a + 2 * f = 2 * g ∧
    2 * f = a + 4 * b ∧
    2 * c < a + 2 * b ∧
    c + g < a + b + f ∧
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
    b + c < f ∧
    2 * b + 2 * d < a + 2 * f ∧
    b + e < a + f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f ∧
    3 * c < a + b + f ∧
    4 * c + 2 * d < 3 * a + 2 * b + 2 * f ∧
    2 * c + e < 2 * a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEFG50
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : a + 2 * f < 2 * g ∧
      2 * c < a + 2 * b ∧
      a + 4 * d < 2 * b + 2 * g ∧
      4 * e < a + 2 * b + 2 * g ∧
      2 * g < 5 * a + 2 * b ∧
      a + 2 * b < g) :
    a + 2 * f < 2 * g ∧
    c + f < b + g ∧
    2 * c < a + 2 * b ∧
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
private theorem astra4zExhaustTailBCDEFG51
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : g = a + 2 * b ∧
      a + 2 * f < 2 * g ∧
      a + 4 * d < 2 * b + 2 * g ∧
      4 * e < a + 2 * b + 2 * g ∧
      6 * c < a + 2 * b + 2 * g) :
    g = a + 2 * b ∧
    a + 2 * f < 2 * g ∧
    c + f < b + g ∧
    2 * c < a + 2 * b ∧
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
private theorem astra4zExhaustTailBCDEFG6
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : a + 2 * b = 2 * c ∧
      a + b + f = c + g ∧
      2 * d < b + f ∧
      2 * e < a + b + f ∧
      2 * g < 3 * a + b + f ∧
      3 * c < a + b + f) :
    a + 2 * f = 2 * g ∧
    a + 2 * b = 2 * c ∧
    a + b + f = c + g ∧
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
    b + c < f ∧
    2 * b + 2 * d < a + 2 * f ∧
    b + e < a + f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f ∧
    3 * c < a + b + f ∧
    4 * c + 2 * d < 3 * a + 2 * b + 2 * f ∧
    2 * c + e < 2 * a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDEFG7
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : a + b + f = c + g ∧
      a + 2 * f = 4 * c ∧
      a + b + f = 3 * c ∧
      2 * d < b + f ∧
      2 * e < a + b + f) :
    a + 2 * f = 2 * g ∧
    a + 2 * b = 2 * c ∧
    a + b + f = c + g ∧
    2 * f = a + 4 * b ∧
    f = b + c ∧
    a + 2 * f = 4 * c ∧
    a + b + f = 3 * c ∧
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
    b + e < a + f ∧
    c + d < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f ∧
    4 * c + 2 * d < 3 * a + 2 * b + 2 * f ∧
    2 * c + e < 2 * a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Cost-argmin subtree on the three comparison branches `020`. -/
private theorem chamberExhaustBCDEFGPath020
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0a : (2 * C.natDegree) < (A.natDegree + 2 * B.natDegree))
    (ht1c : (A.natDegree + 2 * D.natDegree) < (2 * E.natDegree))
    (ht2a : (2 * G.natDegree) < (A.natDegree + 2 * F.natDegree)) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht3a | ht3b | ht3c
  · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
      · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG125 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG126 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG126 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG46 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG47 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG3 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG125 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG125 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
  · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
      · exact (by omega : False).elim
      · exact (by omega : False).elim
      · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG3 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG48 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG130 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
  · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG132 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG49 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
      · -- 2 * A.natDegree + B.natDegree > F.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG2 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG3 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
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
/-- Cost-argmin subtree on the three comparison branches `021`. -/
private theorem chamberExhaustBCDEFGPath021
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0a : (2 * C.natDegree) < (A.natDegree + 2 * B.natDegree))
    (ht1c : (A.natDegree + 2 * D.natDegree) < (2 * E.natDegree))
    (ht2b : (2 * G.natDegree) = (A.natDegree + 2 * F.natDegree)) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht3a | ht3b | ht3c
  · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
      · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG125 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG126 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG126 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG24 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG25 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG5 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG125 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG125 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG125 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
  · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht5a | ht5b | ht5c
      · exact (by omega : False).elim
      · exact (by omega : False).elim
      · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG5 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG26 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG129 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
  · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG133 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG27 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
      · -- 2 * A.natDegree + B.natDegree > F.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG4 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG5 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
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
/-- Cost-argmin subtree on the three comparison branches `022`. -/
private theorem chamberExhaustBCDEFGPath022
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0a : (2 * C.natDegree) < (A.natDegree + 2 * B.natDegree))
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
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG126 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG126 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG70 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG71 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG50 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG51 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG51 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
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
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG50 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG51 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG51 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG72 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG131 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
  · -- G.natDegree > A.natDegree + E.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht5a | ht5b | ht5c
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG134 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG134 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG73 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
      · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG50 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG50 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG51 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG51 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG0 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
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
/-- Cost-argmin subtree on the three comparison branches `100`. -/
private theorem chamberExhaustBCDEFGPath100
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0b : (2 * C.natDegree) = (A.natDegree + 2 * B.natDegree))
    (ht1a : (2 * E.natDegree) < (A.natDegree + 2 * D.natDegree))
    (ht2a : (2 * G.natDegree) < (A.natDegree + 2 * F.natDegree)) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht3a | ht3b | ht3c
  · -- F.natDegree < A.natDegree + D.natDegree
    rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
    · -- D.natDegree < A.natDegree + B.natDegree
      rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
      · -- B.natDegree + F.natDegree < 2 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG111 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG113 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG113 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- B.natDegree + F.natDegree = 2 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG30 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG31 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- B.natDegree + F.natDegree > 2 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG28 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG29 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG29 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG111 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG111 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
  · -- F.natDegree = A.natDegree + D.natDegree
    rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
    · -- D.natDegree < A.natDegree + B.natDegree
      rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
      · exact (by omega : False).elim
      · exact (by omega : False).elim
      · -- B.natDegree + F.natDegree > 2 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG28 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG29 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG29 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG35 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG123 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
  · -- F.natDegree > A.natDegree + D.natDegree
    rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
    · -- D.natDegree < A.natDegree + B.natDegree
      rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG132 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG39 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
      · -- 2 * A.natDegree + B.natDegree > F.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG28 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG29 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG29 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
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
/-- Cost-argmin subtree on the three comparison branches `101`. -/
private theorem chamberExhaustBCDEFGPath101
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0b : (2 * C.natDegree) = (A.natDegree + 2 * B.natDegree))
    (ht1a : (2 * E.natDegree) < (A.natDegree + 2 * D.natDegree))
    (ht2b : (2 * G.natDegree) = (A.natDegree + 2 * F.natDegree)) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht3a | ht3b | ht3c
  · -- F.natDegree < A.natDegree + D.natDegree
    rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
    · -- D.natDegree < A.natDegree + B.natDegree
      rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
      · -- B.natDegree + F.natDegree < 2 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG111 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG113 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG113 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- B.natDegree + F.natDegree = 2 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG8 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG9 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- B.natDegree + F.natDegree > 2 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG6 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG7 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG7 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG111 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG111 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
  · -- F.natDegree = A.natDegree + D.natDegree
    rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
    · -- D.natDegree < A.natDegree + B.natDegree
      rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht5a | ht5b | ht5c
      · exact (by omega : False).elim
      · exact (by omega : False).elim
      · -- B.natDegree + F.natDegree > 2 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG6 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG7 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG7 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG13 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG122 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
  · -- F.natDegree > A.natDegree + D.natDegree
    rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
    · -- D.natDegree < A.natDegree + B.natDegree
      rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG133 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG17 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
      · -- 2 * A.natDegree + B.natDegree > F.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG6 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG7 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG7 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
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
/-- Cost-argmin subtree on the three comparison branches `102`. -/
private theorem chamberExhaustBCDEFGPath102
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0b : (2 * C.natDegree) = (A.natDegree + 2 * B.natDegree))
    (ht1a : (2 * E.natDegree) < (A.natDegree + 2 * D.natDegree))
    (ht2c : (A.natDegree + 2 * F.natDegree) < (2 * G.natDegree)) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
  · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
    · -- D.natDegree < A.natDegree + B.natDegree
      rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
      · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG111 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG113 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG113 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG54 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG55 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG53 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG111 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG111 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG111 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
  · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
    · -- D.natDegree < A.natDegree + B.natDegree
      rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht5a | ht5b | ht5c
      · exact (by omega : False).elim
      · exact (by omega : False).elim
      · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG53 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG59 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG124 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
  · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
    · -- D.natDegree < A.natDegree + B.natDegree
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
