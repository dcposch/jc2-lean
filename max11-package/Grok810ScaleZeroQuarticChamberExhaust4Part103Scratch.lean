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
private theorem astra4zExhaustTailBCDEFG120
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : a + 2 * d = 2 * e ∧
      a + 4 * d = 2 * b + 4 * c ∧
      a + 2 * d = 3 * c ∧
      2 * c + 2 * f < a + 4 * d ∧
      c + g < a + 2 * d) :
    a + 2 * d = 2 * e ∧
    a + 2 * d = 2 * e ∧
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
private theorem astra4zExhaustTailBCDEFG127
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : 4 * e = a + 2 * b + 4 * c ∧
      2 * e = 3 * c ∧
      a + 2 * c + 2 * f < 4 * e ∧
      c + g < 2 * e ∧
      a + 2 * d < 2 * e) :
    4 * e = 3 * a + 6 * b ∧
    2 * e = a + 2 * b + c ∧
    4 * e = a + 2 * b + 4 * c ∧
    2 * e = 3 * c ∧
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
    a + 4 * b + 2 * d < 4 * e ∧
    2 * b < e ∧
    b + c + d < 2 * e ∧
    2 * b + 2 * c < a + 2 * e ∧
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
private theorem astra4zExhaustTailBCDEFG17
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : a + b + f = c + g ∧
      5 * a + 2 * b = 2 * g ∧
      3 * a + b + f = 2 * g ∧
      2 * d + 2 * g < 3 * a + 2 * b + 2 * f ∧
      e + g < 2 * a + b + f) :
    a + 2 * f = 2 * g ∧
    a + 2 * b = 2 * c ∧
    a + b + f = c + g ∧
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
private theorem astra4zExhaustTailBCDEFG39
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hs : a + 2 * b = 2 * c ∧
      2 * a + b = f ∧
      d < a + b ∧
      2 * e < 3 * a + 2 * b ∧
      2 * g < 3 * a + b + f) :
    a + 2 * b = 2 * c ∧
    2 * a + b = f ∧
    2 * g < a + 2 * f ∧
    c + g < a + b + f ∧
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
/-- Cost-argmin subtree on the three comparison branches `110`. -/
private theorem chamberExhaustBCDEFGPath110
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0b : (2 * C.natDegree) = (A.natDegree + 2 * B.natDegree))
    (ht1b : (2 * E.natDegree) = (A.natDegree + 2 * D.natDegree))
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
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG118 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG120 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG120 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- B.natDegree + F.natDegree = 2 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG33 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG34 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- B.natDegree + F.natDegree > 2 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG28 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG29 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG29 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG118 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG118 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
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
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG32 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG116 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
  · -- F.natDegree > A.natDegree + D.natDegree
    rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
    · -- D.natDegree < A.natDegree + B.natDegree
      rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG132 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG39 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG39 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
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
/-- Cost-argmin subtree on the three comparison branches `111`. -/
private theorem chamberExhaustBCDEFGPath111
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0b : (2 * C.natDegree) = (A.natDegree + 2 * B.natDegree))
    (ht1b : (2 * E.natDegree) = (A.natDegree + 2 * D.natDegree))
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
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG118 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG120 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG120 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- B.natDegree + F.natDegree = 2 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG11 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG12 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- B.natDegree + F.natDegree > 2 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG6 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG7 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG7 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG118 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG118 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
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
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG10 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG115 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
  · -- F.natDegree > A.natDegree + D.natDegree
    rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht4a | ht4b | ht4c
    · -- D.natDegree < A.natDegree + B.natDegree
      rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG133 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG17 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG17 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
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
/-- Cost-argmin subtree on the three comparison branches `112`. -/
private theorem chamberExhaustBCDEFGPath112
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0b : (2 * C.natDegree) = (A.natDegree + 2 * B.natDegree))
    (ht1b : (2 * E.natDegree) = (A.natDegree + 2 * D.natDegree))
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
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG118 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG120 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG120 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG57 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG58 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG52 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG52 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG53 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG53 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG118 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG118 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG118 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
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
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG56 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG117 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
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
/-- Cost-argmin subtree on the three comparison branches `120`. -/
private theorem chamberExhaustBCDEFGPath120
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0b : (2 * C.natDegree) = (A.natDegree + 2 * B.natDegree))
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
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG127 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG127 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG36 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG37 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG28 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG29 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG29 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
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
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG28 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG28 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG29 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG29 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG38 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG130 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
  · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG132 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG132 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG39 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG39 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
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
/-- Cost-argmin subtree on the three comparison branches `121`. -/
private theorem chamberExhaustBCDEFGPath121
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0)
    (ht0b : (2 * C.natDegree) = (A.natDegree + 2 * B.natDegree))
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
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG127 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG127 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG14 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG15 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG6 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG7 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG7 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
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
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG6 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG7 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG7 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG16 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG129 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, by omega⟩)
  · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht4a | ht4b | ht4c
    · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
      rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht5a | ht5b | ht5c
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG133 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG17 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG17 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
      · -- 2 * A.natDegree + B.natDegree > F.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht6a | ht6b | ht6c
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG6 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG6 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG7 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG7 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
        · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG1 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG133 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
    · exact QuarticChamberSupport810.size6 (QuarticChamberSupportSize6810.cBCDEFG133 ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, astra4zExhaustTailBCDEFG133 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG (by omega)⟩)
end QuarticChamberExhaust810

end Max11DegreeRoutes
