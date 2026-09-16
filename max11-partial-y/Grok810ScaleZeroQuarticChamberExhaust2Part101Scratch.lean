import Grok810ScaleZeroQuarticChamberDefs4Scratch

/-! Part 1 of 15 of `Grok810ScaleZeroQuarticChamberExhaust2Scratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

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
private theorem astra4zExhaustTailBCDE0
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hGn : g = 0)
    (hs : 4 * d < a + 6 * b ∧
      4 * e < 3 * a + 6 * b ∧
      2 * c < a + 2 * b) :
    4 * d < a + 6 * b ∧
    d + e < a + 3 * b ∧
    4 * e < 3 * a + 6 * b ∧
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
private theorem astra4zExhaustTailBCDE1
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hGn : g = 0)
    (hs : a + 2 * b = 2 * c ∧
      4 * d < a + 6 * b ∧
      4 * e < 3 * a + 6 * b) :
    a + 2 * b = 2 * c ∧
    a + 2 * b = 2 * c ∧
    a + 2 * b = 2 * c ∧
    4 * d < a + 6 * b ∧
    d + e < a + 3 * b ∧
    4 * e < 3 * a + 6 * b ∧
    d < a + b ∧
    2 * e < 3 * a + 2 * b ∧
    2 * c + 2 * d < 3 * a + 4 * b ∧
    c + e < 2 * a + 2 * b ∧
    2 * c + d < 2 * a + 3 * b ∧
    4 * c + 2 * e < 5 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDE11
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hGn : g = 0)
    (hs : a + 2 * d < 2 * e ∧
      3 * a + 6 * b < 4 * e ∧
      3 * c < 2 * e) :
    a + 2 * d < 2 * e ∧
    a + 2 * d < 2 * e ∧
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
private theorem astra4zExhaustTailBCDE2
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hGn : g = 0)
    (hs : a + 2 * d < 3 * c ∧
      2 * e < 3 * c ∧
      a + 2 * b < 2 * c) :
    a + 2 * d < 3 * c ∧
    a + 2 * d + 2 * e < 6 * c ∧
    2 * e < 3 * c ∧
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
private theorem astra4zExhaustTailBCDE3
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hGn : g = 0)
    (hs : 2 * e < a + 2 * d ∧
      a + 6 * b < 4 * d ∧
      3 * c < a + 2 * d) :
    2 * e < a + 2 * d ∧
    2 * e < a + 2 * d ∧
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
private theorem astra4zExhaustTailBCDE7
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hFn : f = 0)
    (hGn : g = 0)
    (hs : a + 2 * d = 2 * e ∧
      a + 6 * b < 4 * d ∧
      3 * c < a + 2 * d) :
    a + 2 * d = 2 * e ∧
    a + 2 * d = 2 * e ∧
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
private theorem astra4zExhaustTailBCDF0
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hGn : g = 0)
    (hs : 2 * f < a + 4 * b ∧
      4 * d < a + 6 * b ∧
      2 * c < a + 2 * b) :
    2 * f < a + 4 * b ∧
    c + f < a + 3 * b ∧
    4 * d < a + 6 * b ∧
    2 * d + 2 * f < 3 * a + 6 * b ∧
    4 * f < 5 * a + 6 * b ∧
    2 * c < a + 2 * b ∧
    d < a + b ∧
    2 * c < a + 2 * b ∧
    2 * c + 2 * d < 3 * a + 4 * b ∧
    2 * c < a + 2 * b ∧
    2 * c + d < 2 * a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDF1
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hGn : g = 0)
    (hs : a + 2 * b = 2 * c ∧
      c + f < a + 3 * b ∧
      4 * d < a + 6 * b) :
    a + 2 * b = 2 * c ∧
    a + 2 * b = 2 * c ∧
    a + 2 * b = 2 * c ∧
    2 * f < a + 4 * b ∧
    c + f < a + 3 * b ∧
    4 * d < a + 6 * b ∧
    2 * d + 2 * f < 3 * a + 6 * b ∧
    4 * f < 5 * a + 6 * b ∧
    d < a + b ∧
    2 * c + 2 * d < 3 * a + 4 * b ∧
    2 * c + d < 2 * a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDF14
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hGn : g = 0)
    (hs : a + 2 * f < 4 * c ∧
      a + 2 * d < 3 * c ∧
      a + 2 * b < 2 * c) :
    a + b + f < 3 * c ∧
    a + 2 * f < 4 * c ∧
    a + 2 * d < 3 * c ∧
    d + f < 3 * c ∧
    2 * f < a + 3 * c ∧
    a + 2 * b < 2 * c ∧
    a + 2 * b < 2 * c ∧
    a + 4 * b + 2 * d < 6 * c ∧
    a + 2 * b < 2 * c ∧
    b + d < 2 * c ∧
    2 * d < a + 2 * c := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDF15
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hGn : g = 0)
    (hs : a + 2 * b < 2 * c ∧
      a + 4 * d < 2 * c + 2 * f ∧
      2 * f < 3 * a + 2 * c ∧
      4 * c < a + 2 * f) :
    a + 2 * b < 2 * c ∧
    a + 4 * d < 2 * c + 2 * f ∧
    2 * d < a + 2 * c ∧
    2 * f < 3 * a + 2 * c ∧
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
private theorem astra4zExhaustTailBCDF16
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hGn : g = 0)
    (hs : a + 2 * f = 4 * c ∧
      a + 4 * d < 2 * c + 2 * f ∧
      b + c < f) :
    a + 2 * f = 4 * c ∧
    a + 2 * b < 2 * c ∧
    a + 4 * d < 2 * c + 2 * f ∧
    2 * d < a + 2 * c ∧
    2 * f < 3 * a + 2 * c ∧
    a + 3 * b < c + f ∧
    a + 4 * b < 2 * f ∧
    2 * b + d < c + f ∧
    b + c < f ∧
    2 * b + 2 * d < a + 2 * f ∧
    c + d < a + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDF2
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hGn : g = 0)
    (hs : 2 * c < a + 2 * b ∧
      2 * d < b + f ∧
      f < 2 * a + b ∧
      a + 4 * b < 2 * f) :
    2 * c < a + 2 * b ∧
    2 * d < b + f ∧
    d < a + b ∧
    f < 2 * a + b ∧
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
private theorem astra4zExhaustTailBCDF21
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hGn : g = 0)
    (hs : b + f < 2 * d ∧
      2 * c + 2 * f < a + 4 * d ∧
      f < a + d ∧
      a + 6 * b < 4 * d ∧
      3 * c < a + 2 * d) :
    b + f < 2 * d ∧
    2 * c + 2 * f < a + 4 * d ∧
    f < a + d ∧
    f < a + d ∧
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
private theorem astra4zExhaustTailBCDF25
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hGn : g = 0)
    (hs : a + d = f ∧
      b + f < 2 * d ∧
      2 * c + 2 * f < a + 4 * d) :
    a + d = f ∧
    a + d = f ∧
    b + f < 2 * d ∧
    2 * c + 2 * f < a + 4 * d ∧
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
private theorem astra4zExhaustTailBCDF26
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hGn : g = 0)
    (hs : 2 * a + b < f ∧
      3 * a + 2 * c < 2 * f ∧
      a + d < f) :
    2 * a + b < f ∧
    3 * a + 2 * c < 2 * f ∧
    a + d < f ∧
    a + d < f ∧
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
private theorem astra4zExhaustTailBCDF3
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hGn : g = 0)
    (hs : 2 * f = a + 4 * b ∧
      2 * d < b + f ∧
      3 * c < a + b + f) :
    2 * f = a + 4 * b ∧
    2 * c < a + 2 * b ∧
    2 * d < b + f ∧
    d < a + b ∧
    f < 2 * a + b ∧
    b + c < f ∧
    2 * b + 2 * d < a + 2 * f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f ∧
    3 * c < a + b + f ∧
    4 * c + 2 * d < 3 * a + 2 * b + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDF4
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hGn : g = 0)
    (hs : a + 2 * b = 2 * c ∧
      2 * d < b + f ∧
      f < 2 * a + b ∧
      3 * c < a + b + f) :
    a + 2 * b = 2 * c ∧
    2 * d < b + f ∧
    d < a + b ∧
    f < 2 * a + b ∧
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
private theorem astra4zExhaustTailBCDF5
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hGn : g = 0)
    (hs : a + 2 * f = 4 * c ∧
      a + b + f = 3 * c ∧
      2 * d < b + f) :
    a + 2 * b = 2 * c ∧
    2 * f = a + 4 * b ∧
    f = b + c ∧
    a + 2 * f = 4 * c ∧
    a + b + f = 3 * c ∧
    2 * d < b + f ∧
    d < a + b ∧
    f < 2 * a + b ∧
    2 * b + 2 * d < a + 2 * f ∧
    c + d < a + f ∧
    4 * c + 2 * d < 3 * a + 2 * b + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDG0
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hFn : f = 0)
    (hs : g < a + 2 * b ∧
      4 * d < a + 6 * b ∧
      2 * c < a + 2 * b) :
    g < a + 2 * b ∧
    2 * c + 2 * g < 3 * a + 6 * b ∧
    4 * d < a + 6 * b ∧
    d + g < 2 * a + 3 * b ∧
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
private theorem astra4zExhaustTailBCDG1
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hFn : f = 0)
    (hs : a + 2 * b = 2 * c ∧
      2 * c + 2 * g < 3 * a + 6 * b ∧
      4 * d < a + 6 * b) :
    a + 2 * b = 2 * c ∧
    a + 2 * b = 2 * c ∧
    a + 2 * b = 2 * c ∧
    g < a + 2 * b ∧
    2 * c + 2 * g < 3 * a + 6 * b ∧
    4 * d < a + 6 * b ∧
    d + g < 2 * a + 3 * b ∧
    4 * g < 7 * a + 6 * b ∧
    d < a + b ∧
    2 * c + 2 * d < 3 * a + 4 * b ∧
    2 * c + d < 2 * a + 3 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCDG14
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hFn : f = 0)
    (hs : g < 2 * c ∧
      a + 2 * d < 3 * c ∧
      a + 2 * b < 2 * c) :
    a + 2 * b + 2 * g < 6 * c ∧
    g < 2 * c ∧
    a + 2 * d < 3 * c ∧
    2 * d + 2 * g < a + 6 * c ∧
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
private theorem astra4zExhaustTailBCDG15
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hFn : f = 0)
    (hs : a + 2 * b < 2 * c ∧
      a + 2 * d < c + g ∧
      g < 2 * a + c ∧
      2 * c < g) :
    a + 2 * b < 2 * c ∧
    a + 2 * d < c + g ∧
    2 * d < a + 2 * c ∧
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
private theorem astra4zExhaustTailBCDG16
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hFn : f = 0)
    (hs : g = 2 * c ∧
      a + 2 * d < c + g ∧
      a + 2 * b + 2 * c < 2 * g) :
    g = 2 * c ∧
    a + 2 * b < 2 * c ∧
    a + 2 * d < c + g ∧
    2 * d < a + 2 * c ∧
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
private theorem astra4zExhaustTailBCDG2
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hFn : f = 0)
    (hs : 2 * c < a + 2 * b ∧
      a + 4 * d < 2 * b + 2 * g ∧
      2 * g < 5 * a + 2 * b ∧
      a + 2 * b < g) :
    2 * c < a + 2 * b ∧
    a + 4 * d < 2 * b + 2 * g ∧
    d < a + b ∧
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
private theorem astra4zExhaustTailBCDG21
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hFn : f = 0)
    (hs : 2 * b + 2 * g < a + 4 * d ∧
      c + g < a + 2 * d ∧
      2 * g < 3 * a + 2 * d ∧
      a + 6 * b < 4 * d ∧
      3 * c < a + 2 * d) :
    2 * b + 2 * g < a + 4 * d ∧
    c + g < a + 2 * d ∧
    2 * g < 3 * a + 2 * d ∧
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
private theorem astra4zExhaustTailBCDG25
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hFn : f = 0)
    (hs : 3 * a + 2 * d = 2 * g ∧
      2 * b + 2 * g < a + 4 * d ∧
      c + g < a + 2 * d) :
    3 * a + 2 * d = 2 * g ∧
    3 * a + 2 * d = 2 * g ∧
    2 * b + 2 * g < a + 4 * d ∧
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
private theorem astra4zExhaustTailBCDG26
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hFn : f = 0)
    (hs : 5 * a + 2 * b < 2 * g ∧
      2 * a + c < g ∧
      3 * a + 2 * d < 2 * g) :
    5 * a + 2 * b < 2 * g ∧
    2 * a + c < g ∧
    3 * a + 2 * d < 2 * g ∧
    3 * a + 2 * d < 2 * g ∧
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
private theorem astra4zExhaustTailBCDG3
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hFn : f = 0)
    (hs : g = a + 2 * b ∧
      a + 4 * d < 2 * b + 2 * g ∧
      6 * c < a + 2 * b + 2 * g) :
    g = a + 2 * b ∧
    2 * c < a + 2 * b ∧
    a + 4 * d < 2 * b + 2 * g ∧
    d < a + b ∧
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
private theorem astra4zExhaustTailBCDG4
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hFn : f = 0)
    (hs : a + 2 * b = 2 * c ∧
      a + 4 * d < 2 * b + 2 * g ∧
      2 * g < 5 * a + 2 * b ∧
      6 * c < a + 2 * b + 2 * g) :
    a + 2 * b = 2 * c ∧
    a + 4 * d < 2 * b + 2 * g ∧
    d < a + b ∧
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
private theorem astra4zExhaustTailBCDG5
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hEn : e = 0)
    (hFn : f = 0)
    (hs : g = 2 * c ∧
      a + 2 * b + 2 * g = 6 * c ∧
      a + 4 * d < 2 * b + 2 * g) :
    a + 2 * b = 2 * c ∧
    g = a + 2 * b ∧
    2 * g = a + 2 * b + 2 * c ∧
    g = 2 * c ∧
    a + 2 * b + 2 * g = 6 * c ∧
    a + 4 * d < 2 * b + 2 * g ∧
    d < a + b ∧
    2 * g < 5 * a + 2 * b ∧
    b + d < g ∧
    2 * c + 2 * d < a + 2 * g ∧
    2 * c + d < a + b + g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEF0
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hGn : g = 0)
    (hs : 2 * f < a + 4 * b ∧
      4 * e < 3 * a + 6 * b ∧
      2 * c < a + 2 * b) :
    2 * f < a + 4 * b ∧
    c + f < a + 3 * b ∧
    4 * e < 3 * a + 6 * b ∧
    e + f < 2 * a + 3 * b ∧
    4 * f < 5 * a + 6 * b ∧
    2 * c < a + 2 * b ∧
    2 * e < 3 * a + 2 * b ∧
    2 * c < a + 2 * b ∧
    c + e < 2 * a + 2 * b ∧
    2 * c < a + 2 * b ∧
    4 * c + 2 * e < 5 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEF1
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hGn : g = 0)
    (hs : a + 2 * b = 2 * c ∧
      c + f < a + 3 * b ∧
      4 * e < 3 * a + 6 * b) :
    a + 2 * b = 2 * c ∧
    a + 2 * b = 2 * c ∧
    a + 2 * b = 2 * c ∧
    2 * f < a + 4 * b ∧
    c + f < a + 3 * b ∧
    4 * e < 3 * a + 6 * b ∧
    e + f < 2 * a + 3 * b ∧
    4 * f < 5 * a + 6 * b ∧
    2 * e < 3 * a + 2 * b ∧
    c + e < 2 * a + 2 * b ∧
    4 * c + 2 * e < 5 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEF14
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hGn : g = 0)
    (hs : a + 2 * f < 4 * c ∧
      2 * e < 3 * c ∧
      a + 2 * b < 2 * c) :
    a + b + f < 3 * c ∧
    a + 2 * f < 4 * c ∧
    2 * e < 3 * c ∧
    2 * e + 2 * f < a + 6 * c ∧
    2 * f < a + 3 * c ∧
    a + 2 * b < 2 * c ∧
    a + 2 * b < 2 * c ∧
    2 * b + e < 3 * c ∧
    a + 2 * b < 2 * c ∧
    2 * b + 2 * e < a + 4 * c ∧
    e < a + c := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEF15
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hGn : g = 0)
    (hs : a + 2 * b < 2 * c ∧
      4 * e < a + 2 * c + 2 * f ∧
      2 * f < 3 * a + 2 * c ∧
      4 * c < a + 2 * f) :
    a + 2 * b < 2 * c ∧
    4 * e < a + 2 * c + 2 * f ∧
    e < a + c ∧
    2 * f < 3 * a + 2 * c ∧
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
private theorem astra4zExhaustTailBCEF16
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hGn : g = 0)
    (hs : a + 2 * f = 4 * c ∧
      4 * e < a + 2 * c + 2 * f ∧
      b + c < f) :
    a + 2 * f = 4 * c ∧
    a + 2 * b < 2 * c ∧
    4 * e < a + 2 * c + 2 * f ∧
    e < a + c ∧
    2 * f < 3 * a + 2 * c ∧
    a + 3 * b < c + f ∧
    a + 4 * b < 2 * f ∧
    4 * b + 2 * e < a + 2 * c + 2 * f ∧
    b + c < f ∧
    b + e < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEF2
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hGn : g = 0)
    (hs : 2 * c < a + 2 * b ∧
      2 * e < a + b + f ∧
      f < 2 * a + b ∧
      a + 4 * b < 2 * f) :
    2 * c < a + 2 * b ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    f < 2 * a + b ∧
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
private theorem astra4zExhaustTailBCEF21
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hGn : g = 0)
    (hs : a + b + f < 2 * e ∧
      a + 2 * c + 2 * f < 4 * e ∧
      2 * f < a + 2 * e ∧
      3 * a + 6 * b < 4 * e ∧
      3 * c < 2 * e) :
    a + b + f < 2 * e ∧
    a + 2 * c + 2 * f < 4 * e ∧
    2 * f < a + 2 * e ∧
    2 * f < a + 2 * e ∧
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
private theorem astra4zExhaustTailBCEF25
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hGn : g = 0)
    (hs : a + 2 * e = 2 * f ∧
      a + b + f < 2 * e ∧
      a + 2 * c + 2 * f < 4 * e) :
    a + 2 * e = 2 * f ∧
    a + 2 * e = 2 * f ∧
    a + b + f < 2 * e ∧
    a + 2 * c + 2 * f < 4 * e ∧
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
private theorem astra4zExhaustTailBCEF26
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hGn : g = 0)
    (hs : 2 * a + b < f ∧
      3 * a + 2 * c < 2 * f ∧
      a + 2 * e < 2 * f) :
    2 * a + b < f ∧
    3 * a + 2 * c < 2 * f ∧
    a + 2 * e < 2 * f ∧
    a + 2 * e < 2 * f ∧
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
private theorem astra4zExhaustTailBCEF3
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hGn : g = 0)
    (hs : 2 * f = a + 4 * b ∧
      2 * e < a + b + f ∧
      3 * c < a + b + f) :
    2 * f = a + 4 * b ∧
    2 * c < a + 2 * b ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    f < 2 * a + b ∧
    b + c < f ∧
    b + e < a + f ∧
    4 * c < a + 2 * f ∧
    2 * c + 2 * e < 3 * a + 2 * f ∧
    3 * c < a + b + f ∧
    2 * c + e < 2 * a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEF4
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hGn : g = 0)
    (hs : a + 2 * b = 2 * c ∧
      2 * e < a + b + f ∧
      f < 2 * a + b ∧
      3 * c < a + b + f) :
    a + 2 * b = 2 * c ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    f < 2 * a + b ∧
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
private theorem astra4zExhaustTailBCEF5
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hGn : g = 0)
    (hs : a + 2 * f = 4 * c ∧
      a + b + f = 3 * c ∧
      2 * e < a + b + f) :
    a + 2 * b = 2 * c ∧
    2 * f = a + 4 * b ∧
    f = b + c ∧
    a + 2 * f = 4 * c ∧
    a + b + f = 3 * c ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    f < 2 * a + b ∧
    b + e < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f ∧
    2 * c + e < 2 * a + b + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BCDE`. -/
theorem quarticChamberSupport810_of_live_BCDE
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFz : F = 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE4 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
    · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE7 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE7 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE8 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE7 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE7 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE7 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE7 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
    · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE11 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE11 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE12 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE0 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE11 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE11 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE11 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE11 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE5 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
    · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE7 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE7 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE9 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE7 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE7 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE7 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE7 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
    · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE11 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE11 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE13 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE1 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE11 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE11 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE11 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE11 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE6 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE3 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
    · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE7 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE7 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE10 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE7 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE7 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE7 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE7 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
    · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE11 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE11 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE14 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE2 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE11 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE11 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDE11 ⟨hA, hBne, hCne, hDne, hEne, hFz, hGz, astra4zExhaustTailBCDE11 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hFn hGn (by omega)⟩)
end QuarticChamberExhaust810
end Max11DegreeRoutes
end
/-! Part 2 of 15 of `Grok810ScaleZeroQuarticChamberExhaust2Scratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

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
/-- Exhaust of the cost-argmin taxonomy on the live set `BCDF`. -/
theorem quarticChamberSupport810_of_live_BCDF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEz : E = 0) (hFne : F ≠ 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · -- F.natDegree < A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF21 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF22 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF10 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF11 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF2 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF3 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF21 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF21 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
    · -- F.natDegree = A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF2 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF3 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF12 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF25 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
    · -- F.natDegree > A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF13 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF2 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF3 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF0 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · -- F.natDegree < A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF21 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF23 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF6 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF7 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF4 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF5 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF21 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF21 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
    · -- F.natDegree = A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF4 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF5 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF8 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF25 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
    · -- F.natDegree > A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF9 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF4 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF5 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF1 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · -- F.natDegree < A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF21 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF24 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF14 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF17 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF18 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF14 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF15 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF15 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF16 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF14 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF21 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF21 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
    · -- F.natDegree = A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF15 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF15 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF16 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF14 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF19 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF25 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
    · -- F.natDegree > A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF20 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, by omega⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF15 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF15 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF16 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF14 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDF26 ⟨hA, hBne, hCne, hDne, hEz, hFne, hGz, astra4zExhaustTailBCDF26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hGn (by omega)⟩)
end QuarticChamberExhaust810
end Max11DegreeRoutes
end
/-! Part 3 of 15 of `Grok810ScaleZeroQuarticChamberExhaust2Scratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

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
/-- Exhaust of the cost-argmin taxonomy on the live set `BCDG`. -/
theorem quarticChamberSupport810_of_live_BCDG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEz : E = 0) (hFz : F = 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG21 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG22 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG0 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG10 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG11 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG0 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG2 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG3 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG0 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG21 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG21 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
    · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG2 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG3 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG0 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG12 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG25 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
    · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG26 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG13 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG2 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG3 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG0 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG26 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG26 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG21 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG23 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG1 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG6 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG7 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG1 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG4 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG5 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG1 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG21 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG21 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
    · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG4 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG5 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG1 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG8 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG25 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
    · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG26 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG9 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG4 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG5 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG1 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG26 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG26 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG21 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG24 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG14 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG17 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG18 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG14 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG15 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG15 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG16 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG14 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG21 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG21 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
    · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG15 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG15 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG16 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG14 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG19 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG25 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
    · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG26 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG20 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, by omega⟩)
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG15 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG15 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG16 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG14 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG26 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCDG26 ⟨hA, hBne, hCne, hDne, hEz, hFz, hGne, astra4zExhaustTailBCDG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hEn hFn (by omega)⟩)
end QuarticChamberExhaust810
end Max11DegreeRoutes
end
/-! Part 4 of 15 of `Grok810ScaleZeroQuarticChamberExhaust2Scratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

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
/-- Exhaust of the cost-argmin taxonomy on the live set `BCEF`. -/
theorem quarticChamberSupport810_of_live_BCEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDz : D = 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF21 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF22 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF10 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF11 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF2 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF3 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF21 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF21 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
    · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF2 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF3 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF12 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF25 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
    · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF13 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF2 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF3 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF0 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF21 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF23 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF6 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF7 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF4 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF5 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF21 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF21 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
    · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF4 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF5 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF8 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF25 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
    · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF9 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF4 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF5 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF1 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF21 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF24 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF14 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF17 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF18 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF14 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF15 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF15 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF16 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF14 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF21 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF21 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
    · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF15 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF15 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF16 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF14 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF19 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF25 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
    · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF20 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, by omega⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF15 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF15 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF16 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF14 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEF26 ⟨hA, hBne, hCne, hDz, hEne, hFne, hGz, astra4zExhaustTailBCEF26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hGn (by omega)⟩)
end QuarticChamberExhaust810
end Max11DegreeRoutes
end
