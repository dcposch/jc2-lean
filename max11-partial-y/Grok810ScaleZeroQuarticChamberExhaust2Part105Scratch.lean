import Grok810ScaleZeroQuarticChamberDefs4Scratch

/-! Part 9 of 15 of `Grok810ScaleZeroQuarticChamberExhaust2Scratch`, split so that no single module elaborates them all
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
private theorem astra4zExhaustTailBDFG0
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hEn : e = 0)
    (hs : 2 * f < a + 4 * b ∧
      g < a + 2 * b ∧
      4 * d < a + 6 * b) :
    2 * f < a + 4 * b ∧
    g < a + 2 * b ∧
    4 * d < a + 6 * b ∧
    2 * d + 2 * f < 3 * a + 6 * b ∧
    d + g < 2 * a + 3 * b ∧
    4 * f < 5 * a + 6 * b ∧
    f + g < 3 * a + 3 * b ∧
    4 * g < 7 * a + 6 * b ∧
    d < a + b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDFG1
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hEn : e = 0)
    (hs : 2 * g < a + 2 * f ∧
      2 * d < b + f ∧
      f < 2 * a + b ∧
      a + 4 * b < 2 * f) :
    2 * g < a + 2 * f ∧
    2 * d < b + f ∧
    d < a + b ∧
    2 * d + 2 * g < 3 * a + 2 * b + 2 * f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    a + 4 * b < 2 * f ∧
    2 * b + 2 * d < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDFG13
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hEn : e = 0)
    (hs : a + 2 * f < 2 * g ∧
      a + 4 * d < 2 * b + 2 * g ∧
      2 * g < 5 * a + 2 * b ∧
      a + 2 * b < g) :
    a + 2 * f < 2 * g ∧
    a + 4 * d < 2 * b + 2 * g ∧
    2 * d + 2 * f < a + 2 * b + 2 * g ∧
    d < a + b ∧
    4 * f < 3 * a + 2 * b + 2 * g ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    a + 2 * b < g ∧
    b + d < g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDFG14
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hEn : e = 0)
    (hs : g = a + 2 * b ∧
      a + 2 * f < 2 * g ∧
      a + 4 * d < 2 * b + 2 * g) :
    g = a + 2 * b ∧
    a + 2 * f < 2 * g ∧
    a + 4 * d < 2 * b + 2 * g ∧
    2 * d + 2 * f < a + 2 * b + 2 * g ∧
    d < a + b ∧
    4 * f < 3 * a + 2 * b + 2 * g ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    b + d < g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDFG19
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hEn : e = 0)
    (hs : b + f < 2 * d ∧
      2 * b + 2 * g < a + 4 * d ∧
      f < a + d ∧
      2 * g < 3 * a + 2 * d ∧
      a + 6 * b < 4 * d) :
    b + f < 2 * d ∧
    2 * b + 2 * g < a + 4 * d ∧
    f < a + d ∧
    2 * g < 3 * a + 2 * d ∧
    f < a + d ∧
    2 * f + 2 * g < 5 * a + 4 * d ∧
    2 * g < 3 * a + 2 * d ∧
    a + 6 * b < 4 * d ∧
    4 * b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDFG2
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hEn : e = 0)
    (hs : 2 * f = a + 4 * b ∧
      2 * g < a + 2 * f ∧
      2 * d < b + f) :
    2 * f = a + 4 * b ∧
    2 * g < a + 2 * f ∧
    2 * d < b + f ∧
    d < a + b ∧
    2 * d + 2 * g < 3 * a + 2 * b + 2 * f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    2 * b + 2 * d < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDFG20
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hEn : e = 0)
    (hs : 4 * d = a + 6 * b ∧
      b + f < 2 * d ∧
      2 * b + 2 * g < a + 4 * d) :
    4 * d = a + 6 * b ∧
    b + f < 2 * d ∧
    2 * b + 2 * g < a + 4 * d ∧
    f < a + d ∧
    2 * g < 3 * a + 2 * d ∧
    f < a + d ∧
    2 * f + 2 * g < 5 * a + 4 * d ∧
    2 * g < 3 * a + 2 * d ∧
    4 * b < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDFG24
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hEn : e = 0)
    (hs : 2 * a + b < f ∧
      a + d < f ∧
      2 * g < a + 2 * f) :
    2 * a + b < f ∧
    3 * a + 2 * b + 2 * g < 4 * f ∧
    a + d < f ∧
    a + d < f ∧
    a + 2 * d + 2 * g < 4 * f ∧
    2 * g < a + 2 * f ∧
    2 * g < a + 2 * f ∧
    5 * a + 6 * b < 4 * f ∧
    3 * a + 4 * b + 2 * d < 4 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDFG25
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hEn : e = 0)
    (hs : a + 2 * f = 2 * g ∧
      3 * a + 2 * b + 2 * g < 4 * f ∧
      a + 2 * d + 2 * g < 4 * f) :
    a + 2 * f = 2 * g ∧
    a + 2 * f = 2 * g ∧
    2 * a + b < f ∧
    3 * a + 2 * b + 2 * g < 4 * f ∧
    a + d < f ∧
    a + d < f ∧
    a + 2 * d + 2 * g < 4 * f ∧
    5 * a + 6 * b < 4 * f ∧
    3 * a + 4 * b + 2 * d < 4 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDFG26
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hEn : e = 0)
    (hs : 5 * a + 2 * b < 2 * g ∧
      3 * a + 2 * d < 2 * g ∧
      a + 2 * f < 2 * g) :
    3 * a + b + f < 2 * g ∧
    5 * a + 2 * b < 2 * g ∧
    3 * a + 2 * d < 2 * g ∧
    2 * a + d + f < 2 * g ∧
    3 * a + 2 * d < 2 * g ∧
    a + 2 * f < 2 * g ∧
    a + 2 * f < 2 * g ∧
    7 * a + 6 * b < 4 * g ∧
    5 * a + 4 * b + 2 * d < 4 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDFG3
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hEn : e = 0)
    (hs : a + 2 * f = 2 * g ∧
      2 * d < b + f ∧
      2 * g < 3 * a + b + f ∧
      a + 4 * b < 2 * f) :
    a + 2 * f = 2 * g ∧
    2 * d < b + f ∧
    d < a + b ∧
    2 * d + 2 * g < 3 * a + 2 * b + 2 * f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    a + 4 * b < 2 * f ∧
    2 * b + 2 * d < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDFG4
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hEn : e = 0)
    (hs : a + 2 * f = 2 * g ∧
      2 * f = a + 4 * b ∧
      2 * d < b + f) :
    a + 2 * f = 2 * g ∧
    2 * f = a + 4 * b ∧
    2 * d < b + f ∧
    d < a + b ∧
    2 * d + 2 * g < 3 * a + 2 * b + 2 * f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    2 * b + 2 * d < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBEFG0
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hDn : d = 0)
    (hs : 2 * f < a + 4 * b ∧
      g < a + 2 * b ∧
      4 * e < 3 * a + 6 * b) :
    2 * f < a + 4 * b ∧
    g < a + 2 * b ∧
    4 * e < 3 * a + 6 * b ∧
    e + f < 2 * a + 3 * b ∧
    2 * e + 2 * g < 5 * a + 6 * b ∧
    4 * f < 5 * a + 6 * b ∧
    f + g < 3 * a + 3 * b ∧
    4 * g < 7 * a + 6 * b ∧
    2 * e < 3 * a + 2 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBEFG1
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hDn : d = 0)
    (hs : 2 * g < a + 2 * f ∧
      2 * e < a + b + f ∧
      f < 2 * a + b ∧
      a + 4 * b < 2 * f) :
    2 * g < a + 2 * f ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    e + g < 2 * a + b + f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    a + 4 * b < 2 * f ∧
    b + e < a + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBEFG13
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hDn : d = 0)
    (hs : a + 2 * f < 2 * g ∧
      4 * e < a + 2 * b + 2 * g ∧
      2 * g < 5 * a + 2 * b ∧
      a + 2 * b < g) :
    a + 2 * f < 2 * g ∧
    4 * e < a + 2 * b + 2 * g ∧
    e + f < a + b + g ∧
    2 * e < 3 * a + 2 * b ∧
    4 * f < 3 * a + 2 * b + 2 * g ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    a + 2 * b < g ∧
    2 * b + 2 * e < a + 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBEFG14
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hDn : d = 0)
    (hs : g = a + 2 * b ∧
      a + 2 * f < 2 * g ∧
      4 * e < a + 2 * b + 2 * g) :
    g = a + 2 * b ∧
    a + 2 * f < 2 * g ∧
    4 * e < a + 2 * b + 2 * g ∧
    e + f < a + b + g ∧
    2 * e < 3 * a + 2 * b ∧
    4 * f < 3 * a + 2 * b + 2 * g ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * b + 2 * e < a + 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBEFG19
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hDn : d = 0)
    (hs : a + b + f < 2 * e ∧
      a + 2 * b + 2 * g < 4 * e ∧
      2 * f < a + 2 * e ∧
      g < a + e ∧
      3 * a + 6 * b < 4 * e) :
    a + b + f < 2 * e ∧
    a + 2 * b + 2 * g < 4 * e ∧
    2 * f < a + 2 * e ∧
    g < a + e ∧
    2 * f < a + 2 * e ∧
    2 * f + 2 * g < 3 * a + 4 * e ∧
    g < a + e ∧
    3 * a + 6 * b < 4 * e ∧
    2 * b < e := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBEFG2
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hDn : d = 0)
    (hs : 2 * f = a + 4 * b ∧
      2 * g < a + 2 * f ∧
      2 * e < a + b + f) :
    2 * f = a + 4 * b ∧
    2 * g < a + 2 * f ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    e + g < 2 * a + b + f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    b + e < a + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBEFG20
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hDn : d = 0)
    (hs : 4 * e = 3 * a + 6 * b ∧
      a + b + f < 2 * e ∧
      a + 2 * b + 2 * g < 4 * e) :
    4 * e = 3 * a + 6 * b ∧
    a + b + f < 2 * e ∧
    a + 2 * b + 2 * g < 4 * e ∧
    2 * f < a + 2 * e ∧
    g < a + e ∧
    2 * f < a + 2 * e ∧
    2 * f + 2 * g < 3 * a + 4 * e ∧
    g < a + e ∧
    2 * b < e := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBEFG24
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hDn : d = 0)
    (hs : 2 * a + b < f ∧
      a + 2 * e < 2 * f ∧
      2 * g < a + 2 * f) :
    2 * a + b < f ∧
    3 * a + 2 * b + 2 * g < 4 * f ∧
    a + 2 * e < 2 * f ∧
    a + 2 * e < 2 * f ∧
    e + g < 2 * f ∧
    2 * g < a + 2 * f ∧
    2 * g < a + 2 * f ∧
    5 * a + 6 * b < 4 * f ∧
    a + 2 * b + e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBEFG25
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hDn : d = 0)
    (hs : a + 2 * f = 2 * g ∧
      3 * a + 2 * b + 2 * g < 4 * f ∧
      e + g < 2 * f) :
    a + 2 * f = 2 * g ∧
    a + 2 * f = 2 * g ∧
    2 * a + b < f ∧
    3 * a + 2 * b + 2 * g < 4 * f ∧
    a + 2 * e < 2 * f ∧
    a + 2 * e < 2 * f ∧
    e + g < 2 * f ∧
    5 * a + 6 * b < 4 * f ∧
    a + 2 * b + e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBEFG26
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hDn : d = 0)
    (hs : 5 * a + 2 * b < 2 * g ∧
      a + e < g ∧
      a + 2 * f < 2 * g) :
    3 * a + b + f < 2 * g ∧
    5 * a + 2 * b < 2 * g ∧
    a + e < g ∧
    3 * a + 2 * e + 2 * f < 4 * g ∧
    a + e < g ∧
    a + 2 * f < 2 * g ∧
    a + 2 * f < 2 * g ∧
    7 * a + 6 * b < 4 * g ∧
    2 * a + 2 * b + e < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBEFG3
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hDn : d = 0)
    (hs : a + 2 * f = 2 * g ∧
      2 * e < a + b + f ∧
      2 * g < 3 * a + b + f ∧
      a + 4 * b < 2 * f) :
    a + 2 * f = 2 * g ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    e + g < 2 * a + b + f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    a + 4 * b < 2 * f ∧
    b + e < a + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBEFG4
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hDn : d = 0)
    (hs : a + 2 * f = 2 * g ∧
      2 * f = a + 4 * b ∧
      2 * e < a + b + f) :
    a + 2 * f = 2 * g ∧
    2 * f = a + 4 * b ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    e + g < 2 * a + b + f ∧
    f < 2 * a + b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * g < 3 * a + b + f ∧
    b + e < a + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEF0
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hGn : g = 0)
    (hs : a + 2 * f < 4 * c ∧
      a + 2 * d < 3 * c ∧
      2 * e < 3 * c) :
    a + 2 * f < 4 * c ∧
    a + 2 * d < 3 * c ∧
    a + 2 * d + 2 * e < 6 * c ∧
    d + f < 3 * c ∧
    2 * e < 3 * c ∧
    2 * e + 2 * f < a + 6 * c ∧
    2 * f < a + 3 * c ∧
    2 * d < a + 2 * c ∧
    e < a + c := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEF1
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hGn : g = 0)
    (hs : a + 4 * d < 2 * c + 2 * f ∧
      4 * e < a + 2 * c + 2 * f ∧
      2 * f < 3 * a + 2 * c ∧
      4 * c < a + 2 * f) :
    a + 4 * d < 2 * c + 2 * f ∧
    d + e < c + f ∧
    2 * d < a + 2 * c ∧
    4 * e < a + 2 * c + 2 * f ∧
    e < a + c ∧
    2 * f < 3 * a + 2 * c ∧
    4 * c < a + 2 * f ∧
    c + d < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEF12
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hGn : g = 0)
    (hs : 3 * a + 2 * c = 2 * f ∧
      2 * d < a + 2 * c ∧
      e < a + c) :
    3 * a + 2 * c = 2 * f ∧
    a + 4 * d < 2 * c + 2 * f ∧
    d + e < c + f ∧
    2 * d < a + 2 * c ∧
    4 * e < a + 2 * c + 2 * f ∧
    e < a + c ∧
    4 * c < a + 2 * f ∧
    c + d < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEF13
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hGn : g = 0)
    (hs : 2 * c + 2 * f < a + 4 * d ∧
      2 * e < a + 2 * d ∧
      f < a + d ∧
      3 * c < a + 2 * d) :
    2 * c + 2 * f < a + 4 * d ∧
    2 * e < a + 2 * d ∧
    f < a + d ∧
    2 * e < a + 2 * d ∧
    2 * e + 2 * f < 3 * a + 4 * d ∧
    f < a + d ∧
    3 * c < a + 2 * d ∧
    4 * c < 3 * a + 2 * d ∧
    2 * c + e < 2 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEF16
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hGn : g = 0)
    (hs : a + 2 * d = 2 * e ∧
      2 * c + 2 * f < a + 4 * d ∧
      2 * e + 2 * f < 3 * a + 4 * d ∧
      3 * c < a + 2 * d) :
    a + 2 * d = 2 * e ∧
    a + 2 * d = 2 * e ∧
    2 * c + 2 * f < a + 4 * d ∧
    f < a + d ∧
    2 * e + 2 * f < 3 * a + 4 * d ∧
    f < a + d ∧
    3 * c < a + 2 * d ∧
    4 * c < 3 * a + 2 * d ∧
    2 * c + e < 2 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEF19
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hGn : g = 0)
    (hs : a + 2 * c + 2 * f < 4 * e ∧
      a + 2 * d < 2 * e ∧
      2 * f < a + 2 * e ∧
      3 * c < 2 * e) :
    a + 2 * c + 2 * f < 4 * e ∧
    a + 2 * d < 2 * e ∧
    a + 2 * d < 2 * e ∧
    d + f < 2 * e ∧
    2 * f < a + 2 * e ∧
    2 * f < a + 2 * e ∧
    3 * c < 2 * e ∧
    4 * c + 2 * d < a + 4 * e ∧
    2 * c < a + e := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEF2
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hGn : g = 0)
    (hs : a + 2 * f = 4 * c ∧
      a + 4 * d < 2 * c + 2 * f ∧
      4 * e < a + 2 * c + 2 * f) :
    a + 2 * f = 4 * c ∧
    a + 4 * d < 2 * c + 2 * f ∧
    d + e < c + f ∧
    2 * d < a + 2 * c ∧
    4 * e < a + 2 * c + 2 * f ∧
    e < a + c ∧
    2 * f < 3 * a + 2 * c ∧
    c + d < a + f ∧
    2 * c + 2 * e < 3 * a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEF22
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hGn : g = 0)
    (hs : 3 * a + 2 * c < 2 * f ∧
      a + d < f ∧
      a + 2 * e < 2 * f) :
    3 * a + 2 * c < 2 * f ∧
    a + d < f ∧
    3 * a + 2 * d + 2 * e < 4 * f ∧
    a + d < f ∧
    a + 2 * e < 2 * f ∧
    a + 2 * e < 2 * f ∧
    a + 3 * c < 2 * f ∧
    a + 4 * c + 2 * d < 4 * f ∧
    2 * c + e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEG0
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hFn : f = 0)
    (hs : g < 2 * c ∧
      a + 2 * d < 3 * c ∧
      2 * e < 3 * c) :
    g < 2 * c ∧
    a + 2 * d < 3 * c ∧
    a + 2 * d + 2 * e < 6 * c ∧
    2 * d + 2 * g < a + 6 * c ∧
    2 * e < 3 * c ∧
    e + g < a + 3 * c ∧
    2 * g < 2 * a + 3 * c ∧
    2 * d < a + 2 * c ∧
    e < a + c := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEG1
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hFn : f = 0)
    (hs : a + 2 * d < c + g ∧
      2 * e < c + g ∧
      g < 2 * a + c ∧
      2 * c < g) :
    a + 2 * d < c + g ∧
    a + 2 * d + 2 * e < 2 * c + 2 * g ∧
    2 * d < a + 2 * c ∧
    2 * e < c + g ∧
    e < a + c ∧
    g < 2 * a + c ∧
    2 * c < g ∧
    2 * c + 2 * d < a + 2 * g ∧
    c + e < a + g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEG12
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hFn : f = 0)
    (hs : 2 * a + c = g ∧
      2 * d < a + 2 * c ∧
      e < a + c) :
    2 * a + c = g ∧
    a + 2 * d < c + g ∧
    a + 2 * d + 2 * e < 2 * c + 2 * g ∧
    2 * d < a + 2 * c ∧
    2 * e < c + g ∧
    e < a + c ∧
    2 * c < g ∧
    2 * c + 2 * d < a + 2 * g ∧
    c + e < a + g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEG13
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hFn : f = 0)
    (hs : c + g < a + 2 * d ∧
      2 * e < a + 2 * d ∧
      2 * g < 3 * a + 2 * d ∧
      3 * c < a + 2 * d) :
    c + g < a + 2 * d ∧
    2 * e < a + 2 * d ∧
    2 * g < 3 * a + 2 * d ∧
    2 * e < a + 2 * d ∧
    e + g < 2 * a + 2 * d ∧
    2 * g < 3 * a + 2 * d ∧
    3 * c < a + 2 * d ∧
    4 * c < 3 * a + 2 * d ∧
    2 * c + e < 2 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEG16
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hFn : f = 0)
    (hs : a + 2 * d = 2 * e ∧
      c + g < a + 2 * d ∧
      e + g < 2 * a + 2 * d ∧
      3 * c < a + 2 * d) :
    a + 2 * d = 2 * e ∧
    a + 2 * d = 2 * e ∧
    c + g < a + 2 * d ∧
    2 * g < 3 * a + 2 * d ∧
    e + g < 2 * a + 2 * d ∧
    2 * g < 3 * a + 2 * d ∧
    3 * c < a + 2 * d ∧
    4 * c < 3 * a + 2 * d ∧
    2 * c + e < 2 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEG19
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hFn : f = 0)
    (hs : c + g < 2 * e ∧
      a + 2 * d < 2 * e ∧
      g < a + e ∧
      3 * c < 2 * e) :
    c + g < 2 * e ∧
    a + 2 * d < 2 * e ∧
    a + 2 * d < 2 * e ∧
    2 * d + 2 * g < a + 4 * e ∧
    g < a + e ∧
    g < a + e ∧
    3 * c < 2 * e ∧
    4 * c + 2 * d < a + 4 * e ∧
    2 * c < a + e := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEG2
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hFn : f = 0)
    (hs : g = 2 * c ∧
      a + 2 * d < c + g ∧
      2 * e < c + g) :
    g = 2 * c ∧
    a + 2 * d < c + g ∧
    a + 2 * d + 2 * e < 2 * c + 2 * g ∧
    2 * d < a + 2 * c ∧
    2 * e < c + g ∧
    e < a + c ∧
    g < 2 * a + c ∧
    2 * c + 2 * d < a + 2 * g ∧
    c + e < a + g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDEG22
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hFn : f = 0)
    (hs : 2 * a + c < g ∧
      3 * a + 2 * d < 2 * g ∧
      a + e < g) :
    2 * a + c < g ∧
    3 * a + 2 * d < 2 * g ∧
    5 * a + 2 * d + 2 * e < 4 * g ∧
    3 * a + 2 * d < 2 * g ∧
    a + e < g ∧
    a + e < g ∧
    2 * a + 3 * c < 2 * g ∧
    3 * a + 4 * c + 2 * d < 4 * g ∧
    a + 2 * c + e < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BDFG`. -/
theorem quarticChamberSupport810_of_live_BDFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCz : C = 0) (hDne : D ≠ 0) (hEz : E = 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · -- F.natDegree < A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG19 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG20 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG20 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG9 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG10 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG1 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG2 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG19 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG19 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
    · -- F.natDegree = A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG1 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG2 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG11 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG22 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
    · -- F.natDegree > A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG24 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG24 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG12 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG1 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG2 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG24 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG24 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG24 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG24 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
  · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · -- F.natDegree < A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG19 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG20 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG20 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG5 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG6 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG3 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG4 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG19 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG19 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
    · -- F.natDegree = A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG3 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG4 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG7 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG21 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
    · -- F.natDegree > A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG25 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG8 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG3 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG4 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG25 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG25 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
  · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG19 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG20 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG20 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG15 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG16 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG13 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG14 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG19 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG19 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
    · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG13 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG14 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG17 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG23 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
    · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG26 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG18 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG13 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG14 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG0 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG26 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDFG26 ⟨hA, hBne, hCz, hDne, hEz, hFne, hGne, astra4zExhaustTailBDFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hEn (by omega)⟩)
end QuarticChamberExhaust810
end Max11DegreeRoutes
end
/-! Part 10 of 15 of `Grok810ScaleZeroQuarticChamberExhaust2Scratch`, split so that no single module elaborates them all
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
/-- Exhaust of the cost-argmin taxonomy on the live set `BEFG`. -/
theorem quarticChamberSupport810_of_live_BEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCz : C = 0) (hDz : D = 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG19 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG20 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG20 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG9 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG10 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG1 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG2 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG19 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG19 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
    · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG1 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG2 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG11 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG22 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
    · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG24 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG24 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG12 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG1 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG2 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG24 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG24 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG24 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG24 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
  · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG19 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG20 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG20 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG5 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG6 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG3 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG4 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG19 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG19 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
    · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG3 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG4 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG7 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG21 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
    · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG25 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG8 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG3 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG4 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG25 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG25 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
  · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht1a | ht1b | ht1c
    · -- G.natDegree < A.natDegree + E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG19 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG20 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG20 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG15 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG16 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG13 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG14 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG19 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG19 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
    · -- G.natDegree = A.natDegree + E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG13 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG14 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG17 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG23 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
    · -- G.natDegree > A.natDegree + E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG26 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG18 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG13 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG14 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG0 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG26 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBEFG26 ⟨hA, hBne, hCz, hDz, hEne, hFne, hGne, astra4zExhaustTailBEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hDn (by omega)⟩)
end QuarticChamberExhaust810
end Max11DegreeRoutes
end
/-! Part 11 of 15 of `Grok810ScaleZeroQuarticChamberExhaust2Scratch`, split so that no single module elaborates them all
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
/-- Exhaust of the cost-argmin taxonomy on the live set `CDEF`. -/
theorem quarticChamberSupport810_of_live_CDEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · -- F.natDegree < A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF13 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF14 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF3 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF4 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF13 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF13 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
    · -- F.natDegree = A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF8 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF18 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
    · -- F.natDegree > A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF22 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF12 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF12 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF22 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF22 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
  · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · -- F.natDegree < A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF16 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF17 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF6 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF7 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF16 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF16 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
    · -- F.natDegree = A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF5 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF15 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
    · -- F.natDegree > A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF22 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF12 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF12 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF22 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF22 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
  · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF19 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF20 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF9 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF10 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF19 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF19 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
    · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF11 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF21 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, by omega⟩)
    · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF22 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF12 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF12 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF1 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF2 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF0 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF22 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEF22 ⟨hA, hBz, hCne, hDne, hEne, hFne, hGz, astra4zExhaustTailCDEF22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hGn (by omega)⟩)
end QuarticChamberExhaust810
end Max11DegreeRoutes
end
/-! Part 12 of 15 of `Grok810ScaleZeroQuarticChamberExhaust2Scratch`, split so that no single module elaborates them all
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
/-- Exhaust of the cost-argmin taxonomy on the live set `CDEG`. -/
theorem quarticChamberSupport810_of_live_CDEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFz : F = 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG13 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG14 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG3 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG4 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG2 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG13 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG13 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
    · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG2 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG8 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG18 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
    · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG22 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG12 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG12 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG2 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG22 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG22 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
  · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG16 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG17 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG6 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG7 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG2 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG16 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG16 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
    · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG2 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG5 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG15 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
    · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG22 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG12 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG12 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG2 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG22 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG22 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
  · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht1a | ht1b | ht1c
    · -- G.natDegree < A.natDegree + E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG19 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG20 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
        · -- C.natDegree + G.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG9 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG10 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
        · -- C.natDegree + G.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG2 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG19 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG19 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
    · -- G.natDegree = A.natDegree + E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG2 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG11 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG21 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, by omega⟩)
    · -- G.natDegree > A.natDegree + E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG22 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG12 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG12 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG1 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG2 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG0 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG22 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDEG22 ⟨hA, hBz, hCne, hDne, hEne, hFz, hGne, astra4zExhaustTailCDEG22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hFn (by omega)⟩)
end QuarticChamberExhaust810
end Max11DegreeRoutes
end
/-! Part 13 of 15 of `Grok810ScaleZeroQuarticChamberExhaust2Scratch`, split so that no single module elaborates them all
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
private theorem astra4zExhaustTailCDFG0
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hEn : e = 0)
    (hs : a + 2 * f < 4 * c ∧
      g < 2 * c ∧
      a + 2 * d < 3 * c) :
    a + 2 * f < 4 * c ∧
    g < 2 * c ∧
    a + 2 * d < 3 * c ∧
    d + f < 3 * c ∧
    2 * d + 2 * g < a + 6 * c ∧
    2 * f < a + 3 * c ∧
    2 * f + 2 * g < 3 * a + 6 * c ∧
    2 * g < 2 * a + 3 * c ∧
    2 * d < a + 2 * c := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDFG1
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hEn : e = 0)
    (hs : 2 * g < a + 2 * f ∧
      a + 4 * d < 2 * c + 2 * f ∧
      2 * f < 3 * a + 2 * c ∧
      4 * c < a + 2 * f) :
    2 * g < a + 2 * f ∧
    a + 4 * d < 2 * c + 2 * f ∧
    2 * d < a + 2 * c ∧
    d + g < a + c + f ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    4 * g < 5 * a + 2 * c + 2 * f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDFG13
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hEn : e = 0)
    (hs : a + 2 * f < 2 * g ∧
      a + 2 * d < c + g ∧
      g < 2 * a + c ∧
      2 * c < g) :
    a + 2 * f < 2 * g ∧
    a + 2 * d < c + g ∧
    d + f < c + g ∧
    2 * d < a + 2 * c ∧
    2 * f < a + c + g ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    2 * c < g ∧
    2 * c + 2 * d < a + 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDFG14
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hEn : e = 0)
    (hs : g = 2 * c ∧
      a + 2 * f < 2 * g ∧
      a + 2 * d < c + g) :
    g = 2 * c ∧
    a + 2 * f < 2 * g ∧
    a + 2 * d < c + g ∧
    d + f < c + g ∧
    2 * d < a + 2 * c ∧
    2 * f < a + c + g ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    2 * c + 2 * d < a + 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDFG19
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hEn : e = 0)
    (hs : 2 * c + 2 * f < a + 4 * d ∧
      c + g < a + 2 * d ∧
      f < a + d ∧
      2 * g < 3 * a + 2 * d ∧
      3 * c < a + 2 * d) :
    2 * c + 2 * f < a + 4 * d ∧
    c + g < a + 2 * d ∧
    f < a + d ∧
    2 * g < 3 * a + 2 * d ∧
    f < a + d ∧
    2 * f + 2 * g < 5 * a + 4 * d ∧
    2 * g < 3 * a + 2 * d ∧
    3 * c < a + 2 * d ∧
    4 * c < 3 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDFG2
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hEn : e = 0)
    (hs : a + 2 * f = 4 * c ∧
      2 * g < a + 2 * f ∧
      a + 4 * d < 2 * c + 2 * f) :
    a + 2 * f = 4 * c ∧
    2 * g < a + 2 * f ∧
    a + 4 * d < 2 * c + 2 * f ∧
    2 * d < a + 2 * c ∧
    d + g < a + c + f ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    4 * g < 5 * a + 2 * c + 2 * f ∧
    c + d < a + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDFG20
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hEn : e = 0)
    (hs : a + 2 * d = 3 * c ∧
      2 * c + 2 * f < a + 4 * d ∧
      c + g < a + 2 * d) :
    a + 2 * d = 3 * c ∧
    2 * c + 2 * f < a + 4 * d ∧
    c + g < a + 2 * d ∧
    f < a + d ∧
    2 * g < 3 * a + 2 * d ∧
    f < a + d ∧
    2 * f + 2 * g < 5 * a + 4 * d ∧
    2 * g < 3 * a + 2 * d ∧
    4 * c < 3 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDFG24
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hEn : e = 0)
    (hs : 3 * a + 2 * c < 2 * f ∧
      a + d < f ∧
      2 * g < a + 2 * f) :
    3 * a + 2 * c < 2 * f ∧
    a + c + g < 2 * f ∧
    a + d < f ∧
    a + d < f ∧
    a + 2 * d + 2 * g < 4 * f ∧
    2 * g < a + 2 * f ∧
    2 * g < a + 2 * f ∧
    a + 3 * c < 2 * f ∧
    a + 4 * c + 2 * d < 4 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDFG25
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hEn : e = 0)
    (hs : a + 2 * f = 2 * g ∧
      a + c + g < 2 * f ∧
      a + 2 * d + 2 * g < 4 * f) :
    a + 2 * f = 2 * g ∧
    a + 2 * f = 2 * g ∧
    3 * a + 2 * c < 2 * f ∧
    a + c + g < 2 * f ∧
    a + d < f ∧
    a + d < f ∧
    a + 2 * d + 2 * g < 4 * f ∧
    a + 3 * c < 2 * f ∧
    a + 4 * c + 2 * d < 4 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDFG26
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hEn : e = 0)
    (hs : 2 * a + c < g ∧
      3 * a + 2 * d < 2 * g ∧
      a + 2 * f < 2 * g) :
    5 * a + 2 * c + 2 * f < 4 * g ∧
    2 * a + c < g ∧
    3 * a + 2 * d < 2 * g ∧
    2 * a + d + f < 2 * g ∧
    3 * a + 2 * d < 2 * g ∧
    a + 2 * f < 2 * g ∧
    a + 2 * f < 2 * g ∧
    2 * a + 3 * c < 2 * g ∧
    3 * a + 4 * c + 2 * d < 4 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDFG3
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hEn : e = 0)
    (hs : a + 2 * f = 2 * g ∧
      a + 4 * d < 2 * c + 2 * f ∧
      4 * g < 5 * a + 2 * c + 2 * f ∧
      4 * c < a + 2 * f) :
    a + 2 * f = 2 * g ∧
    a + 4 * d < 2 * c + 2 * f ∧
    2 * d < a + 2 * c ∧
    d + g < a + c + f ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    4 * g < 5 * a + 2 * c + 2 * f ∧
    4 * c < a + 2 * f ∧
    c + d < a + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCDFG4
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hEn : e = 0)
    (hs : a + 2 * f = 2 * g ∧
      a + 2 * f = 4 * c ∧
      a + 4 * d < 2 * c + 2 * f) :
    a + 2 * f = 2 * g ∧
    a + 2 * f = 4 * c ∧
    a + 4 * d < 2 * c + 2 * f ∧
    2 * d < a + 2 * c ∧
    d + g < a + c + f ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    4 * g < 5 * a + 2 * c + 2 * f ∧
    c + d < a + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCEFG0
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hDn : d = 0)
    (hs : a + 2 * f < 4 * c ∧
      g < 2 * c ∧
      2 * e < 3 * c) :
    a + 2 * f < 4 * c ∧
    g < 2 * c ∧
    2 * e < 3 * c ∧
    2 * e + 2 * f < a + 6 * c ∧
    e + g < a + 3 * c ∧
    2 * f < a + 3 * c ∧
    2 * f + 2 * g < 3 * a + 6 * c ∧
    2 * g < 2 * a + 3 * c ∧
    e < a + c := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCEFG1
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hDn : d = 0)
    (hs : 2 * g < a + 2 * f ∧
      4 * e < a + 2 * c + 2 * f ∧
      2 * f < 3 * a + 2 * c ∧
      4 * c < a + 2 * f) :
    2 * g < a + 2 * f ∧
    4 * e < a + 2 * c + 2 * f ∧
    e < a + c ∧
    2 * e + 2 * g < 3 * a + 2 * c + 2 * f ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    4 * g < 5 * a + 2 * c + 2 * f ∧
    4 * c < a + 2 * f ∧
    2 * c + 2 * e < 3 * a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCEFG13
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hDn : d = 0)
    (hs : a + 2 * f < 2 * g ∧
      2 * e < c + g ∧
      g < 2 * a + c ∧
      2 * c < g) :
    a + 2 * f < 2 * g ∧
    2 * e < c + g ∧
    2 * e + 2 * f < a + 2 * c + 2 * g ∧
    e < a + c ∧
    2 * f < a + c + g ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    2 * c < g ∧
    c + e < a + g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCEFG14
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hDn : d = 0)
    (hs : g = 2 * c ∧
      a + 2 * f < 2 * g ∧
      2 * e < c + g) :
    g = 2 * c ∧
    a + 2 * f < 2 * g ∧
    2 * e < c + g ∧
    2 * e + 2 * f < a + 2 * c + 2 * g ∧
    e < a + c ∧
    2 * f < a + c + g ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    c + e < a + g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCEFG19
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hDn : d = 0)
    (hs : a + 2 * c + 2 * f < 4 * e ∧
      c + g < 2 * e ∧
      2 * f < a + 2 * e ∧
      g < a + e ∧
      3 * c < 2 * e) :
    a + 2 * c + 2 * f < 4 * e ∧
    c + g < 2 * e ∧
    2 * f < a + 2 * e ∧
    g < a + e ∧
    2 * f < a + 2 * e ∧
    2 * f + 2 * g < 3 * a + 4 * e ∧
    g < a + e ∧
    3 * c < 2 * e ∧
    2 * c < a + e := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCEFG2
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hDn : d = 0)
    (hs : a + 2 * f = 4 * c ∧
      2 * g < a + 2 * f ∧
      4 * e < a + 2 * c + 2 * f) :
    a + 2 * f = 4 * c ∧
    2 * g < a + 2 * f ∧
    4 * e < a + 2 * c + 2 * f ∧
    e < a + c ∧
    2 * e + 2 * g < 3 * a + 2 * c + 2 * f ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    4 * g < 5 * a + 2 * c + 2 * f ∧
    2 * c + 2 * e < 3 * a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCEFG20
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hDn : d = 0)
    (hs : 2 * e = 3 * c ∧
      a + 2 * c + 2 * f < 4 * e ∧
      c + g < 2 * e) :
    2 * e = 3 * c ∧
    a + 2 * c + 2 * f < 4 * e ∧
    c + g < 2 * e ∧
    2 * f < a + 2 * e ∧
    g < a + e ∧
    2 * f < a + 2 * e ∧
    2 * f + 2 * g < 3 * a + 4 * e ∧
    g < a + e ∧
    2 * c < a + e := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCEFG24
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hDn : d = 0)
    (hs : 3 * a + 2 * c < 2 * f ∧
      a + 2 * e < 2 * f ∧
      2 * g < a + 2 * f) :
    3 * a + 2 * c < 2 * f ∧
    a + c + g < 2 * f ∧
    a + 2 * e < 2 * f ∧
    a + 2 * e < 2 * f ∧
    e + g < 2 * f ∧
    2 * g < a + 2 * f ∧
    2 * g < a + 2 * f ∧
    a + 3 * c < 2 * f ∧
    2 * c + e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCEFG25
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hDn : d = 0)
    (hs : a + 2 * f = 2 * g ∧
      a + c + g < 2 * f ∧
      e + g < 2 * f) :
    a + 2 * f = 2 * g ∧
    a + 2 * f = 2 * g ∧
    3 * a + 2 * c < 2 * f ∧
    a + c + g < 2 * f ∧
    a + 2 * e < 2 * f ∧
    a + 2 * e < 2 * f ∧
    e + g < 2 * f ∧
    a + 3 * c < 2 * f ∧
    2 * c + e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCEFG26
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hDn : d = 0)
    (hs : 2 * a + c < g ∧
      a + e < g ∧
      a + 2 * f < 2 * g) :
    5 * a + 2 * c + 2 * f < 4 * g ∧
    2 * a + c < g ∧
    a + e < g ∧
    3 * a + 2 * e + 2 * f < 4 * g ∧
    a + e < g ∧
    a + 2 * f < 2 * g ∧
    a + 2 * f < 2 * g ∧
    2 * a + 3 * c < 2 * g ∧
    a + 2 * c + e < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCEFG3
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hDn : d = 0)
    (hs : a + 2 * f = 2 * g ∧
      4 * e < a + 2 * c + 2 * f ∧
      4 * g < 5 * a + 2 * c + 2 * f ∧
      4 * c < a + 2 * f) :
    a + 2 * f = 2 * g ∧
    4 * e < a + 2 * c + 2 * f ∧
    e < a + c ∧
    2 * e + 2 * g < 3 * a + 2 * c + 2 * f ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    4 * g < 5 * a + 2 * c + 2 * f ∧
    4 * c < a + 2 * f ∧
    2 * c + 2 * e < 3 * a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailCEFG4
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hDn : d = 0)
    (hs : a + 2 * f = 2 * g ∧
      a + 2 * f = 4 * c ∧
      4 * e < a + 2 * c + 2 * f) :
    a + 2 * f = 2 * g ∧
    a + 2 * f = 4 * c ∧
    4 * e < a + 2 * c + 2 * f ∧
    e < a + c ∧
    2 * e + 2 * g < 3 * a + 2 * c + 2 * f ∧
    2 * f < 3 * a + 2 * c ∧
    g < 2 * a + c ∧
    4 * g < 5 * a + 2 * c + 2 * f ∧
    2 * c + 2 * e < 3 * a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailDEFG0
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hCn : c = 0)
    (hs : 2 * e < a + 2 * d ∧
      f < a + d ∧
      2 * g < 3 * a + 2 * d) :
    2 * e < a + 2 * d ∧
    f < a + d ∧
    2 * g < 3 * a + 2 * d ∧
    2 * e < a + 2 * d ∧
    2 * e + 2 * f < 3 * a + 4 * d ∧
    e + g < 2 * a + 2 * d ∧
    f < a + d ∧
    2 * f + 2 * g < 5 * a + 4 * d ∧
    2 * g < 3 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailDEFG12
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hCn : c = 0)
    (hs : a + d < f ∧
      a + 2 * e < 2 * f ∧
      2 * g < a + 2 * f) :
    a + d < f ∧
    3 * a + 2 * d + 2 * e < 4 * f ∧
    a + d < f ∧
    a + 2 * d + 2 * g < 4 * f ∧
    a + 2 * e < 2 * f ∧
    a + 2 * e < 2 * f ∧
    e + g < 2 * f ∧
    2 * g < a + 2 * f ∧
    2 * g < a + 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailDEFG13
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hCn : c = 0)
    (hs : a + 2 * f = 2 * g ∧
      a + 2 * d + 2 * g < 4 * f ∧
      e + g < 2 * f) :
    a + 2 * f = 2 * g ∧
    a + 2 * f = 2 * g ∧
    a + d < f ∧
    3 * a + 2 * d + 2 * e < 4 * f ∧
    a + d < f ∧
    a + 2 * d + 2 * g < 4 * f ∧
    a + 2 * e < 2 * f ∧
    a + 2 * e < 2 * f ∧
    e + g < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailDEFG14
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hCn : c = 0)
    (hs : 3 * a + 2 * d < 2 * g ∧
      a + e < g ∧
      a + 2 * f < 2 * g) :
    3 * a + 2 * d < 2 * g ∧
    5 * a + 2 * d + 2 * e < 4 * g ∧
    2 * a + d + f < 2 * g ∧
    3 * a + 2 * d < 2 * g ∧
    a + e < g ∧
    3 * a + 2 * e + 2 * f < 4 * g ∧
    a + e < g ∧
    a + 2 * f < 2 * g ∧
    a + 2 * f < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailDEFG4
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hCn : c = 0)
    (hs : a + 2 * d = 2 * e ∧
      2 * e + 2 * f < 3 * a + 4 * d ∧
      e + g < 2 * a + 2 * d) :
    a + 2 * d = 2 * e ∧
    a + 2 * d = 2 * e ∧
    f < a + d ∧
    2 * g < 3 * a + 2 * d ∧
    2 * e + 2 * f < 3 * a + 4 * d ∧
    e + g < 2 * a + 2 * d ∧
    f < a + d ∧
    2 * f + 2 * g < 5 * a + 4 * d ∧
    2 * g < 3 * a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailDEFG8
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hBn : b = 0)
    (hCn : c = 0)
    (hs : a + 2 * d < 2 * e ∧
      2 * f < a + 2 * e ∧
      g < a + e) :
    a + 2 * d < 2 * e ∧
    a + 2 * d < 2 * e ∧
    d + f < 2 * e ∧
    2 * d + 2 * g < a + 4 * e ∧
    2 * f < a + 2 * e ∧
    g < a + e ∧
    2 * f < a + 2 * e ∧
    2 * f + 2 * g < 3 * a + 4 * e ∧
    g < a + e := by
  omega

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `CDFG`. -/
theorem quarticChamberSupport810_of_live_CDFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCne : C ≠ 0) (hDne : D ≠ 0) (hEz : E = 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · -- F.natDegree < A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG19 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG20 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG20 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG9 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG10 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG1 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG2 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG19 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG19 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
    · -- F.natDegree = A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG1 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG2 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG11 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG22 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
    · -- F.natDegree > A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG24 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG24 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG12 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG1 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG2 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG24 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG24 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG24 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG24 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
  · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · -- F.natDegree < A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * C.natDegree + 2 * F.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG19 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG20 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG20 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG5 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG6 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG3 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG4 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG19 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG19 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
    · -- F.natDegree = A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * C.natDegree + 2 * F.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- 2 * C.natDegree + 2 * F.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG3 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG4 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG7 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG21 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
    · -- F.natDegree > A.natDegree + D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG25 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG8 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG3 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG4 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG25 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG25 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
  · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG19 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG20 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG20 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
        · -- C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (A.natDegree + 2 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG15 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG16 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG13 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG14 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG19 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG19 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
    · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (A.natDegree + 2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > A.natDegree + 2 * D.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG13 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG14 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG17 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG23 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
    · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (2 * D.natDegree) (A.natDegree + 2 * C.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * D.natDegree < A.natDegree + 2 * C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG26 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG18 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, by omega⟩)
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG13 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG14 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG0 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG26 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCDFG26 ⟨hA, hBz, hCne, hDne, hEz, hFne, hGne, astra4zExhaustTailCDFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hEn (by omega)⟩)
end QuarticChamberExhaust810
end Max11DegreeRoutes
end
/-! Part 14 of 15 of `Grok810ScaleZeroQuarticChamberExhaust2Scratch`, split so that no single module elaborates them all
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
/-- Exhaust of the cost-argmin taxonomy on the live set `CEFG`. -/
theorem quarticChamberSupport810_of_live_CEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCne : C ≠ 0) (hDz : D = 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG19 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG20 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG20 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG9 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG10 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG1 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG2 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG19 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG19 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
    · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG1 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG2 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG11 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG22 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
    · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG24 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG24 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG12 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG1 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG2 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG24 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG24 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG24 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG24 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
  · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG19 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG20 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG20 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG5 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG6 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG3 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG4 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG19 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG19 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
    · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * C.natDegree + 2 * F.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- A.natDegree + 2 * C.natDegree + 2 * F.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG3 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG4 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG7 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG21 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
    · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG25 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG8 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
          rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG3 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG4 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG25 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG25 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
  · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht1a | ht1b | ht1c
    · -- G.natDegree < A.natDegree + E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG19 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG20 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG20 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
        · -- C.natDegree + G.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG15 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG16 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
        · -- C.natDegree + G.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG13 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG14 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG19 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG19 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
    · -- G.natDegree = A.natDegree + E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG13 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG14 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG17 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG23 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
    · -- G.natDegree > A.natDegree + E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG26 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG18 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, by omega⟩)
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG13 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG14 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG0 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG26 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cCEFG26 ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne, astra4zExhaustTailCEFG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hDn (by omega)⟩)
end QuarticChamberExhaust810
end Max11DegreeRoutes
end
/-! Part 15 of 15 of `Grok810ScaleZeroQuarticChamberExhaust2Scratch`, split so that no single module elaborates them all
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
/-- Exhaust of the cost-argmin taxonomy on the live set `DEFG`. -/
theorem quarticChamberSupport810_of_live_DEFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBz : B = 0) (hCz : C = 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hCn : C.natDegree = 0 := by simp [hCz]
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG0 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hCn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG6 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG12 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailDEFG12 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hCn (by omega)⟩)
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG0 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hCn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG5 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG13 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailDEFG13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hCn (by omega)⟩)
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG0 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailDEFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hCn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG7 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG14 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailDEFG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hCn (by omega)⟩)
  · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG4 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailDEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hCn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG2 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG12 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailDEFG12 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hCn (by omega)⟩)
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG4 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailDEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hCn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG1 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG13 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailDEFG13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hCn (by omega)⟩)
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG4 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailDEFG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hCn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG3 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG14 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailDEFG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hCn (by omega)⟩)
  · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG8 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailDEFG8 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hCn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG10 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG12 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailDEFG12 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hCn (by omega)⟩)
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG8 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailDEFG8 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hCn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG9 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG13 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailDEFG13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hCn (by omega)⟩)
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG8 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailDEFG8 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hCn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG11 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cDEFG14 ⟨hA, hBz, hCz, hDne, hEne, hFne, hGne, astra4zExhaustTailDEFG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hBn hCn (by omega)⟩)



end QuarticChamberExhaust810
end Max11DegreeRoutes
end
