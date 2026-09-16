import Grok810ScaleZeroQuarticChamberDefs4Scratch

/-! Part 5 of 15 of `Grok810ScaleZeroQuarticChamberExhaust2Scratch`, split so that no single module elaborates them all
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
private theorem astra4zExhaustTailBCEG0
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hFn : f = 0)
    (hs : g < a + 2 * b ∧
      4 * e < 3 * a + 6 * b ∧
      2 * c < a + 2 * b) :
    g < a + 2 * b ∧
    2 * c + 2 * g < 3 * a + 6 * b ∧
    4 * e < 3 * a + 6 * b ∧
    2 * e + 2 * g < 5 * a + 6 * b ∧
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
private theorem astra4zExhaustTailBCEG1
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hFn : f = 0)
    (hs : a + 2 * b = 2 * c ∧
      2 * c + 2 * g < 3 * a + 6 * b ∧
      4 * e < 3 * a + 6 * b) :
    a + 2 * b = 2 * c ∧
    a + 2 * b = 2 * c ∧
    a + 2 * b = 2 * c ∧
    g < a + 2 * b ∧
    2 * c + 2 * g < 3 * a + 6 * b ∧
    4 * e < 3 * a + 6 * b ∧
    2 * e + 2 * g < 5 * a + 6 * b ∧
    4 * g < 7 * a + 6 * b ∧
    2 * e < 3 * a + 2 * b ∧
    c + e < 2 * a + 2 * b ∧
    4 * c + 2 * e < 5 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCEG14
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hFn : f = 0)
    (hs : g < 2 * c ∧
      2 * e < 3 * c ∧
      a + 2 * b < 2 * c) :
    a + 2 * b + 2 * g < 6 * c ∧
    g < 2 * c ∧
    2 * e < 3 * c ∧
    e + g < a + 3 * c ∧
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
private theorem astra4zExhaustTailBCEG15
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hFn : f = 0)
    (hs : a + 2 * b < 2 * c ∧
      2 * e < c + g ∧
      g < 2 * a + c ∧
      2 * c < g) :
    a + 2 * b < 2 * c ∧
    2 * e < c + g ∧
    e < a + c ∧
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
private theorem astra4zExhaustTailBCEG16
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hFn : f = 0)
    (hs : g = 2 * c ∧
      2 * e < c + g ∧
      a + 2 * b + 2 * c < 2 * g) :
    g = 2 * c ∧
    a + 2 * b < 2 * c ∧
    2 * e < c + g ∧
    e < a + c ∧
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
private theorem astra4zExhaustTailBCEG2
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hFn : f = 0)
    (hs : 2 * c < a + 2 * b ∧
      4 * e < a + 2 * b + 2 * g ∧
      2 * g < 5 * a + 2 * b ∧
      a + 2 * b < g) :
    2 * c < a + 2 * b ∧
    4 * e < a + 2 * b + 2 * g ∧
    2 * e < 3 * a + 2 * b ∧
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
private theorem astra4zExhaustTailBCEG21
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hFn : f = 0)
    (hs : a + 2 * b + 2 * g < 4 * e ∧
      c + g < 2 * e ∧
      g < a + e ∧
      3 * a + 6 * b < 4 * e ∧
      3 * c < 2 * e) :
    a + 2 * b + 2 * g < 4 * e ∧
    c + g < 2 * e ∧
    g < a + e ∧
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
private theorem astra4zExhaustTailBCEG25
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hFn : f = 0)
    (hs : a + e = g ∧
      a + 2 * b + 2 * g < 4 * e ∧
      c + g < 2 * e) :
    a + e = g ∧
    a + e = g ∧
    a + 2 * b + 2 * g < 4 * e ∧
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
private theorem astra4zExhaustTailBCEG26
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hFn : f = 0)
    (hs : 5 * a + 2 * b < 2 * g ∧
      2 * a + c < g ∧
      a + e < g) :
    5 * a + 2 * b < 2 * g ∧
    2 * a + c < g ∧
    a + e < g ∧
    a + e < g ∧
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
private theorem astra4zExhaustTailBCEG3
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hFn : f = 0)
    (hs : g = a + 2 * b ∧
      4 * e < a + 2 * b + 2 * g ∧
      6 * c < a + 2 * b + 2 * g) :
    g = a + 2 * b ∧
    2 * c < a + 2 * b ∧
    4 * e < a + 2 * b + 2 * g ∧
    2 * e < 3 * a + 2 * b ∧
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
private theorem astra4zExhaustTailBCEG4
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hFn : f = 0)
    (hs : a + 2 * b = 2 * c ∧
      4 * e < a + 2 * b + 2 * g ∧
      2 * g < 5 * a + 2 * b ∧
      6 * c < a + 2 * b + 2 * g) :
    a + 2 * b = 2 * c ∧
    4 * e < a + 2 * b + 2 * g ∧
    2 * e < 3 * a + 2 * b ∧
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
private theorem astra4zExhaustTailBCEG5
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hFn : f = 0)
    (hs : g = 2 * c ∧
      a + 2 * b + 2 * g = 6 * c ∧
      4 * e < a + 2 * b + 2 * g) :
    a + 2 * b = 2 * c ∧
    g = a + 2 * b ∧
    2 * g = a + 2 * b + 2 * c ∧
    g = 2 * c ∧
    a + 2 * b + 2 * g = 6 * c ∧
    4 * e < a + 2 * b + 2 * g ∧
    2 * e < 3 * a + 2 * b ∧
    2 * g < 5 * a + 2 * b ∧
    2 * b + 2 * e < a + 2 * g ∧
    c + e < a + g ∧
    4 * c + 2 * e < 3 * a + 2 * b + 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCFG0
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hEn : e = 0)
    (hs : 2 * f < a + 4 * b ∧
      g < a + 2 * b ∧
      2 * c < a + 2 * b) :
    2 * f < a + 4 * b ∧
    g < a + 2 * b ∧
    c + f < a + 3 * b ∧
    2 * c + 2 * g < 3 * a + 6 * b ∧
    4 * f < 5 * a + 6 * b ∧
    f + g < 3 * a + 3 * b ∧
    4 * g < 7 * a + 6 * b ∧
    2 * c < a + 2 * b ∧
    2 * c < a + 2 * b ∧
    2 * c < a + 2 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCFG1
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hEn : e = 0)
    (hs : a + 2 * b = 2 * c ∧
      c + f < a + 3 * b ∧
      2 * c + 2 * g < 3 * a + 6 * b) :
    a + 2 * b = 2 * c ∧
    a + 2 * b = 2 * c ∧
    a + 2 * b = 2 * c ∧
    2 * f < a + 4 * b ∧
    g < a + 2 * b ∧
    c + f < a + 3 * b ∧
    2 * c + 2 * g < 3 * a + 6 * b ∧
    4 * f < 5 * a + 6 * b ∧
    f + g < 3 * a + 3 * b ∧
    4 * g < 7 * a + 6 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCFG20
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hEn : e = 0)
    (hs : a + 2 * f < 4 * c ∧
      g < 2 * c ∧
      a + 2 * b < 2 * c) :
    a + b + f < 3 * c ∧
    a + 2 * b + 2 * g < 6 * c ∧
    a + 2 * f < 4 * c ∧
    g < 2 * c ∧
    2 * f < a + 3 * c ∧
    2 * f + 2 * g < 3 * a + 6 * c ∧
    2 * g < 2 * a + 3 * c ∧
    a + 2 * b < 2 * c ∧
    a + 2 * b < 2 * c ∧
    a + 2 * b < 2 * c := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCFG30
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hEn : e = 0)
    (hs : 2 * a + b < f ∧
      3 * a + 2 * c < 2 * f ∧
      2 * g < a + 2 * f) :
    2 * a + b < f ∧
    3 * a + 2 * b + 2 * g < 4 * f ∧
    3 * a + 2 * c < 2 * f ∧
    a + c + g < 2 * f ∧
    2 * g < a + 2 * f ∧
    2 * g < a + 2 * f ∧
    5 * a + 6 * b < 4 * f ∧
    2 * a + 2 * b + c < 2 * f ∧
    3 * a + 2 * b + 4 * c < 4 * f ∧
    a + 3 * c < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCFG31
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hEn : e = 0)
    (hs : a + 2 * f = 2 * g ∧
      3 * a + 2 * b + 2 * g < 4 * f ∧
      a + c + g < 2 * f) :
    a + 2 * f = 2 * g ∧
    a + 2 * f = 2 * g ∧
    2 * a + b < f ∧
    3 * a + 2 * b + 2 * g < 4 * f ∧
    3 * a + 2 * c < 2 * f ∧
    a + c + g < 2 * f ∧
    5 * a + 6 * b < 4 * f ∧
    2 * a + 2 * b + c < 2 * f ∧
    3 * a + 2 * b + 4 * c < 4 * f ∧
    a + 3 * c < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBCFG32
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hDn : d = 0)
    (hEn : e = 0)
    (hs : 5 * a + 2 * b < 2 * g ∧
      2 * a + c < g ∧
      a + 2 * f < 2 * g) :
    3 * a + b + f < 2 * g ∧
    5 * a + 2 * b < 2 * g ∧
    5 * a + 2 * c + 2 * f < 4 * g ∧
    2 * a + c < g ∧
    a + 2 * f < 2 * g ∧
    a + 2 * f < 2 * g ∧
    7 * a + 6 * b < 4 * g ∧
    3 * a + 2 * b + c < 2 * g ∧
    5 * a + 2 * b + 4 * c < 4 * g ∧
    2 * a + 3 * c < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEF0
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hGn : g = 0)
    (hs : 2 * f < a + 4 * b ∧
      4 * d < a + 6 * b ∧
      4 * e < 3 * a + 6 * b) :
    2 * f < a + 4 * b ∧
    4 * d < a + 6 * b ∧
    d + e < a + 3 * b ∧
    2 * d + 2 * f < 3 * a + 6 * b ∧
    4 * e < 3 * a + 6 * b ∧
    e + f < 2 * a + 3 * b ∧
    4 * f < 5 * a + 6 * b ∧
    d < a + b ∧
    2 * e < 3 * a + 2 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEF1
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hGn : g = 0)
    (hs : 2 * d < b + f ∧
      2 * e < a + b + f ∧
      f < 2 * a + b ∧
      a + 4 * b < 2 * f) :
    2 * d < b + f ∧
    2 * d + 2 * e < a + 2 * b + 2 * f ∧
    d < a + b ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    f < 2 * a + b ∧
    a + 4 * b < 2 * f ∧
    2 * b + 2 * d < a + 2 * f ∧
    b + e < a + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEF12
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hGn : g = 0)
    (hs : 2 * a + b = f ∧
      d < a + b ∧
      2 * e < 3 * a + 2 * b) :
    2 * a + b = f ∧
    2 * d < b + f ∧
    2 * d + 2 * e < a + 2 * b + 2 * f ∧
    d < a + b ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    a + 4 * b < 2 * f ∧
    2 * b + 2 * d < a + 2 * f ∧
    b + e < a + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEF13
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hGn : g = 0)
    (hs : b + f < 2 * d ∧
      2 * e < a + 2 * d ∧
      f < a + d ∧
      a + 6 * b < 4 * d) :
    b + f < 2 * d ∧
    2 * e < a + 2 * d ∧
    f < a + d ∧
    2 * e < a + 2 * d ∧
    2 * e + 2 * f < 3 * a + 4 * d ∧
    f < a + d ∧
    a + 6 * b < 4 * d ∧
    4 * b < a + 2 * d ∧
    2 * b + e < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEF16
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hGn : g = 0)
    (hs : a + 2 * d = 2 * e ∧
      b + f < 2 * d ∧
      2 * e + 2 * f < 3 * a + 4 * d ∧
      a + 6 * b < 4 * d) :
    a + 2 * d = 2 * e ∧
    a + 2 * d = 2 * e ∧
    b + f < 2 * d ∧
    f < a + d ∧
    2 * e + 2 * f < 3 * a + 4 * d ∧
    f < a + d ∧
    a + 6 * b < 4 * d ∧
    4 * b < a + 2 * d ∧
    2 * b + e < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEF19
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hGn : g = 0)
    (hs : a + b + f < 2 * e ∧
      a + 2 * d < 2 * e ∧
      2 * f < a + 2 * e ∧
      3 * a + 6 * b < 4 * e) :
    a + b + f < 2 * e ∧
    a + 2 * d < 2 * e ∧
    a + 2 * d < 2 * e ∧
    d + f < 2 * e ∧
    2 * f < a + 2 * e ∧
    2 * f < a + 2 * e ∧
    3 * a + 6 * b < 4 * e ∧
    a + 4 * b + 2 * d < 4 * e ∧
    2 * b < e := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEF2
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hGn : g = 0)
    (hs : 2 * f = a + 4 * b ∧
      2 * d < b + f ∧
      2 * e < a + b + f) :
    2 * f = a + 4 * b ∧
    2 * d < b + f ∧
    2 * d + 2 * e < a + 2 * b + 2 * f ∧
    d < a + b ∧
    2 * e < a + b + f ∧
    2 * e < 3 * a + 2 * b ∧
    f < 2 * a + b ∧
    2 * b + 2 * d < a + 2 * f ∧
    b + e < a + f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEF22
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hGn : g = 0)
    (hs : 2 * a + b < f ∧
      a + d < f ∧
      a + 2 * e < 2 * f) :
    2 * a + b < f ∧
    a + d < f ∧
    3 * a + 2 * d + 2 * e < 4 * f ∧
    a + d < f ∧
    a + 2 * e < 2 * f ∧
    a + 2 * e < 2 * f ∧
    5 * a + 6 * b < 4 * f ∧
    3 * a + 4 * b + 2 * d < 4 * f ∧
    a + 2 * b + e < 2 * f := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEG0
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hFn : f = 0)
    (hs : g < a + 2 * b ∧
      4 * d < a + 6 * b ∧
      4 * e < 3 * a + 6 * b) :
    g < a + 2 * b ∧
    4 * d < a + 6 * b ∧
    d + e < a + 3 * b ∧
    d + g < 2 * a + 3 * b ∧
    4 * e < 3 * a + 6 * b ∧
    2 * e + 2 * g < 5 * a + 6 * b ∧
    4 * g < 7 * a + 6 * b ∧
    d < a + b ∧
    2 * e < 3 * a + 2 * b := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEG1
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hFn : f = 0)
    (hs : a + 4 * d < 2 * b + 2 * g ∧
      4 * e < a + 2 * b + 2 * g ∧
      2 * g < 5 * a + 2 * b ∧
      a + 2 * b < g) :
    a + 4 * d < 2 * b + 2 * g ∧
    d + e < b + g ∧
    d < a + b ∧
    4 * e < a + 2 * b + 2 * g ∧
    2 * e < 3 * a + 2 * b ∧
    2 * g < 5 * a + 2 * b ∧
    a + 2 * b < g ∧
    b + d < g ∧
    2 * b + 2 * e < a + 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEG12
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hFn : f = 0)
    (hs : 5 * a + 2 * b = 2 * g ∧
      d < a + b ∧
      2 * e < 3 * a + 2 * b) :
    5 * a + 2 * b = 2 * g ∧
    a + 4 * d < 2 * b + 2 * g ∧
    d + e < b + g ∧
    d < a + b ∧
    4 * e < a + 2 * b + 2 * g ∧
    2 * e < 3 * a + 2 * b ∧
    a + 2 * b < g ∧
    b + d < g ∧
    2 * b + 2 * e < a + 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEG13
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hFn : f = 0)
    (hs : 2 * b + 2 * g < a + 4 * d ∧
      2 * e < a + 2 * d ∧
      2 * g < 3 * a + 2 * d ∧
      a + 6 * b < 4 * d) :
    2 * b + 2 * g < a + 4 * d ∧
    2 * e < a + 2 * d ∧
    2 * g < 3 * a + 2 * d ∧
    2 * e < a + 2 * d ∧
    e + g < 2 * a + 2 * d ∧
    2 * g < 3 * a + 2 * d ∧
    a + 6 * b < 4 * d ∧
    4 * b < a + 2 * d ∧
    2 * b + e < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEG16
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hFn : f = 0)
    (hs : a + 2 * d = 2 * e ∧
      2 * b + 2 * g < a + 4 * d ∧
      e + g < 2 * a + 2 * d ∧
      a + 6 * b < 4 * d) :
    a + 2 * d = 2 * e ∧
    a + 2 * d = 2 * e ∧
    2 * b + 2 * g < a + 4 * d ∧
    2 * g < 3 * a + 2 * d ∧
    e + g < 2 * a + 2 * d ∧
    2 * g < 3 * a + 2 * d ∧
    a + 6 * b < 4 * d ∧
    4 * b < a + 2 * d ∧
    2 * b + e < a + 2 * d := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEG19
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hFn : f = 0)
    (hs : a + 2 * b + 2 * g < 4 * e ∧
      a + 2 * d < 2 * e ∧
      g < a + e ∧
      3 * a + 6 * b < 4 * e) :
    a + 2 * b + 2 * g < 4 * e ∧
    a + 2 * d < 2 * e ∧
    a + 2 * d < 2 * e ∧
    2 * d + 2 * g < a + 4 * e ∧
    g < a + e ∧
    g < a + e ∧
    3 * a + 6 * b < 4 * e ∧
    a + 4 * b + 2 * d < 4 * e ∧
    2 * b < e := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEG2
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hFn : f = 0)
    (hs : g = a + 2 * b ∧
      a + 4 * d < 2 * b + 2 * g ∧
      4 * e < a + 2 * b + 2 * g) :
    g = a + 2 * b ∧
    a + 4 * d < 2 * b + 2 * g ∧
    d + e < b + g ∧
    d < a + b ∧
    4 * e < a + 2 * b + 2 * g ∧
    2 * e < 3 * a + 2 * b ∧
    2 * g < 5 * a + 2 * b ∧
    b + d < g ∧
    2 * b + 2 * e < a + 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Reusable arithmetic implication for one cost chamber. -/
private theorem astra4zExhaustTailBDEG22
    (a b c d e f g : ℕ)
    (hApos : 0 < a) (hAB : 2 * b < 3 * a) (hAC : c < 2 * a) (hAD : 2 * d < 5 * a) (hAE : e < 3 * a) (hAF : 2 * f < 7 * a) (hAG : g < 4 * a)
    (hCn : c = 0)
    (hFn : f = 0)
    (hs : 5 * a + 2 * b < 2 * g ∧
      3 * a + 2 * d < 2 * g ∧
      a + e < g) :
    5 * a + 2 * b < 2 * g ∧
    3 * a + 2 * d < 2 * g ∧
    5 * a + 2 * d + 2 * e < 4 * g ∧
    3 * a + 2 * d < 2 * g ∧
    a + e < g ∧
    a + e < g ∧
    7 * a + 6 * b < 4 * g ∧
    5 * a + 4 * b + 2 * d < 4 * g ∧
    2 * a + 2 * b + e < 2 * g := by
  omega

set_option maxHeartbeats 64000000 in
/-- Exhaust of the cost-argmin taxonomy on the live set `BCEG`. -/
theorem quarticChamberSupport810_of_live_BCEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDz : D = 0) (hEne : E ≠ 0) (hFz : F = 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht1a | ht1b | ht1c
    · -- G.natDegree < A.natDegree + E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG21 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG22 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG0 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG10 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG11 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG0 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG2 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG3 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG0 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG21 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG21 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
    · -- G.natDegree = A.natDegree + E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG2 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG3 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG0 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG12 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG25 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
    · -- G.natDegree > A.natDegree + E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG26 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG13 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG2 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG3 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG3 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG0 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG26 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG26 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht1a | ht1b | ht1c
    · -- G.natDegree < A.natDegree + E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG21 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG23 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG1 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG6 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG7 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG1 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG4 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG5 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG1 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG21 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG21 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
    · -- G.natDegree = A.natDegree + E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG4 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG5 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG1 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG8 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG25 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
    · -- G.natDegree > A.natDegree + E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG26 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG9 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG4 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG4 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG5 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG5 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG1 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG26 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG26 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht1a | ht1b | ht1c
    · -- G.natDegree < A.natDegree + E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- C.natDegree + G.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG21 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG24 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG14 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
        · -- C.natDegree + G.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * C.natDegree) (2 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG17 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG18 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG14 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
        · -- C.natDegree + G.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG15 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG15 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG16 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG14 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG21 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG21 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG21 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
    · -- G.natDegree = A.natDegree + E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (C.natDegree + G.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- C.natDegree + G.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG15 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG15 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG16 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG14 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG19 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG25 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG25 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
    · -- G.natDegree > A.natDegree + E.natDegree
      rcases lt_trichotomy (E.natDegree) (A.natDegree + C.natDegree) with ht2a | ht2b | ht2c
      · -- E.natDegree < A.natDegree + C.natDegree
        rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG26 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG20 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, by omega⟩)
        · -- 2 * A.natDegree + C.natDegree > G.natDegree
          rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG15 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG15 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG16 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG14 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG14 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG26 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCEG26 ⟨hA, hBne, hCne, hDz, hEne, hFz, hGne, astra4zExhaustTailBCEG26 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hFn (by omega)⟩)
end QuarticChamberExhaust810
end Max11DegreeRoutes
end
/-! Part 6 of 15 of `Grok810ScaleZeroQuarticChamberExhaust2Scratch`, split so that no single module elaborates them all
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
/-- Exhaust of the cost-argmin taxonomy on the live set `BCFG`. -/
theorem quarticChamberSupport810_of_live_BCFG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCne : C ≠ 0) (hDz : D = 0) (hEz : E = 0) (hFne : F ≠ 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  rcases lt_trichotomy (2 * C.natDegree) (A.natDegree + 2 * B.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * C.natDegree < A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG30 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, astra4zExhaustTailBCFG30 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG13 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 2 * A.natDegree + B.natDegree > F.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG2 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG3 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG0 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, astra4zExhaustTailBCFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hEn (by omega)⟩)
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG31 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, astra4zExhaustTailBCFG31 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG9 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 2 * A.natDegree + B.natDegree > F.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG4 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG5 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG0 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, astra4zExhaustTailBCFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hEn (by omega)⟩)
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG32 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, astra4zExhaustTailBCFG32 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG19 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG14 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG15 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG0 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, astra4zExhaustTailBCFG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hEn (by omega)⟩)
  · -- 2 * C.natDegree = A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG30 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, astra4zExhaustTailBCFG30 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG12 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 2 * A.natDegree + B.natDegree > F.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG10 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG11 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG1 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, astra4zExhaustTailBCFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hEn (by omega)⟩)
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG31 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, astra4zExhaustTailBCFG31 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG8 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 2 * A.natDegree + B.natDegree > F.natDegree
        rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG6 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG7 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG1 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, astra4zExhaustTailBCFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hEn (by omega)⟩)
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG32 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, astra4zExhaustTailBCFG32 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG18 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG16 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG17 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG1 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, astra4zExhaustTailBCFG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hEn (by omega)⟩)
  · -- 2 * C.natDegree > A.natDegree + 2 * B.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (A.natDegree + 2 * F.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG30 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, astra4zExhaustTailBCFG30 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG26 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG21 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG22 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG20 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, astra4zExhaustTailBCFG20 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hEn (by omega)⟩)
    · -- 2 * G.natDegree = A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (3 * A.natDegree + 2 * C.natDegree) (2 * F.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG31 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, astra4zExhaustTailBCFG31 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG25 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 3 * A.natDegree + 2 * C.natDegree > 2 * F.natDegree
        rcases lt_trichotomy (4 * C.natDegree) (A.natDegree + 2 * F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG23 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG24 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG20 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, astra4zExhaustTailBCFG20 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hEn (by omega)⟩)
    · -- 2 * G.natDegree > A.natDegree + 2 * F.natDegree
      rcases lt_trichotomy (2 * A.natDegree + C.natDegree) (G.natDegree) with ht2a | ht2b | ht2c
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG32 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, astra4zExhaustTailBCFG32 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hEn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG29 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
      · -- 2 * A.natDegree + C.natDegree > G.natDegree
        rcases lt_trichotomy (2 * C.natDegree) (G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG27 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG28 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, by omega⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBCFG20 ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, astra4zExhaustTailBCFG20 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hDn hEn (by omega)⟩)


end QuarticChamberExhaust810
end Max11DegreeRoutes
end
/-! Part 7 of 15 of `Grok810ScaleZeroQuarticChamberExhaust2Scratch`, split so that no single module elaborates them all
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
/-- Exhaust of the cost-argmin taxonomy on the live set `BDEF`. -/
theorem quarticChamberSupport810_of_live_BDEF
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCz : C = 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFne : F ≠ 0) (hGz : G = 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hGn : G.natDegree = 0 := by simp [hGz]
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · -- F.natDegree < A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF13 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF14 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF3 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF4 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF13 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF13 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
    · -- F.natDegree = A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF8 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF18 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
    · -- F.natDegree > A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF22 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF12 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF12 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF22 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF22 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
  · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (F.natDegree) (A.natDegree + D.natDegree) with ht1a | ht1b | ht1c
    · -- F.natDegree < A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · -- B.natDegree + F.natDegree < 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF16 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF17 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
        · -- B.natDegree + F.natDegree = 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF6 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF7 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF16 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF16 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
    · -- F.natDegree = A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (B.natDegree + F.natDegree) (2 * D.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- B.natDegree + F.natDegree > 2 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF5 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF15 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
    · -- F.natDegree > A.natDegree + D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF22 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF12 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF12 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF22 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF22 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
  · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * F.natDegree) (A.natDegree + 2 * E.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * F.natDegree < A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + B.natDegree + F.natDegree < 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF19 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF20 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
        · -- A.natDegree + B.natDegree + F.natDegree = 2 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF9 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF10 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF19 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF19 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
    · -- 2 * F.natDegree = A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + B.natDegree + F.natDegree) (2 * E.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- A.natDegree + B.natDegree + F.natDegree > 2 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF11 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF21 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, by omega⟩)
    · -- 2 * F.natDegree > A.natDegree + 2 * E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (2 * A.natDegree + B.natDegree) (F.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF22 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF12 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF12 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
        · -- 2 * A.natDegree + B.natDegree > F.natDegree
          rcases lt_trichotomy (A.natDegree + 4 * B.natDegree) (2 * F.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF1 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF2 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF0 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF22 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEF22 ⟨hA, hBne, hCz, hDne, hEne, hFne, hGz, astra4zExhaustTailBDEF22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hGn (by omega)⟩)
end QuarticChamberExhaust810
end Max11DegreeRoutes
end
/-! Part 8 of 15 of `Grok810ScaleZeroQuarticChamberExhaust2Scratch`, split so that no single module elaborates them all
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
/-- Exhaust of the cost-argmin taxonomy on the live set `BDEG`. -/
theorem quarticChamberSupport810_of_live_BDEG
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hBne : B ≠ 0) (hCz : C = 0) (hDne : D ≠ 0) (hEne : E ≠ 0) (hFz : F = 0) (hGne : G ≠ 0) :
    QuarticChamberSupport810 A B C D E F G := by
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hCn : C.natDegree = 0 := by simp [hCz]
  have hFn : F.natDegree = 0 := by simp [hFz]
  rcases lt_trichotomy (2 * E.natDegree) (A.natDegree + 2 * D.natDegree) with ht0a | ht0b | ht0c
  · -- 2 * E.natDegree < A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG13 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG14 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG3 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG4 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG2 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG13 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG13 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG13 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
    · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG2 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG8 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG18 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
    · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG22 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG12 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG12 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG2 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG22 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG22 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
  · -- 2 * E.natDegree = A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (2 * G.natDegree) (3 * A.natDegree + 2 * D.natDegree) with ht1a | ht1b | ht1c
    · -- 2 * G.natDegree < 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · -- 2 * B.natDegree + 2 * G.natDegree < A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG16 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG17 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree = A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 6 * B.natDegree) (4 * D.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG6 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG7 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG2 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG16 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG16 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG16 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
    · -- 2 * G.natDegree = 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (2 * B.natDegree + 2 * G.natDegree) (A.natDegree + 4 * D.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- 2 * B.natDegree + 2 * G.natDegree > A.natDegree + 4 * D.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG2 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG5 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG15 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
    · -- 2 * G.natDegree > 3 * A.natDegree + 2 * D.natDegree
      rcases lt_trichotomy (D.natDegree) (A.natDegree + B.natDegree) with ht2a | ht2b | ht2c
      · -- D.natDegree < A.natDegree + B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG22 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG12 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG12 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG2 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG22 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG22 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
  · -- 2 * E.natDegree > A.natDegree + 2 * D.natDegree
    rcases lt_trichotomy (G.natDegree) (A.natDegree + E.natDegree) with ht1a | ht1b | ht1c
    · -- G.natDegree < A.natDegree + E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree < 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG19 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG20 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree = 4 * E.natDegree
          rcases lt_trichotomy (3 * A.natDegree + 6 * B.natDegree) (4 * E.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG9 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG10 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG2 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG19 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG19 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG19 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
    · -- G.natDegree = A.natDegree + E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (A.natDegree + 2 * B.natDegree + 2 * G.natDegree) (4 * E.natDegree) with ht3a | ht3b | ht3c
        · exact (by omega : False).elim
        · exact (by omega : False).elim
        · -- A.natDegree + 2 * B.natDegree + 2 * G.natDegree > 4 * E.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG2 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG11 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG21 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, by omega⟩)
    · -- G.natDegree > A.natDegree + E.natDegree
      rcases lt_trichotomy (2 * E.natDegree) (3 * A.natDegree + 2 * B.natDegree) with ht2a | ht2b | ht2c
      · -- 2 * E.natDegree < 3 * A.natDegree + 2 * B.natDegree
        rcases lt_trichotomy (5 * A.natDegree + 2 * B.natDegree) (2 * G.natDegree) with ht3a | ht3b | ht3c
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG22 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
        · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG12 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG12 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
        · -- 5 * A.natDegree + 2 * B.natDegree > 2 * G.natDegree
          rcases lt_trichotomy (A.natDegree + 2 * B.natDegree) (G.natDegree) with ht4a | ht4b | ht4c
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG1 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG1 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG2 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG2 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
          · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG0 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG0 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG22 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
      · exact QuarticChamberSupport810.size4 (QuarticChamberSupportSize4810.cBDEG22 ⟨hA, hBne, hCz, hDne, hEne, hFz, hGne, astra4zExhaustTailBDEG22 A.natDegree B.natDegree C.natDegree D.natDegree E.natDegree F.natDegree G.natDegree hApos hAB hAC hAD hAE hAF hAG hCn hFn (by omega)⟩)
end QuarticChamberExhaust810
end Max11DegreeRoutes
end
