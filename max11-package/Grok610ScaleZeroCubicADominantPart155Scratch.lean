import Max11SpeedReflectDegLibScratch
import Grok610ScaleZeroCubicADominantPart153Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal into coefficient/exponent data. -/
private theorem round4_astra4f_part71_polyOf
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubicNoSigmaCE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 486 : k)), (5 / 81 : k), (10 / 81 : k),
      (25 / 486 : k), (5 / 54 : k), (-(5 / 27 : k)),
      (-(5 / 27 : k)), (-(5 / 6912 * l : k)), (1 / 864 * l : k),
      (-(1 / 288 * l : k)), (-(1 / 96 * l : k)), (7 / 96 * l : k),
      (1 / 24 * l : k), (1 / 16 * l : k), (-(1 / 8 * l : k)),
      (-(1 / 4 * l : k)), (-(1 / 8 * l : k)), (-(3 / 16 * l : k)),
      (4 / 81 * alpha : k), (1 / 81 * alpha : k), (-(2 / 27 * alpha : k)),
      (-(2 / 27 * alpha : k)), (-(2 / 9 * alpha : k)), (-(4 / 81 * alpha : k)),
      (2 / 9 * alpha : k), (-(7 / 2592 * beta : k)), (7 / 1296 * beta : k),
      (7 / 648 * beta : k), (-(7 / 216 * beta : k)), (-(7 / 144 * beta : k)),
      (-(7 / 108 * beta : k)), (7 / 36 * beta : k), (-(5 / 432 * delta : k)),
      (5 / 108 * delta : k), (5 / 324 * delta : k), (-(5 / 36 * delta : k)),
      (1 / 27 * epsilon : k), (-(1 / 9 * epsilon : k)), (-(1 / 9 * epsilon : k)),
      (-(1 / 12 * zeta : k)), (-(1 / 6 * zeta : k)), (-(1 / 18 * eta : k)),
      (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [1, 4, 0, 0, 0], [1, 2, 0, 0, 1], [1, 1, 1, 1, 0], [0, 3, 0, 1, 0],
      [0, 2, 2, 0, 0], [0, 1, 0, 1, 1], [0, 0, 1, 2, 0], [4, 0, 0, 1, 0],
      [3, 1, 1, 0, 0], [2, 3, 0, 0, 0], [2, 0, 1, 1, 0], [1, 2, 0, 1, 0],
      [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1],
      [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0],
      [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
      [0, 0, 0, 0, 2], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0], [1, 3, 0, 0, 0],
      [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1],
      [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 0, 1, 1, 0],
      [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0],
      [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0]] := by
  unfold degreeZeroOmicronCubicNoSigmaCE610
  simp only [Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronCubicNoSigmaCE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeCE610 A B C D E) :
    (degreeZeroOmicronCubicNoSigmaCE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      2 * C.natDegree + E.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt h6
  have hs8 : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree := Nat.succ_le_of_lt h8
  have hs9 : A.natDegree + 2 * D.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt h9
  have hs10 : 11 * A.natDegree + 1 ≤ 6 * C.natDegree := Nat.succ_le_of_lt h10
  rw [round4_astra4f_part71_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_sigmaDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicSigmaFaceDE610 A B C D E +
        degreeZeroKappaCubicNoSigmaDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicSigmaFaceDE610, degreeZeroKappaCubicNoSigmaDE610]
  all_goals module

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal into coefficient/exponent data. -/
private theorem round4_astra4p_part76_polyOf
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubicNoSigmaDE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 243 : k), (-(5 / 27 : k)), (-(5 / 27 : k)),
      (7 / 6912 * l : k), (5 / 288 * l : k), (-(1 / 192 * l : k)),
      (1 / 16 * l : k), (-(1 / 8 * l : k)), (1 / 16 * l : k),
      (-(3 / 16 * l : k)), (3 / 4 * l : k), (3 / 8 * l : k),
      (-(4 / 81 * alpha : k)), (4 / 9 * alpha : k), (4 / 9 * alpha : k),
      (35 / 10368 * beta : k), (7 / 144 * beta : k), (-(7 / 432 * beta : k)),
      (7 / 36 * beta : k), (7 / 36 * beta : k), (7 / 72 * beta : k),
      (5 / 432 * delta : k), (5 / 36 * delta : k), (-(5 / 72 * delta : k)),
      (5 / 6 * delta : k), (2 / 3 * epsilon : k), (1 / 24 * zeta : k),
      (1 / 2 * zeta : k), (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [1, 3, 0, 0, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [5, 0, 0, 0, 0],
      [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
      [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
      [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0],
      [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]] := by
  unfold degreeZeroKappaCubicNoSigmaDE610
  simp only [Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaCubicNoSigmaDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeDE610 A B C D E) :
    (degreeZeroKappaCubicNoSigmaDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt h6
  have hs8 : A.natDegree + 6 * B.natDegree + 1 ≤ 4 * D.natDegree := Nat.succ_le_of_lt h8
  have hs9 : 3 * C.natDegree + 1 ≤ A.natDegree + 2 * D.natDegree := Nat.succ_le_of_lt h9
  have hs10 : 9 * A.natDegree + 1 ≤ 4 * D.natDegree := Nat.succ_le_of_lt h10
  rw [round4_astra4p_part76_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubic610_eq_sigmaBCD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      omicronCubicSigmaFaceBCD610 A B C D E +
        degreeZeroOmicronCubicNoSigmaBCD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroOmicronCubic610, omicronCubicSigmaFaceBCD610, degreeZeroOmicronCubicNoSigmaBCD610]
  all_goals module

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal into coefficient/exponent data. -/
private theorem round4_astra4f_part81_polyOf
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubicNoSigmaBCD610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 486 : k)), (5 / 81 : k), (25 / 486 : k),
      (5 / 54 : k), (-(5 / 27 : k)), (-(5 / 27 : k)),
      (-(5 / 27 : k)), (-(5 / 6912 * l : k)), (1 / 864 * l : k),
      (-(1 / 288 * l : k)), (-(1 / 96 * l : k)), (7 / 96 * l : k),
      (1 / 24 * l : k), (1 / 16 * l : k), (-(1 / 8 * l : k)),
      (-(1 / 4 * l : k)), (-(1 / 8 * l : k)), (-(3 / 16 * l : k)),
      (4 / 81 * alpha : k), (1 / 81 * alpha : k), (-(2 / 27 * alpha : k)),
      (-(2 / 27 * alpha : k)), (-(2 / 9 * alpha : k)), (-(4 / 81 * alpha : k)),
      (2 / 9 * alpha : k), (-(7 / 2592 * beta : k)), (7 / 1296 * beta : k),
      (7 / 648 * beta : k), (-(7 / 216 * beta : k)), (-(7 / 144 * beta : k)),
      (-(7 / 108 * beta : k)), (7 / 36 * beta : k), (-(5 / 432 * delta : k)),
      (5 / 108 * delta : k), (5 / 324 * delta : k), (-(5 / 36 * delta : k)),
      (1 / 27 * epsilon : k), (-(1 / 9 * epsilon : k)), (-(1 / 9 * epsilon : k)),
      (-(1 / 12 * zeta : k)), (-(1 / 6 * zeta : k)), (-(1 / 18 * eta : k)),
      (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [1, 4, 0, 0, 0], [1, 2, 0, 0, 1], [0, 3, 0, 1, 0], [0, 2, 2, 0, 0],
      [0, 1, 0, 1, 1], [0, 0, 2, 0, 1], [0, 0, 1, 2, 0], [4, 0, 0, 1, 0],
      [3, 1, 1, 0, 0], [2, 3, 0, 0, 0], [2, 0, 1, 1, 0], [1, 2, 0, 1, 0],
      [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1],
      [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0],
      [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
      [0, 0, 0, 0, 2], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0], [1, 3, 0, 0, 0],
      [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1],
      [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 0, 1, 1, 0],
      [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0],
      [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0]] := by
  unfold degreeZeroOmicronCubicNoSigmaBCD610
  simp only [Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronCubicNoSigmaBCD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBCD610 A B C D E) :
    (degreeZeroOmicronCubicNoSigmaBCD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt h6
  have hs7 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt h7
  have hs10 : 4 * E.natDegree + 1 ≤ 3 * A.natDegree + 6 * B.natDegree := Nat.succ_le_of_lt h10
  have hs11 : 4 * A.natDegree + 1 ≤ 3 * B.natDegree := Nat.succ_le_of_lt h11
  rw [round4_astra4f_part81_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
theorem cubicSigmaInner_BCE_identity
    (a b c e : k) :
    ((-1 / 40 : k) * a * b * c ^ 3 + (-1 / 16 : k) * a * b * e ^ 2) * kappaCubicSigmaInnerBCE610 a b c e +
      ((1 / 40 : k) * a * b ^ 2 * c ^ 2 + (-1 / 5 : k) * c ^ 4) * lambdaCubicSigmaInnerBCE610 a b c e +
      ((1 / 16 : k) * a * b ^ 2 * e + (-3 / 5 : k) * c ^ 2 * e) * omicronCubicSigmaInnerBCE610 a b c e =
      c ^ 7 := by
  simp only [kappaCubicSigmaInnerBCE610, lambdaCubicSigmaInnerBCE610, omicronCubicSigmaInnerBCE610]
  ring

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_sigmaBCE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicSigmaFaceBCE610 A B C D E +
        degreeZeroKappaCubicNoSigmaBCE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicSigmaFaceBCE610, degreeZeroKappaCubicNoSigmaBCE610]
  all_goals module

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal into coefficient/exponent data. -/
private theorem round4_astra4p_part90_polyOf
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubicNoSigmaBCE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 27 : k)), (10 / 9 : k), (7 / 6912 * l : k),
      (5 / 288 * l : k), (-(1 / 192 * l : k)), (1 / 16 * l : k),
      (-(1 / 8 * l : k)), (1 / 16 * l : k), (-(3 / 16 * l : k)),
      (3 / 4 * l : k), (3 / 8 * l : k), (-(4 / 81 * alpha : k)),
      (4 / 9 * alpha : k), (4 / 9 * alpha : k), (35 / 10368 * beta : k),
      (7 / 144 * beta : k), (-(7 / 432 * beta : k)), (7 / 36 * beta : k),
      (7 / 36 * beta : k), (7 / 72 * beta : k), (5 / 432 * delta : k),
      (5 / 36 * delta : k), (-(5 / 72 * delta : k)), (5 / 6 * delta : k),
      (2 / 3 * epsilon : k), (1 / 24 * zeta : k), (1 / 2 * zeta : k),
      (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [0, 2, 0, 1, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0],
      [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [1, 0, 2, 0, 0],
      [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [0, 3, 0, 0, 0],
      [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0],
      [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0],
      [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
      [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0],
      [1, 0, 0, 0, 0]] := by
  unfold degreeZeroKappaCubicNoSigmaBCE610
  simp only [Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaCubicNoSigmaBCE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBCE610 A B C D E) :
    (degreeZeroKappaCubicNoSigmaBCE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt h6
  have hs7 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt h7
  have hs10 : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree := Nat.succ_le_of_lt h10
  have hs11 : 4 * A.natDegree + 1 ≤ 3 * B.natDegree := Nat.succ_le_of_lt h11
  rw [round4_astra4p_part90_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

theorem kappaCubicSigmaFaceBCE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicSigmaConeBCE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    : (kappaCubicSigmaFaceBCE610 A B C D E).coeff (A.natDegree + 3 * B.natDegree) =
      (1 / 243 : k) * kappaCubicSigmaInnerBCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  simp only [kappaCubicSigmaFaceBCE610, kappaCubicSigmaInnerBCE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB3 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
  have hcf_AB3 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hdeg_AB3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_AB3, hcf_BC2]
  ring

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_sigmaBCE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicSigmaFaceBCE610 A B C D E +
        degreeZeroLambdaCubicNoSigmaBCE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicSigmaFaceBCE610, degreeZeroLambdaCubicNoSigmaBCE610]
  all_goals module

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal into coefficient/exponent data. -/
private theorem round4_astra4p_part95_polyOf
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubicNoSigmaBCE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 243 : k), (-(5 / 27 : k)), (-(5 / 27 : k)),
      (-(10 / 27 : k)), (-(5 / 6912 * l : k)), (-(1 / 288 * l : k)),
      (-(1 / 96 * l : k)), (1 / 32 * l : k), (-(1 / 8 * l : k)),
      (-(1 / 8 * l : k)), (-(3 / 16 * l : k)), (-(3 / 16 * l : k)),
      (3 / 4 * l : k), (-(4 / 27 * alpha : k)), (-(4 / 27 * alpha : k)),
      (4 / 9 * alpha : k), (2 / 9 * alpha : k), (-(7 / 2592 * beta : k)),
      (-(7 / 432 * beta : k)), (-(7 / 216 * beta : k)), (-(35 / 1296 * beta : k)),
      (7 / 36 * beta : k), (7 / 36 * beta : k), (-(5 / 432 * delta : k)),
      (-(5 / 36 * delta : k)), (-(5 / 36 * delta : k)), (-(1 / 9 * epsilon : k)),
      (2 / 3 * epsilon : k), (-(1 / 12 * zeta : k)), (1 / 2 * zeta : k),
      (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [0, 4, 0, 0, 0], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
      [4, 1, 0, 0, 0], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0], [1, 3, 0, 0, 0],
      [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0],
      [0, 0, 0, 1, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1],
      [0, 0, 0, 2, 0], [3, 1, 0, 0, 0], [2, 0, 0, 1, 0], [1, 1, 1, 0, 0],
      [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [2, 1, 0, 0, 0],
      [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1],
      [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]] := by
  unfold degreeZeroLambdaCubicNoSigmaBCE610
  simp only [Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
theorem degreeZeroLambdaCubicNoSigmaBCE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBCE610 A B C D E) :
    (degreeZeroLambdaCubicNoSigmaBCE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt h6
  have hs7 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt h7
  have hs10 : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree := Nat.succ_le_of_lt h10
  have hs11 : 4 * A.natDegree + 1 ≤ 3 * B.natDegree := Nat.succ_le_of_lt h11
  rw [round4_astra4p_part95_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

theorem lambdaCubicSigmaFaceBCE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicSigmaConeBCE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    : (lambdaCubicSigmaFaceBCE610 A B C D E).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      (1 / 81 : k) * lambdaCubicSigmaInnerBCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  simp only [lambdaCubicSigmaFaceBCE610, lambdaCubicSigmaInnerBCE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB2C : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2C : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hdeg_AB2C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C3 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_C3 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 3 := by
    rw [← hdeg_C3, coeff_natDegree, leadingCoeff_pow]
  have hdeg_E2 : (E ^ 2).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_E2 : (E ^ 2).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) =
      E.leadingCoeff ^ 2 := by
    rw [← hdeg_E2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_AB2C, hcf_C3, hcf_E2]
  ring

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubic610_eq_sigmaBCE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      omicronCubicSigmaFaceBCE610 A B C D E +
        degreeZeroOmicronCubicNoSigmaBCE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroOmicronCubic610, omicronCubicSigmaFaceBCE610, degreeZeroOmicronCubicNoSigmaBCE610]
  all_goals module

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal into coefficient/exponent data. -/
private theorem round4_astra4f_part100_polyOf
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubicNoSigmaBCE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 486 : k)), (10 / 81 : k), (25 / 486 : k),
      (5 / 54 : k), (-(5 / 27 : k)), (-(5 / 27 : k)),
      (-(5 / 6912 * l : k)), (1 / 864 * l : k), (-(1 / 288 * l : k)),
      (-(1 / 96 * l : k)), (7 / 96 * l : k), (1 / 24 * l : k),
      (1 / 16 * l : k), (-(1 / 8 * l : k)), (-(1 / 4 * l : k)),
      (-(1 / 8 * l : k)), (-(3 / 16 * l : k)), (4 / 81 * alpha : k),
      (1 / 81 * alpha : k), (-(2 / 27 * alpha : k)), (-(2 / 27 * alpha : k)),
      (-(2 / 9 * alpha : k)), (-(4 / 81 * alpha : k)), (2 / 9 * alpha : k),
      (-(7 / 2592 * beta : k)), (7 / 1296 * beta : k), (7 / 648 * beta : k),
      (-(7 / 216 * beta : k)), (-(7 / 144 * beta : k)), (-(7 / 108 * beta : k)),
      (7 / 36 * beta : k), (-(5 / 432 * delta : k)), (5 / 108 * delta : k),
      (5 / 324 * delta : k), (-(5 / 36 * delta : k)), (1 / 27 * epsilon : k),
      (-(1 / 9 * epsilon : k)), (-(1 / 9 * epsilon : k)), (-(1 / 12 * zeta : k)),
      (-(1 / 6 * zeta : k)), (-(1 / 18 * eta : k)), (1 / 3 * eta : k),
      (1 / 6 * theta : k)]
      [
      [1, 4, 0, 0, 0], [1, 1, 1, 1, 0], [0, 3, 0, 1, 0], [0, 2, 2, 0, 0],
      [0, 1, 0, 1, 1], [0, 0, 1, 2, 0], [4, 0, 0, 1, 0], [3, 1, 1, 0, 0],
      [2, 3, 0, 0, 0], [2, 0, 1, 1, 0], [1, 2, 0, 1, 0], [1, 1, 2, 0, 0],
      [0, 3, 1, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0],
      [0, 0, 2, 1, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [1, 0, 0, 2, 0],
      [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0], [0, 0, 0, 0, 2],
      [3, 0, 0, 1, 0], [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 0, 1, 1, 0],
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [2, 0, 0, 1, 0],
      [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 0, 1, 1, 0], [1, 2, 0, 0, 0],
      [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0]] := by
  unfold degreeZeroOmicronCubicNoSigmaBCE610
  simp only [Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronCubicNoSigmaBCE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBCE610 A B C D E) :
    (degreeZeroOmicronCubicNoSigmaBCE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + E.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt h6
  have hs7 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt h7
  have hs10 : 4 * D.natDegree + 1 ≤ A.natDegree + 6 * B.natDegree := Nat.succ_le_of_lt h10
  have hs11 : 4 * A.natDegree + 1 ≤ 3 * B.natDegree := Nat.succ_le_of_lt h11
  rw [round4_astra4f_part100_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

theorem omicronCubicSigmaFaceBCE610_coeff_top
    {A B C D E : k[X]}
    (hcone : CubicSigmaConeBCE610 A B C D E)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    : (omicronCubicSigmaFaceBCE610 A B C D E).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) =
      (1 / 81 : k) * omicronCubicSigmaInnerBCE610 A.leadingCoeff B.leadingCoeff C.leadingCoeff E.leadingCoeff := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  simp only [omicronCubicSigmaFaceBCE610, omicronCubicSigmaInnerBCE610, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_AB2E : ((A * B ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
  have hcf_AB2E : ((A * B ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_AB2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C2E : ((C ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne, natDegree_pow]
    omega
  have hcf_C2E : ((C ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) =
      C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_C2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_AB2E, hcf_C2E]
  ring

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
theorem degreeZeroOmicronCubic610_eq_sigmaBDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      omicronCubicSigmaFaceBDE610 A B C D E +
        degreeZeroOmicronCubicNoSigmaBDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroOmicronCubic610, omicronCubicSigmaFaceBDE610, degreeZeroOmicronCubicNoSigmaBDE610]
  all_goals module

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal into coefficient/exponent data. -/
private theorem round4_astra4f_part106_polyOf
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroOmicronCubicNoSigmaBDE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 486 : k)), (10 / 81 : k), (25 / 486 : k),
      (5 / 54 : k), (-(5 / 27 : k)), (-(5 / 27 : k)),
      (-(5 / 27 : k)), (-(5 / 6912 * l : k)), (1 / 864 * l : k),
      (-(1 / 288 * l : k)), (-(1 / 96 * l : k)), (7 / 96 * l : k),
      (1 / 24 * l : k), (1 / 16 * l : k), (-(1 / 8 * l : k)),
      (-(1 / 4 * l : k)), (-(1 / 8 * l : k)), (-(3 / 16 * l : k)),
      (4 / 81 * alpha : k), (1 / 81 * alpha : k), (-(2 / 27 * alpha : k)),
      (-(2 / 27 * alpha : k)), (-(2 / 9 * alpha : k)), (-(4 / 81 * alpha : k)),
      (2 / 9 * alpha : k), (-(7 / 2592 * beta : k)), (7 / 1296 * beta : k),
      (7 / 648 * beta : k), (-(7 / 216 * beta : k)), (-(7 / 144 * beta : k)),
      (-(7 / 108 * beta : k)), (7 / 36 * beta : k), (-(5 / 432 * delta : k)),
      (5 / 108 * delta : k), (5 / 324 * delta : k), (-(5 / 36 * delta : k)),
      (1 / 27 * epsilon : k), (-(1 / 9 * epsilon : k)), (-(1 / 9 * epsilon : k)),
      (-(1 / 12 * zeta : k)), (-(1 / 6 * zeta : k)), (-(1 / 18 * eta : k)),
      (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [1, 4, 0, 0, 0], [1, 1, 1, 1, 0], [0, 3, 0, 1, 0], [0, 2, 2, 0, 0],
      [0, 1, 0, 1, 1], [0, 0, 2, 0, 1], [0, 0, 1, 2, 0], [4, 0, 0, 1, 0],
      [3, 1, 1, 0, 0], [2, 3, 0, 0, 0], [2, 0, 1, 1, 0], [1, 2, 0, 1, 0],
      [1, 1, 2, 0, 0], [0, 3, 1, 0, 0], [1, 0, 0, 1, 1], [0, 1, 1, 0, 1],
      [0, 1, 0, 2, 0], [0, 0, 2, 1, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0],
      [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 3, 0, 0],
      [0, 0, 0, 0, 2], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0], [1, 3, 0, 0, 0],
      [1, 0, 1, 1, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1],
      [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 0, 1, 1, 0],
      [1, 2, 0, 0, 0], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [1, 0, 0, 1, 0],
      [0, 1, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0]] := by
  unfold degreeZeroOmicronCubicNoSigmaBDE610
  simp only [Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronCubicNoSigmaBDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBDE610 A B C D E) :
    (degreeZeroOmicronCubicNoSigmaBDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + E.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt h6
  have hs7 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt h7
  have hs10 : 2 * C.natDegree + 1 ≤ A.natDegree + 2 * B.natDegree := Nat.succ_le_of_lt h10
  have hs11 : 4 * A.natDegree + 1 ≤ 3 * B.natDegree := Nat.succ_le_of_lt h11
  rw [round4_astra4f_part106_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_sigmaCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicSigmaFaceCDE610 A B C D E +
        degreeZeroKappaCubicNoSigmaCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicSigmaFaceCDE610, degreeZeroKappaCubicNoSigmaCDE610]
  all_goals module

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaKills610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal into coefficient/exponent data. -/
private theorem round4_astra4p_part111_polyOf
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubicNoSigmaCDE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 243 : k), (-(5 / 27 : k)), (-(5 / 27 : k)),
      (7 / 6912 * l : k), (5 / 288 * l : k), (-(1 / 192 * l : k)),
      (1 / 16 * l : k), (-(1 / 8 * l : k)), (1 / 16 * l : k),
      (-(3 / 16 * l : k)), (3 / 4 * l : k), (3 / 8 * l : k),
      (-(4 / 81 * alpha : k)), (4 / 9 * alpha : k), (4 / 9 * alpha : k),
      (35 / 10368 * beta : k), (7 / 144 * beta : k), (-(7 / 432 * beta : k)),
      (7 / 36 * beta : k), (7 / 36 * beta : k), (7 / 72 * beta : k),
      (5 / 432 * delta : k), (5 / 36 * delta : k), (-(5 / 72 * delta : k)),
      (5 / 6 * delta : k), (2 / 3 * epsilon : k), (1 / 24 * zeta : k),
      (1 / 2 * zeta : k), (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [1, 3, 0, 0, 0], [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [5, 0, 0, 0, 0],
      [3, 0, 1, 0, 0], [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0],
      [1, 0, 2, 0, 0], [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0],
      [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0], [0, 0, 1, 0, 0],
      [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]] := by
  unfold degreeZeroKappaCubicNoSigmaCDE610
  simp only [Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaCubicNoSigmaCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeCDE610 A B C D E) :
    (degreeZeroKappaCubicNoSigmaCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      D.natDegree + E.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt h6
  have hs7 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt h7
  have hs10 : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree := Nat.succ_le_of_lt h10
  have hs11 : 11 * A.natDegree + 1 ≤ 6 * C.natDegree := Nat.succ_le_of_lt h11
  rw [round4_astra4p_part111_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

end CubicSigmaKills610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaCD610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_sigmaCD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicSigmaFaceCD610 A B C D E +
        degreeZeroLambdaCubicNoSigmaCD610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicSigmaFaceCD610, degreeZeroLambdaCubicNoSigmaCD610]
  all_goals module

end CubicSigmaCD610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaCD610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal into coefficient/exponent data. -/
private theorem round4_astra4p_part116_polyOf
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubicNoSigmaCD610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 81 : k), (5 / 243 : k), (-(5 / 27 : k)),
      (-(10 / 27 : k)), (5 / 9 : k), (-(5 / 6912 * l : k)),
      (-(1 / 288 * l : k)), (-(1 / 96 * l : k)), (1 / 32 * l : k),
      (-(1 / 8 * l : k)), (-(1 / 8 * l : k)), (-(3 / 16 * l : k)),
      (-(3 / 16 * l : k)), (3 / 4 * l : k), (-(4 / 27 * alpha : k)),
      (-(4 / 27 * alpha : k)), (4 / 9 * alpha : k), (2 / 9 * alpha : k),
      (-(7 / 2592 * beta : k)), (-(7 / 432 * beta : k)), (-(7 / 216 * beta : k)),
      (-(35 / 1296 * beta : k)), (7 / 36 * beta : k), (7 / 36 * beta : k),
      (-(5 / 432 * delta : k)), (-(5 / 36 * delta : k)), (-(5 / 36 * delta : k)),
      (-(1 / 9 * epsilon : k)), (2 / 3 * epsilon : k), (-(1 / 12 * zeta : k)),
      (1 / 2 * zeta : k), (1 / 3 * eta : k), (1 / 6 * theta : k)]
      [
      [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
      [0, 0, 0, 0, 2], [4, 1, 0, 0, 0], [3, 0, 0, 1, 0], [2, 1, 1, 0, 0],
      [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0], [0, 2, 0, 1, 0],
      [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 0], [0, 2, 1, 0, 0],
      [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [3, 1, 0, 0, 0], [2, 0, 0, 1, 0],
      [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1], [0, 0, 1, 1, 0],
      [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0], [0, 2, 0, 0, 0],
      [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0],
      [0, 1, 0, 0, 0]] := by
  unfold degreeZeroLambdaCubicNoSigmaCD610
  simp only [Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
theorem degreeZeroLambdaCubicNoSigmaCD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeCD610 A B C D E) :
    (degreeZeroLambdaCubicNoSigmaCD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * D.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt h6
  have hs8 : A.natDegree + 2 * B.natDegree + 1 ≤ 2 * C.natDegree := Nat.succ_le_of_lt h8
  have hs9 : 2 * E.natDegree + 1 ≤ 3 * C.natDegree := Nat.succ_le_of_lt h9
  have hs10 : 11 * A.natDegree + 1 ≤ 6 * C.natDegree := Nat.succ_le_of_lt h10
  rw [round4_astra4p_part116_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

end CubicSigmaCD610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicSigmaCD610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
theorem degreeZeroN1Cubic610_eq_sigmaCD_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroN1Cubic610 l alpha beta delta epsilon zeta eta theta
        A B C D E =
      n1CubicSigmaFaceCD610 A B C D E +
        degreeZeroN1CubicNoSigmaCD610 l alpha beta delta epsilon zeta
          eta theta A B C D E := by
  simp only [degreeZeroN1Cubic610, n1CubicSigmaFaceCD610,
    degreeZeroN1CubicNoSigmaCD610]
  all_goals module

end CubicSigmaCD610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicBalanced610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaCubic610_eq_sigmaBCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      kappaCubicSigmaFaceBCDE610 A B C D E +
        degreeZeroKappaCubicNoSigmaBCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroKappaCubic610, kappaCubicSigmaFaceBCDE610, degreeZeroKappaCubicNoSigmaBCDE610]
  all_goals module

end CubicBalanced610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicBalanced610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal into coefficient/exponent data. -/
private theorem round4_astra4p_part123_polyOf
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroKappaCubicNoSigmaBCDE610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (-(5 / 27 : k)), (7 / 6912 * l : k), (5 / 288 * l : k),
      (-(1 / 192 * l : k)), (1 / 16 * l : k), (-(1 / 8 * l : k)),
      (1 / 16 * l : k), (-(3 / 16 * l : k)), (3 / 4 * l : k),
      (3 / 8 * l : k), (-(4 / 81 * alpha : k)), (4 / 9 * alpha : k),
      (4 / 9 * alpha : k), (35 / 10368 * beta : k), (7 / 144 * beta : k),
      (-(7 / 432 * beta : k)), (7 / 36 * beta : k), (7 / 36 * beta : k),
      (7 / 72 * beta : k), (5 / 432 * delta : k), (5 / 36 * delta : k),
      (-(5 / 72 * delta : k)), (5 / 6 * delta : k), (2 / 3 * epsilon : k),
      (1 / 24 * zeta : k), (1 / 2 * zeta : k), (1 / 3 * eta : k),
      (1 / 6 * theta : k)]
      [
      [0, 2, 0, 1, 0], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0], [2, 2, 0, 0, 0],
      [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [1, 0, 2, 0, 0], [0, 2, 1, 0, 0],
      [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
      [0, 0, 1, 1, 0], [4, 0, 0, 0, 0], [2, 0, 1, 0, 0], [1, 2, 0, 0, 0],
      [1, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 0, 2, 0, 0], [3, 0, 0, 0, 0],
      [1, 0, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0],
      [2, 0, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [1, 0, 0, 0, 0]] := by
  unfold degreeZeroKappaCubicNoSigmaBCDE610
  simp only [Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
theorem degreeZeroKappaCubicNoSigmaBCDE610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeBCDE610 A B C D E) :
    (degreeZeroKappaCubicNoSigmaBCDE610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ B.natDegree := Nat.succ_le_of_lt h5
  have hs6 : 0 + 1 ≤ C.natDegree := Nat.succ_le_of_lt h6
  have hs7 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt h7
  have hs8 : 0 + 1 ≤ E.natDegree := Nat.succ_le_of_lt h8
  have hs12 : 4 * A.natDegree + 1 ≤ 3 * B.natDegree := Nat.succ_le_of_lt h12
  rw [round4_astra4p_part123_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

end CubicBalanced610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section CubicBalanced610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem degreeZeroLambdaCubic610_eq_sigmaBCDE_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E =
      lambdaCubicSigmaFaceBCDE610 A B C D E +
        degreeZeroLambdaCubicNoSigmaBCDE610 l alpha beta delta epsilon zeta eta theta
          A B C D E := by
  simp only [degreeZeroLambdaCubic610, lambdaCubicSigmaFaceBCDE610, degreeZeroLambdaCubicNoSigmaBCDE610]
  all_goals module

end CubicBalanced610

end Max11DegreeRoutes
