import Max11SpeedReflectDegLibScratch
import Grok610ScaleZeroCubicADominantPart03Scratch
import Grok610ScaleZeroCubicADominantPart35Scratch

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
private theorem round4_astra4p_part37_polyOf
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroLambdaCubicNoSigmaD610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 81 : k), (5 / 243 : k), (-(5 / 27 : k)),
      (-(10 / 27 : k)), (-(5 / 81 : k)), (5 / 9 : k),
      (-(5 / 6912 * l : k)), (-(1 / 288 * l : k)), (-(1 / 96 * l : k)),
      (1 / 32 * l : k), (-(1 / 8 * l : k)), (-(1 / 8 * l : k)),
      (-(3 / 16 * l : k)), (-(3 / 16 * l : k)), (3 / 4 * l : k),
      (-(4 / 27 * alpha : k)), (-(4 / 27 * alpha : k)), (4 / 9 * alpha : k),
      (2 / 9 * alpha : k), (-(7 / 2592 * beta : k)), (-(7 / 432 * beta : k)),
      (-(7 / 216 * beta : k)), (-(35 / 1296 * beta : k)), (7 / 36 * beta : k),
      (7 / 36 * beta : k), (-(5 / 432 * delta : k)), (-(5 / 36 * delta : k)),
      (-(5 / 36 * delta : k)), (-(1 / 9 * epsilon : k)), (2 / 3 * epsilon : k),
      (-(1 / 12 * zeta : k)), (1 / 2 * zeta : k), (1 / 3 * eta : k),
      (1 / 6 * theta : k)]
      [
      [1, 2, 1, 0, 0], [0, 4, 0, 0, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
      [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [4, 1, 0, 0, 0], [3, 0, 0, 1, 0],
      [2, 1, 1, 0, 0], [1, 3, 0, 0, 0], [1, 1, 0, 0, 1], [1, 0, 1, 1, 0],
      [0, 2, 0, 1, 0], [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [1, 1, 0, 1, 0],
      [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [3, 1, 0, 0, 0],
      [2, 0, 0, 1, 0], [1, 1, 1, 0, 0], [0, 3, 0, 0, 0], [0, 1, 0, 0, 1],
      [0, 0, 1, 1, 0], [2, 1, 0, 0, 0], [1, 0, 0, 1, 0], [0, 1, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 0, 0, 0], [0, 0, 0, 1, 0],
      [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]] := by
  unfold degreeZeroLambdaCubicNoSigmaD610
  simp only [Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
theorem degreeZeroLambdaCubicNoSigmaD610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicSigmaConeD610 A B C D E) :
    (degreeZeroLambdaCubicNoSigmaD610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * D.natDegree := by
  rcases hcone with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have hs0 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt h0
  have hs1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h1
  have hs2 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt h2
  have hs3 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt h3
  have hs4 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt h4
  have hs5 : 0 + 1 ≤ D.natDegree := Nat.succ_le_of_lt h5
  have hs6 : A.natDegree + 6 * B.natDegree + 1 ≤ 4 * D.natDegree := Nat.succ_le_of_lt h6
  have hs7 : 3 * C.natDegree + 1 ≤ A.natDegree + 2 * D.natDegree := Nat.succ_le_of_lt h7
  have hs8 : 2 * E.natDegree + 1 ≤ A.natDegree + 2 * D.natDegree := Nat.succ_le_of_lt h8
  have hs9 : 9 * A.natDegree + 1 ≤ 4 * D.natDegree := Nat.succ_le_of_lt h9
  rw [round4_astra4p_part37_polyOf]
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
