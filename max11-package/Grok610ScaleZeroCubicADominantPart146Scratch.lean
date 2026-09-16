import Max11SpeedReflectDegLibScratch
import Grok610ScaleZeroCubicADominantPart16Scratch
import Grok610ScaleZeroCubicADominantPart22Scratch

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

section CubicLoadB0_610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- Reflect the unchanged polynomial literal into coefficient/exponent data. -/
private theorem round4_astra4f_part146_polyOf
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X]) :
    degreeZeroN1CubicNoL610 l alpha beta delta epsilon zeta eta theta A B C D E =
      Max11ReflectDeg.polyOf [A, B, C, D, E]
      [
      (5 / 81 : k), (20 / 243 : k), (-(10 / 27 : k)),
      (-(5 / 27 : k)), (-(5 / 27 : k)), (35 / 6912 * l : k),
      (-(1 / 1152 * l : k)), (5 / 288 * l : k), (-(1 / 96 * l : k)),
      (1 / 64 * l : k), (1 / 32 * l : k), (3 / 128 * l : k),
      (1 / 8 * l : k), (-(1 / 16 * l : k)), (-(3 / 16 * l : k)),
      (-(3 / 8 * l : k)), (-(1 / 16 * l : k)), (3 / 8 * l : k),
      (4 / 243 * alpha : k), (-(4 / 27 * alpha : k)), (-(4 / 27 * alpha : k)),
      (4 / 9 * alpha : k), (7 / 6912 * beta : k), (35 / 2592 * beta : k),
      (-(7 / 5184 * beta : k)), (7 / 144 * beta : k), (-(7 / 216 * beta : k)),
      (7 / 432 * beta : k), (-(35 / 432 * beta : k)), (7 / 36 * beta : k),
      (7 / 72 * beta : k), (35 / 10368 * delta : k), (5 / 144 * delta : k),
      (5 / 432 * delta : k), (5 / 36 * delta : k), (-(5 / 36 * delta : k)),
      (-(5 / 72 * delta : k)), (-(2 / 9 * epsilon : k)), (5 / 432 * zeta : k),
      (1 / 12 * zeta : k), (-(1 / 8 * zeta : k)), (1 / 2 * zeta : k),
      (1 / 3 * eta : k), (1 / 24 * theta : k), (1 / 6 * theta : k)]
      [
      [1, 2, 0, 1, 0], [0, 3, 1, 0, 0], [0, 1, 1, 0, 1], [0, 1, 0, 2, 0],
      [0, 0, 2, 1, 0], [4, 0, 1, 0, 0], [3, 2, 0, 0, 0], [3, 0, 0, 0, 1],
      [2, 1, 0, 1, 0], [2, 0, 2, 0, 0], [1, 2, 1, 0, 0], [0, 4, 0, 0, 0],
      [1, 0, 1, 0, 1], [1, 0, 0, 2, 0], [0, 2, 0, 0, 1], [0, 1, 1, 1, 0],
      [0, 0, 3, 0, 0], [0, 0, 0, 0, 2], [1, 3, 0, 0, 0], [0, 2, 0, 1, 0],
      [0, 1, 2, 0, 0], [0, 0, 0, 1, 1], [5, 0, 0, 0, 0], [3, 0, 1, 0, 0],
      [2, 2, 0, 0, 0], [2, 0, 0, 0, 1], [1, 1, 0, 1, 0], [1, 0, 2, 0, 0],
      [0, 2, 1, 0, 0], [0, 0, 1, 0, 1], [0, 0, 0, 2, 0], [4, 0, 0, 0, 0],
      [2, 0, 1, 0, 0], [1, 2, 0, 0, 0], [1, 0, 0, 0, 1], [0, 1, 0, 1, 0],
      [0, 0, 2, 0, 0], [0, 1, 1, 0, 0], [3, 0, 0, 0, 0], [1, 0, 1, 0, 0],
      [0, 2, 0, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 0], [2, 0, 0, 0, 0],
      [0, 0, 1, 0, 0]] := by
  unfold degreeZeroN1CubicNoL610
  simp only [Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc,
    sub_eq_add_neg, neg_smul, add_assoc]

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicNoL610_natDegree_lt_of_loadCompete
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicLoadCompetes610 A B C D E) :
    (degreeZeroN1CubicNoL610 l alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  rw [round4_astra4f_part146_polyOf]
  apply Max11ReflectDeg.natDegree_lt_of_bnd_lt
  simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
    Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
    Max11ReflectDeg.mdeg_nil_right, List.map_cons, List.map_nil,
    Nat.zero_mul, Nat.one_mul, Nat.add_zero, Nat.zero_add,
    max_lt_iff]
  repeat' apply And.intro
  all_goals omega

end CubicLoadB0_610

end Max11DegreeRoutes
