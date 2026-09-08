import Grok610ScaleZeroCubicLoadMultiPart29Scratch

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
set_option maxRecDepth 100000000

section CubicLoadSigmaBCDERest610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroN1CubicNoSigmaBCDENoL610_natDegree_lt_of_loadCone
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : CubicLoadSigmaConeBCDE610 A B C D E)
    (hb : beta  = 0 ∨ 7 * (9 * A.natDegree) < 18 * A.natDegree + 42 * B.natDegree)
    (hd : delta = 0 ∨ 7 * (9 * A.natDegree) < 30 * A.natDegree + 42 * B.natDegree)
    (hz : zeta  = 0 ∨ 9 * A.natDegree < 6 * A.natDegree + 6 * B.natDegree)
    (ht : theta = 0 ∨ 7 * (9 * A.natDegree) < 54 * A.natDegree + 42 * B.natDegree) :
    (degreeZeroN1CubicNoSigmaBCDENoL610 0 alpha beta delta epsilon zeta eta theta
        A B C D E).natDegree <
      A.natDegree + 2 * B.natDegree + D.natDegree := by
  rcases hcone with ⟨⟨⟨hApos, hAB, hAC, hAD, hAE⟩, hBl, hCl, hDl, hEl⟩,
    hBne, hCne, hDne, hEne, heq1, heq2, heq3⟩
  have hsA : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  have hsAB : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAB
  have hsAC : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hAC
  have hsAD : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hAD
  have hsAE : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hAE
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  have htieBC : 4 * A.natDegree + 2 * B.natDegree =
      3 * A.natDegree + 2 * C.natDegree := heq1
  have htieBD : 10 * A.natDegree + 6 * B.natDegree =
      9 * A.natDegree + 4 * D.natDegree := heq2
  have htieBE : 12 * A.natDegree + 6 * B.natDegree =
      9 * A.natDegree + 4 * E.natDegree := heq3
  have eqC : 2 * C.natDegree = A.natDegree + 2 * B.natDegree := by omega
  have eqD : 4 * D.natDegree = A.natDegree + 6 * B.natDegree := by omega
  have eqE : 4 * E.natDegree = 3 * A.natDegree + 6 * B.natDegree := by omega

  rw [speedRefl_degreeZeroN1CubicNoSigmaBCDENoL610_eq_polyOf_dupfix]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  rcases hb with rfl | hb <;> rcases hd with rfl | hd <;>
    rcases hz with rfl | hz <;> rcases ht with rfl | ht <;>
      (simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
                  Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mdeg_cons,
                  Max11ReflectDeg.mdeg_nil_left, Max11ReflectDeg.mdeg_nil_right,
                  List.map_cons, List.map_nil, mul_zero, zero_mul, neg_zero,
                  Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
                  mul_one, one_mul, and_true, true_and, natDegree_zero];
       repeat' apply And.intro) <;>
        first
          | (right; right; omega)
          | (left; norm_num; done)
          | (right; left; simp; done)
          | trivial

end CubicLoadSigmaBCDERest610

end Max11DegreeRoutes
