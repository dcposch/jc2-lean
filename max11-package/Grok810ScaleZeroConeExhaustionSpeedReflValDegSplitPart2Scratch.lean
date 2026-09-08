import Grok810ScaleZeroConeExhaustionSpeedReflValDegSplitPart1Scratch

/-! # SPEED: theorems of `Grok810ScaleZeroConeExhaustionSpeedReflValDegScratch`, part 2 of 8, so that no single
module retains all the reflective bridge proof terms at once.
Statements unchanged. -/

noncomputable section

open scoped Polynomial.Bivariate
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
set_option maxRecDepth 8000000

section ExhaustRests810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoAC02_natDegree_lt_of_ABC0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : ABC0RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoAC02Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, htie, h4b, h5b, hD, hE, hF, hG⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, degreeZeroXiNoAC02Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0),
    zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0), zero_pow (by decide : (7 : ℕ) ≠ 0), hD, hE, hF, hG]
  compute_degree
  simp only [hD, hE, hF, hG, htie, h4b, h5b]
  have h4a2b : 4 * A.natDegree + 2 * B.natDegree + 1 ≤ 7 * A.natDegree := by
    omega
  have ha4b : A.natDegree + 4 * B.natDegree + 1 ≤ 7 * A.natDegree := by omega
  omega


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoAE06_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AE06RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoAE06Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hEpos, htie, hB, hC, hD, hF, hG⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, degreeZeroMuNoAE06Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0),
    zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0), zero_pow (by decide : (7 : ℕ) ≠ 0), hB, hC, hD, hF,
    hG]
  compute_degree
  simp only [hB, hC, hD, hF, hG, htie]
  omega


set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoAE06_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AE06RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoAE06Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hEpos, htie, hB, hC, hD, hF, hG⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, degreeZeroXiNoAE06Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0),
    zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0), zero_pow (by decide : (7 : ℕ) ≠ 0), hB, hC, hD, hF,
    hG]
  compute_degree
  simp only [hB, hC, hD, hF, hG, htie]
  omega


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoBE02_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BE02RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoBE02Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hEpos, htie, hA, hC, hD, hF, hG⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, degreeZeroMuNoBE02Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0),
    zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0), zero_pow (by decide : (7 : ℕ) ≠ 0), hA, hC, hD, hF,
    hG]
  compute_degree
  simp only [hA, hC, hD, hF, hG, htie]
  omega


set_option maxHeartbeats 64000000 in
theorem degreeZeroOmicronNoBE02_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BE02RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroOmicronNoBE02Polynomial810 l beta gamma delta epsilon zeta
        eta theta A B C0 D0 E0 F0 G0).natDegree <
      5 * B.natDegree := by
  rcases hcone with ⟨hBpos, hEpos, htie, hA, hC, hD, hF, hG⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, degreeZeroOmicronNoBE02Polynomial810, zero_mul, mul_zero,
    zero_smul, smul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0),
    zero_pow (by decide : (4 : ℕ) ≠ 0), zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0), zero_pow (by decide : (7 : ℕ) ≠ 0),
    hA, hC, hD, hF, hG]
  compute_degree
  simp only [hA, hC, hD, hF, hG, htie]
  omega


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoAD05_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AD05RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoAD05Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      6 * A.natDegree := by
  rcases hcone with ⟨hApos, hDpos, htie, hB, hC, hE, hF, hG⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, degreeZeroMuNoAD05Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0),
    zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0), zero_pow (by decide : (7 : ℕ) ≠ 0), hB, hC, hE, hF,
    hG]
  compute_degree
  simp only [hB, hC, hE, hF, hG, htie]
  omega


set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoAD05_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AD05RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoAD05Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hDpos, htie, hB, hC, hE, hF, hG⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, degreeZeroXiNoAD05Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0),
    zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0), zero_pow (by decide : (7 : ℕ) ≠ 0), hB, hC, hE, hF,
    hG]
  compute_degree
  simp only [hB, hC, hE, hF, hG, htie]
  omega


set_option maxHeartbeats 64000000 in
theorem degreeZeroXiNoC0E0_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0E0RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroXiNoC0E0Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      2 * C0.natDegree + E0.natDegree := by
  rcases hcone with ⟨hCpos, hEpos, htie, hA, hB, hD, hF, hG⟩
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, degreeZeroXiNoC0E0Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0),
    zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0), zero_pow (by decide : (7 : ℕ) ≠ 0), hA, hB, hD, hF,
    hG]
  compute_degree
  simp only [hA, hB, hD, hF, hG, htie]
  omega


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoC03_natDegree_lt_of_BC03
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BC03RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoC03Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      3 * C0.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, htie, hA, hD, hE, hF, hG⟩
  simp only [degreeZeroMuNoC03Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0),
    zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0), zero_pow (by decide : (7 : ℕ) ≠ 0), hA, hD, hE, hF,
    hG]
  compute_degree
  simp only [hA, hD, hE, hF, hG, htie]
  omega


set_option maxHeartbeats 64000000 in
theorem degreeZeroMuNoB4_natDegree_lt_of_BD03
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BD03RatioTieCone810 A B C0 D0 E0 F0 G0) :
    (degreeZeroMuNoB4Polynomial810 l beta gamma delta epsilon zeta eta
        theta A B C0 D0 E0 F0 G0).natDegree <
      4 * B.natDegree := by
  rcases hcone with ⟨hBpos, hDpos, htie, hA, hC, hE, hF, hG⟩
  simp only [degreeZeroMuNoB4Polynomial810, zero_mul, mul_zero, zero_smul,
    smul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0), zero_pow (by decide : (4 : ℕ) ≠ 0),
    zero_pow (by decide : (5 : ℕ) ≠ 0), zero_pow (by decide : (6 : ℕ) ≠ 0), zero_pow (by decide : (7 : ℕ) ≠ 0), hA, hC, hE, hF,
    hG]
  compute_degree
  simp only [hA, hC, hE, hF, hG, htie]
  omega


end ExhaustRests810

section ExhaustCombinedDeg810

variable {k : Type*} [Field k] [CharZero k]
set_option maxHeartbeats 64000000 in

theorem muA6Face810_natDegree
    {A : k[X]} (hA : A ≠ 0) :
    (muA6Face810 A).natDegree = 6 * A.natDegree := by
  have hc : (385 / 65536 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, muA6Face810]
  rw [natDegree_smul _ hc, natDegree_pow]
set_option maxHeartbeats 64000000 in


theorem muAC02Combined810_coeff (A C0 : k[X]) (n : ℕ) :
    (muAC02Combined810 A C0).coeff n =
      (385 / 65536 : k) * (A ^ 6).coeff n -
        (385 / 8192 : k) * (A ^ 4 * C0).coeff n +
          (105 / 1024 : k) * (A ^ 2 * C0 ^ 2).coeff n -
            (5 / 128 : k) * (C0 ^ 3).coeff n := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, muAC02Combined810, coeff_add, coeff_sub, coeff_smul, smul_eq_mul]
  ring


end ExhaustCombinedDeg810

end Max11DegreeRoutes

end
