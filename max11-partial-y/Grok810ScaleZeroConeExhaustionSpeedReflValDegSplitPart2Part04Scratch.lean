import Grok810ScaleZeroConeExhaustionSpeedReflValDegSplitPart2Part03Scratch

/-! # Part 4 of `Grok810ScaleZeroConeExhaustionSpeedReflValDegSplitPart2Scratch`.

One declaration split out of `Grok810ScaleZeroConeExhaustionSpeedReflValDegSplitPart2Scratch`; statements are byte-identical.
-/

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

end Max11DegreeRoutes
