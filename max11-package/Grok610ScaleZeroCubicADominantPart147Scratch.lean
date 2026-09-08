import Grok610ScaleZeroCubicADominantPart19Scratch
import Grok610ScaleZeroCubicADominantPart23Scratch
import Grok610ScaleZeroCubicADominantPart146Scratch

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

theorem cubicADominant_l_eq_zero
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hcone : cubicLoadCompetes610 A B C D E)
    (hmu : (degreeZeroMuCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E).natDegree = 0)
    (hkap : (degreeZeroKappaCubic610 l alpha beta delta epsilon zeta
          eta theta A B C D E).natDegree = 0) :
    l = 0 := by
  by_contra hl
  have hApos : 0 < A.natDegree := hcone.1.1
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (77 / 248832 * l : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hl
  have hlead : (n1CubicLFace610 l A).natDegree = 6 * A.natDegree := by
    simp only [n1CubicLFace610]
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroN1CubicNoL610_natDegree_lt_of_loadCompete l alpha beta delta
      epsilon zeta eta theta A B C D E hcone
  have hN1le := degreeZeroN1Cubic610_natDegree_le l alpha beta delta epsilon
      zeta eta theta A B C D E hmu hkap
  have hN1deg :
      (degreeZeroN1Cubic610 l alpha beta delta epsilon zeta eta theta
          A B C D E).natDegree =
        6 * A.natDegree := by
    rw [degreeZeroN1Cubic610_eq_L_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
  omega

end CubicLoadB0_610

end Max11DegreeRoutes
