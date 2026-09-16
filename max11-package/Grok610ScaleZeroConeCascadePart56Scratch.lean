import Grok610ScaleZeroConeCascadePart01Scratch
import Grok610ScaleZeroConeCascadePart06Scratch
import Grok610ScaleZeroConeCascadePart08Scratch
import Grok610ScaleZeroConeCascadePart10Scratch
import Grok610ScaleZeroConeCascadePart38Scratch
import Grok610ScaleZeroConeCascadeSpeedTPart00Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section HighACone610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem uniqueHighA_impossible_of_l_zero_B_zero_beta_ne
    (alpha beta delta epsilon zeta eta theta j : k)
    (A C0 D0 E0 : k[X]) (hj : j ≠ 0) (hbeta : beta ≠ 0)
    (hcone : UniqueHighACone610 A 0 C0 D0 E0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 0 alpha beta delta epsilon
            zeta eta theta A 0 C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 0 alpha beta delta epsilon zeta
          eta theta A 0 C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hc : (2695 / 559872 * beta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hbeta
  have hlead :
      ((2695 / 559872 * beta : k) • A ^ 6).natDegree =
        6 * A.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :
      (degreeZeroPrimitiveHighA_B0_noA6_Rest610 0 alpha beta delta epsilon
          zeta eta theta A C0 D0 E0).natDegree <
        6 * A.natDegree := by
    rcases hcone with ⟨hApos, _, hC, hD, hE⟩
    have hbase :
        (degreeZeroBaseGroupHighA_noA6B_Rest610 0 A 0 C0 D0 E0).natDegree <
          6 * A.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroBaseGroupHighA_noA6B_Rest610 0 A 0 C0 D0 E0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A 0 C0 D0 E0).natDegree <
          6 * A.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroAlphaGroupPolynomial610 A 0 C0 D0 E0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have hbetaG :
        (degreeZeroBetaGroupNoA6Polynomial610 A 0 C0 D0 E0).natDegree <
          6 * A.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroBetaGroupNoA6Polynomial610 A 0 C0 D0 E0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A 0 C0 D0).natDegree <
          6 * A.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroDeltaGroupPolynomial610 A 0 C0 D0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A 0 C0 D0).natDegree <
          6 * A.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroEpsilonGroupPolynomial610 A 0 C0 D0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A 0 C0 D0).natDegree <
          6 * A.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroZetaGroupPolynomial610 A 0 C0 D0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A 0 C0 D0).natDegree <
          6 * A.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroEtaGroupPolynomial610 A 0 C0 D0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A 0 C0 E0).natDegree <
          6 * A.natDegree := by
      refine (coneCascade610SpeedTBound_degreeZeroThetaGroupPolynomial610 A 0 C0 E0).trans_lt ?_
      simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
        Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
        Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
        Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
      omega
    simp only [degreeZeroPrimitiveHighA_B0_noA6_Rest610]
    exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
      (natDegree_smul_lt610 beta hbetaG) (natDegree_smul_lt610 delta hdelta)
      (natDegree_smul_lt610 epsilon hepsilon)
      (natDegree_smul_lt610 zeta hzeta) (natDegree_smul_lt610 eta heta)
      (natDegree_smul_lt610 theta htheta)
  rw [degreeZeroPrimitivePolynomial610_eq_betaA6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

end HighACone610

end Max11DegreeRoutes
