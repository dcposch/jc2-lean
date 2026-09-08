import Grok610ScaleZeroConeCascadePart01Scratch
import Grok610ScaleZeroConeCascadePart06Scratch
import Grok610ScaleZeroConeCascadePart08Scratch
import Grok610ScaleZeroConeCascadePart39Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section HighBAndDCone610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
/-- If `E₀` is the only nonconstant free-core letter and `β ≠ 0`, the
face `β E₀²` has degree at least two. -/
theorem uniqueNonconstantE0_impossible_of_beta_ne
    (l alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0) (hbeta : beta ≠ 0)
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hEpos : 0 < E0.natDegree)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hEne : E0 ≠ 0 := by
    intro hE0
    simp [hE0] at hEpos
  have hc : (326592 / 559872 * beta : k) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hbeta
  have hlead :
      ((326592 / 559872 * beta : k) • E0 ^ 2).natDegree =
        2 * E0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :
      (degreeZeroPrimitiveHighERest610 l alpha beta delta epsilon zeta eta
          theta A B C0 D0 E0).natDegree <
        2 * E0.natDegree := by
    have hbase :
        (degreeZeroBaseGroupPolynomial610 l A B C0 D0 E0).natDegree <
          2 * E0.natDegree := by
      simp only [degreeZeroBaseGroupPolynomial610]
      compute_degree
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
          2 * E0.natDegree := by
      simp only [degreeZeroAlphaGroupPolynomial610]
      compute_degree
      omega
    have hbetaG :
        (degreeZeroBetaGroupNoE2Polynomial610 A B C0 D0 E0).natDegree <
          2 * E0.natDegree := by
      simp only [degreeZeroBetaGroupNoE2Polynomial610]
      compute_degree
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
          2 * E0.natDegree := by
      simp only [degreeZeroDeltaGroupPolynomial610]
      compute_degree
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
          2 * E0.natDegree := by
      simp only [degreeZeroEpsilonGroupPolynomial610]
      compute_degree
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
          2 * E0.natDegree := by
      simp only [degreeZeroZetaGroupPolynomial610]
      compute_degree
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
          2 * E0.natDegree := by
      simp only [degreeZeroEtaGroupPolynomial610]
      compute_degree
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
          2 * E0.natDegree := by
      simp only [degreeZeroThetaGroupPolynomial610]
      compute_degree
      omega
    simp only [degreeZeroPrimitiveHighERest610]
    exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
      (natDegree_smul_lt610 beta hbetaG) (natDegree_smul_lt610 delta hdelta)
      (natDegree_smul_lt610 epsilon hepsilon)
      (natDegree_smul_lt610 zeta hzeta) (natDegree_smul_lt610 eta heta)
      (natDegree_smul_lt610 theta htheta)
  rw [degreeZeroPrimitivePolynomial610_eq_betaE2_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega

end HighBAndDCone610

end Max11DegreeRoutes
