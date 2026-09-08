import Grok610ScaleZeroConeCascadePart01Scratch
import Grok610ScaleZeroConeCascadePart07Scratch
import Grok610ScaleZeroConeCascadePart09Scratch
import Grok610ScaleZeroConeCascadePart28Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section SourcePrimitiveDegree610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 32000000 in
/-- A constant free core makes the polynomial primitive constant, hence
cannot support derivative `C (j / t) ≠ 0`. -/
theorem degreeZeroPrimitivePolynomial610_false_of_constant_core
    (l alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hA : A.natDegree = 0) (hB : B.natDegree = 0)
    (hC : C0.natDegree = 0) (hD : D0.natDegree = 0)
    (hE : E0.natDegree = 0)
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
  have hle :
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree ≤
        0 := by
    have hbase :
        (degreeZeroBaseGroupPolynomial610 l A B C0 D0 E0).natDegree ≤ 0 := by
      simp only [degreeZeroBaseGroupPolynomial610]
      compute_degree
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree ≤ 0 := by
      simp only [degreeZeroAlphaGroupPolynomial610]
      compute_degree
      omega
    have hbeta :
        (degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).natDegree ≤ 0 := by
      simp only [degreeZeroBetaGroupPolynomial610]
      compute_degree
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree ≤ 0 := by
      simp only [degreeZeroDeltaGroupPolynomial610]
      compute_degree
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree ≤ 0 := by
      simp only [degreeZeroEpsilonGroupPolynomial610]
      compute_degree
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree ≤ 0 := by
      simp only [degreeZeroZetaGroupPolynomial610]
      compute_degree
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree ≤ 0 := by
      simp only [degreeZeroEtaGroupPolynomial610]
      compute_degree
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree ≤ 0 := by
      simp only [degreeZeroThetaGroupPolynomial610]
      compute_degree
      omega
    simp only [degreeZeroPrimitivePolynomial610]
    exact natDegree_add8_le610 hbase (natDegree_smul_le_of_le610 alpha halpha)
      (natDegree_smul_le_of_le610 beta hbeta)
      (natDegree_smul_le_of_le610 delta hdelta)
      (natDegree_smul_le_of_le610 epsilon hepsilon)
      (natDegree_smul_le_of_le610 zeta hzeta)
      (natDegree_smul_le_of_le610 eta heta)
      (natDegree_smul_le_of_le610 theta htheta)
  omega

end SourcePrimitiveDegree610

end Max11DegreeRoutes
