import Grok610ScaleZeroConeCascadePart06Scratch
import Grok610ScaleZeroConeCascadePart08Scratch
import Grok610ScaleZeroConeCascadePart10Scratch
import Grok610ScaleZeroConeCascadePart29Scratch

open scoped Polynomial.Bivariate
noncomputable section
open Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section HighACone610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitiveHighARest610_natDegree_lt
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : UniqueHighACone610 A B C0 D0 E0) :
    (degreeZeroPrimitiveHighARest610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE⟩
  have hbase :
      (degreeZeroBaseGroupHighARest610 l A B C0 D0 E0).natDegree <
        7 * A.natDegree := by
    simp only [degreeZeroBaseGroupHighARest610]
    compute_degree
    omega
  have halpha :
      (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
        7 * A.natDegree := by
    simp only [degreeZeroAlphaGroupPolynomial610]
    compute_degree
    omega
  have hbeta :
      (degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).natDegree <
        7 * A.natDegree := by
    simp only [degreeZeroBetaGroupPolynomial610]
    compute_degree
    omega
  have hdelta :
      (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
        7 * A.natDegree := by
    simp only [degreeZeroDeltaGroupPolynomial610]
    compute_degree
    omega
  have hepsilon :
      (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
        7 * A.natDegree := by
    simp only [degreeZeroEpsilonGroupPolynomial610]
    compute_degree
    omega
  have hzeta :
      (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
        7 * A.natDegree := by
    simp only [degreeZeroZetaGroupPolynomial610]
    compute_degree
    omega
  have heta :
      (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
        7 * A.natDegree := by
    simp only [degreeZeroEtaGroupPolynomial610]
    compute_degree
    omega
  have htheta :
      (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
        7 * A.natDegree := by
    simp only [degreeZeroThetaGroupPolynomial610]
    compute_degree
    omega
  simp only [degreeZeroPrimitiveHighARest610]
  exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
    (natDegree_smul_lt610 beta hbeta) (natDegree_smul_lt610 delta hdelta)
    (natDegree_smul_lt610 epsilon hepsilon) (natDegree_smul_lt610 zeta hzeta)
    (natDegree_smul_lt610 eta heta) (natDegree_smul_lt610 theta htheta)

end HighACone610

end Max11DegreeRoutes
