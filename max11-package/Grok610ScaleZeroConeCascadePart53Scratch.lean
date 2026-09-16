import Grok610ScaleZeroConeCascadePart06Scratch
import Grok610ScaleZeroConeCascadePart08Scratch
import Grok610ScaleZeroConeCascadePart10Scratch
import Grok610ScaleZeroConeCascadePart29Scratch
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
    refine (coneCascade610SpeedTBound_degreeZeroBaseGroupHighARest610 l A B C0 D0 E0).trans_lt ?_
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
      Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
    omega
  have halpha :
      (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
        7 * A.natDegree := by
    refine (coneCascade610SpeedTBound_degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).trans_lt ?_
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
      Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
    omega
  have hbeta :
      (degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).natDegree <
        7 * A.natDegree := by
    refine (coneCascade610SpeedTBound_degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).trans_lt ?_
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
      Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
    omega
  have hdelta :
      (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
        7 * A.natDegree := by
    refine (coneCascade610SpeedTBound_degreeZeroDeltaGroupPolynomial610 A B C0 D0).trans_lt ?_
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
      Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
    omega
  have hepsilon :
      (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
        7 * A.natDegree := by
    refine (coneCascade610SpeedTBound_degreeZeroEpsilonGroupPolynomial610 A B C0 D0).trans_lt ?_
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
      Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
    omega
  have hzeta :
      (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
        7 * A.natDegree := by
    refine (coneCascade610SpeedTBound_degreeZeroZetaGroupPolynomial610 A B C0 D0).trans_lt ?_
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
      Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
    omega
  have heta :
      (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
        7 * A.natDegree := by
    refine (coneCascade610SpeedTBound_degreeZeroEtaGroupPolynomial610 A B C0 D0).trans_lt ?_
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
      Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
    omega
  have htheta :
      (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
        7 * A.natDegree := by
    refine (coneCascade610SpeedTBound_degreeZeroThetaGroupPolynomial610 A B C0 E0).trans_lt ?_
    simp only [Max11ReflectDeg.bnd_cons, Max11ReflectDeg.bnd_nil,
      Max11ReflectDeg.mdeg_cons, Max11ReflectDeg.mdeg_nil_left,
      Max11ReflectDeg.mdeg_nil_right, Nat.zero_mul, Nat.mul_zero,
      Nat.add_zero, Nat.zero_add, Nat.one_mul, natDegree_zero]
    omega
  simp only [degreeZeroPrimitiveHighARest610]
  exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
    (natDegree_smul_lt610 beta hbeta) (natDegree_smul_lt610 delta hdelta)
    (natDegree_smul_lt610 epsilon hepsilon) (natDegree_smul_lt610 zeta hzeta)
    (natDegree_smul_lt610 eta heta) (natDegree_smul_lt610 theta htheta)

end HighACone610

end Max11DegreeRoutes
