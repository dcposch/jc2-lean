import InfinityDBalanced
import InfinityLaterTerminal
import FiniteTargetNormalizedParameters
import FiniteFanLaterHandoff

noncomputable section

/-! # Infinity later-fan handoff

This module packages the already-complete ends of the constant-core
argument.  The infinity analysis supplies `d = 0`; after target
normalization, vanishing of the seven remaining early loads is now the only
input needed by the constant-core terminal exclusion.
-/

namespace GCD369CubePolynomialSource

/-- The target-normalized constant-core source has a genuine infinity
transverse scale.  This is the canonical packet on which the remaining
weight-two through weight-eleven fan is to run. -/
theorem targetNormalized_infinity_transverseScale_nonempty
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0) :
    let U := S.targetNormalizedSource
    Nonempty (U.infinityCommonCoefficientData (by
      simpa [U, targetNormalizedSource] using hsdegree)).TransverseScale := by
  dsimp only
  let U := S.targetNormalizedSource
  have hsdegreeU : U.s.natDegree = 0 := by
    simpa [U, targetNormalizedSource] using hsdegree
  exact U.infinity_transverseScale_nonempty hsdegreeU

/-- Once the canonical parameters of the target-normalized source vanish
through `rho2`, the constant-core source is impossible.  Parameter
uniqueness transports the source loads back to the original barred
coordinates, and first-integral uniqueness transports `rho1,rho2`. -/
theorem targetNormalized_earlyLoads_empty_of_constantCore
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (hc7 : S.targetNormalizedSource.faberConstantParameters.c7 = 0)
    (hc5 : S.targetNormalizedSource.faberConstantParameters.c5 = 0)
    (hc4 : S.targetNormalizedSource.faberConstantParameters.c4 = 0)
    (hc2 : S.targetNormalizedSource.faberConstantParameters.c2 = 0)
    (hc1 : S.targetNormalizedSource.faberConstantParameters.c1 = 0)
    (hrho1 :
      S.targetNormalizedSource.faberFirstIntegralConstants.rho1 = 0)
    (hrho2 :
      S.targetNormalizedSource.faberFirstIntegralConstants.rho2 = 0) :
    False := by
  let U := S.targetNormalizedSource
  let P := S.faberConstantParameters
  let Q := U.faberConstantParameters
  have hd : P.d = 0 := S.infinity_d_eq_zero_of_constantCore hsdegree
  obtain ⟨_hQd, hQc7, _hQc6, hQc5, hQc4, _hQc3, hQc2,
      hQc1, _hQc0⟩ := S.targetNormalizedCanonicalParameters hd
  have hPc7 : P.c7 = 0 := hQc7.symm.trans (by simpa [Q, U] using hc7)
  have hPc5 : P.c5 = 0 := hQc5.symm.trans (by simpa [Q, U] using hc5)
  have hPc4 : P.c4 = 0 := hQc4.symm.trans (by simpa [Q, U] using hc4)
  have hPc2 : P.c2 = 0 := hQc2.symm.trans (by simpa [Q, U] using hc2)
  have hPc1bar : P.c1 - 7 * P.c7 * P.c3 / 9 = 0 :=
    hQc1.symm.trans (by simpa [Q, U] using hc1)
  obtain ⟨hR1, hR2, _hR3, _hR4⟩ :=
    S.targetNormalizedFirstIntegralConstants_eq hd
  have hR1zero : (S.targetNormalizedFirstIntegralConstants hd).rho1 = 0 :=
    hR1.trans hrho1
  have hR2zero : (S.targetNormalizedFirstIntegralConstants hd).rho2 = 0 :=
    hR2.trans hrho2
  exact S.targetNormalizedLater_empty_of_constantCore hsdegree hd
    hPc7 hPc5 hPc4 hPc2 hPc1bar hR1zero hR2zero

end GCD369CubePolynomialSource

#print axioms
  GCD369CubePolynomialSource.targetNormalized_infinity_transverseScale_nonempty
#print axioms
  GCD369CubePolynomialSource.targetNormalized_earlyLoads_empty_of_constantCore
