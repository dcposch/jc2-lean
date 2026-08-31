import InfinityRho1Assembly
import InfinityRho2Before
import InfinityRho2Tie
import InfinityRho2Middle
import InfinityRho2Balanced
import InfinityRho2Late

/-! # Complete weight-eleven infinity fan

After every earlier load vanishes, `rho2` is the final weight-eleven load.
This file assembles its five timing cells and packages all seven normalized
load vanishings needed by the constant-core terminal exclusion.
-/

noncomputable section

namespace GCD369CubePolynomialSource

/-- With the canonical gauge and all earlier loads zero, the final
first-integral parameter `rho2` vanishes. -/
theorem infinity_rho2_eq_zero
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hd0 : S.faberConstantParameters.d = 0)
    (hc70 : S.faberConstantParameters.c7 = 0)
    (hc50 : S.faberConstantParameters.c5 = 0)
    (hc40 : S.faberConstantParameters.c4 = 0)
    (hc30 : S.faberConstantParameters.c3 = 0)
    (hc20 : S.faberConstantParameters.c2 = 0)
    (hc10 : S.faberConstantParameters.c1 = 0)
    (hrho10 : S.faberFirstIntegralConstants.rho1 = 0) :
    S.faberFirstIntegralConstants.rho2 = 0 := by
  let D := S.infinityCommonCoefficientData hsdegree
  rcases lt_trichotomy (11 * D.faber.scale.p) (2 * T.delta) with
      hbefore | htie | hafter
  · exact S.infinity_rho2_eq_zero_strict_before hsdegree T
      hd0 hc70 hc50 hc40 hc30 hc20 hc10 hrho10
      (by simpa only [D] using hbefore)
  · exact S.infinity_rho2_eq_zero_at_transverse hsdegree T
      hd0 hc70 hc50 hc40 hc30 hc20 hc10 hrho10
      (by simpa only [D] using htie)
  · rcases lt_trichotomy (11 * D.faber.scale.p) (3 * T.delta) with
        hmiddle | hbalanced | hlate
    · exact S.infinity_rho2_eq_zero_singular_middle hsdegree T
        hd0 hc70 hc50 hc40 hc30 hc20 hc10 hrho10
        (by simpa only [D] using hafter)
        (by simpa only [D] using hmiddle)
    · exact (S.infinity_rho2_singular_balanced_inconsistent hsdegree T
        hd0 hc70 hc50 hc40 hc30 hc20 hc10 hrho10
        (by simpa only [D] using hbalanced)).elim
    · exact (S.infinity_rho2_singular_late_inconsistent hsdegree T
        hd0 hc70 hc50 hc40 hc30 hc20 hc10 hrho10
        (by simpa only [D] using hlate)).elim

/-- The target-normalized constant-core infinity fan forces all seven
genuine loads through `rho2` to vanish. -/
theorem targetNormalized_infinity_loads_through_rho2
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : let U := S.targetNormalizedSource
      let hsdegreeU : U.s.natDegree = 0 := by
        simpa [U, targetNormalizedSource] using hsdegree
      (U.infinityCommonCoefficientData hsdegreeU).TransverseScale) :
    let U := S.targetNormalizedSource
    U.faberConstantParameters.c7 = 0 ∧
      U.faberConstantParameters.c5 = 0 ∧
      U.faberConstantParameters.c4 = 0 ∧
      U.faberConstantParameters.c2 = 0 ∧
      U.faberConstantParameters.c1 = 0 ∧
      U.faberFirstIntegralConstants.rho1 = 0 ∧
      U.faberFirstIntegralConstants.rho2 = 0 := by
  dsimp only
  let U := S.targetNormalizedSource
  have hsdegreeU : U.s.natDegree = 0 := by
    simpa [U, targetNormalizedSource] using hsdegree
  obtain ⟨hc7, hc5, hc4, hc2, hc1, hrho1⟩ :=
    S.targetNormalized_infinity_loads_through_rho1 hsdegree T
  have hdS : S.faberConstantParameters.d = 0 :=
    S.infinity_d_eq_zero_of_constantCore hsdegree
  obtain ⟨hUd, _hUc7, _hUc6, _hUc5, _hUc4, hUc3, _hUc2,
      _hUc1, _hUc0⟩ := S.targetNormalizedCanonicalParameters hdS
  have hdU : U.faberConstantParameters.d = 0 := by
    simpa only [U] using hUd
  have hc3 : U.faberConstantParameters.c3 = 0 := by
    simpa only [U] using hUc3
  have hrho2 := U.infinity_rho2_eq_zero hsdegreeU T
    hdU hc7 hc5 hc4 hc3 hc2 hc1 hrho1
  exact ⟨hc7, hc5, hc4, hc2, hc1, hrho1, hrho2⟩

end GCD369CubePolynomialSource

#print axioms GCD369CubePolynomialSource.infinity_rho2_eq_zero
#print axioms
  GCD369CubePolynomialSource.targetNormalized_infinity_loads_through_rho2
