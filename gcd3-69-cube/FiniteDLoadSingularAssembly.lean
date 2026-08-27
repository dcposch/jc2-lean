import FiniteEarlyLoadTied
import FiniteDLoadSourceRoot
import FiniteDLoadSourceRootEndpoint
import FinitePoleBranchAssembly

/-! # Assembly of the singular source at a nonzero `d` load

A nonzero weight-one `d` coefficient is inconsistent at every timing of the
first pole scale.  The early routing theorem covers `p ≤ 2 * delta`, the
loaded moving-root argument covers the strict middle interval, the balanced
coefficient extraction closes `p = 3 * delta`, and the source-facing
simple-root obstruction covers the strict late interval.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- A nonzero constant `d` is incompatible with a singular finite source at
every relative timing of the first pole scale. -/
theorem TransverseScale.singular_source_inconsistent_of_d_ne_zero
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 : k)
    (hD0 : D0 ≠ 0)
    (hd : F.d = GCD369CubeHahnRegular.constant D0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hrho1 : F.rho1 = GCD369CubeHahnRegular.constant Rho1)
    (hrho2 : F.rho2 = GCD369CubeHahnRegular.constant Rho2)
    (hrho3 : F.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : F.rho4 = GCD369CubeHahnRegular.constant Rho4) : False := by
  rcases le_or_gt F.scale.p (2 * T.delta) with hle | hmiddle
  · have hzero : D0 = 0 :=
      T.d_eq_zero_at_or_before_transverse F hscale
        D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
        hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4 hle
    exact hD0 hzero
  · rcases lt_trichotomy F.scale.p (3 * T.delta) with hlt | heq | hlate
    · exact T.singular_source_inconsistent_at_active_d_of_lt
        F hscale D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 hD0
        hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
        hmiddle hlt
    · exact T.singular_source_inconsistent_at_active_d_of_eq
        F hscale D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
        hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4 heq
    · exact T.simpleRoot_strictLate_inconsistent_from_source
        F hscale D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
        hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4 hlate

/-- On the singular finite source branch, the first weight-one Faber
constant must vanish. -/
theorem TransverseScale.singular_source_forces_d_eq_zero
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant D0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hrho1 : F.rho1 = GCD369CubeHahnRegular.constant Rho1)
    (hrho2 : F.rho2 = GCD369CubeHahnRegular.constant Rho2)
    (hrho3 : F.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : F.rho4 = GCD369CubeHahnRegular.constant Rho4) :
    D0 = 0 := by
  by_contra hD0
  exact T.singular_source_inconsistent_of_d_ne_zero F hscale
    D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 hD0
    hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4

end GCD369CubeHahnCommonValueData

namespace GCD369CubePolynomialSource

/-- Literal finite-pole form of the complete singular-source `d = 0`
theorem. -/
theorem finite_singular_source_forces_d_eq_zero
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0)
    (T : (S.finiteCommonValueData a hpole).TransverseScale) :
    S.faberConstantParameters.d = 0 := by
  let F := S.finiteFaberPoleData a hpole
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  exact T.singular_source_forces_d_eq_zero F rfl
    P.d P.c7 P.c5 P.c4 P.c3 P.c2 P.c1
    R.rho1 R.rho2 R.rho3 R.rho4
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.d)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.c7)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.c5)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.c4)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.c3)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.c2)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.c1)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a R.rho1)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a R.rho2)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a R.rho3)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a R.rho4)

end GCD369CubePolynomialSource

#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.singular_source_inconsistent_of_d_ne_zero
#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.singular_source_forces_d_eq_zero
#print axioms
  GCD369CubePolynomialSource.finite_singular_source_forces_d_eq_zero
