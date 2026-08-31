import FiniteRho2EarlyRouting
import FiniteRho2LoadSourceRoot
import FiniteRho2SourceAssembly

/-! # Assembly of the singular source at a nonzero `rho2` load -/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- Once all lower Faber parameters vanish, a nonzero `rho2` coefficient is
incompatible with a singular finite source at every load timing. -/
theorem TransverseScale.singular_source_inconsistent_of_rho2_ne_zero
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (R Rho3 Rho4 : k)
    (hR : R ≠ 0)
    (hdNormal : S.normal.d = 0)
    (hc7Normal : S.normal.c7 = 0)
    (hc5Normal : S.normal.c5 = 0)
    (hc4Normal : S.normal.c4 = 0)
    (hc3Normal : S.normal.c3 = 0)
    (hc2Normal : S.normal.c2 = 0)
    (hc1Normal : S.normal.c1 = 0)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant 0)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant 0)
    (hrho1 : F.rho1 = GCD369CubeHahnRegular.constant 0)
    (hrho2 : F.rho2 = GCD369CubeHahnRegular.constant R)
    (hrho3 : F.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : F.rho4 = GCD369CubeHahnRegular.constant Rho4) : False := by
  rcases le_or_gt ((11 * F.scale.p) / 2) T.delta with hle | hdeltaP
  · have hzero : R = 0 :=
      T.rho2_eq_zero_at_or_before_transverse F hscale
        R Rho3 Rho4
        hdNormal hc7Normal hc5Normal hc4Normal hc3Normal hc2Normal hc1Normal
        hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4 hle
    exact hR hzero
  · rcases lt_or_ge (11 * F.scale.p) (3 * T.delta) with hlt | hge
    · exact T.singular_source_inconsistent_at_active_rho2_of_lt
        F hscale R Rho3 Rho4 hR
        hd hc7 hc5 hc4 hc3 hc2 hc1
        hrho1 hrho2 hrho3 hrho4 hdeltaP hlt
    · exact T.singular_source_inconsistent_at_or_after_rho2_resonance
        F hscale R Rho3 Rho4
        hdNormal hc7Normal hc5Normal hc4Normal hc3Normal hc2Normal hc1Normal
        hd hc7 hc5 hc4 hc3 hc2 hc1
        hrho1 hrho2 hrho3 hrho4 hge

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.singular_source_inconsistent_of_rho2_ne_zero
