import FiniteRho2SourceRootSplit
import FiniteRho2LoadSourceRootEndpoint

/-! # Assembly of the singular source at or after `rho2` resonance

The source-facing `rho2` branch is empty both strictly before the
weight-eleven resonance and at the exact cubic tie. -/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- If the intrinsic cubic meets or precedes the weight-eleven `rho2` load,
`3 * delta ≤ 11 * p`, the singular finite source is inconsistent. -/
theorem TransverseScale.singular_source_inconsistent_at_or_after_rho2_resonance
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (R Rho3 Rho4 : k)
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
    (hrho4 : F.rho4 = GCD369CubeHahnRegular.constant Rho4)
    (hp : 3 * T.delta ≤ 11 * F.scale.p) : False := by
  rcases eq_or_lt_of_le hp with hEq | hlt
  · exact T.singular_source_inconsistent_at_active_rho2_of_eq
      F hscale R Rho3 Rho4
      hdNormal hc7Normal hc5Normal hc4Normal hc3Normal hc2Normal hc1Normal
      hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4 hEq.symm
  · have hd0 : F.d = 0 := by simpa using hd
    have hc70 : F.c7 = 0 := by simpa using hc7
    have hc50 : F.c5 = 0 := by simpa using hc5
    have hc40 : F.c4 = 0 := by simpa using hc4
    have hc30 : F.c3 = 0 := by simpa using hc3
    have hc20 : F.c2 = 0 := by simpa using hc2
    have hc10 : F.c1 = 0 := by simpa using hc1
    have hr10 : F.rho1 = 0 := by simpa using hrho1
    exact T.singular_source_inconsistent_before_rho2
      F hscale hdNormal hc7Normal hc5Normal hc4Normal hc3Normal hc2Normal
      hc1Normal hd0 hc70 hc50 hc40 hc30 hc20 hc10 hr10 hlt

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.singular_source_inconsistent_at_or_after_rho2_resonance
