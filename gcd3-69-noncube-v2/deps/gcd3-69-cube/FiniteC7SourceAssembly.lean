import FiniteC7SourceRootSplit
import FiniteC7LoadSourceRootEndpoint

/-! # Assembly of the singular source at or after `c7` resonance

The source-facing `c7` branch is empty both strictly before the weight-two
resonance and at the exact cubic tie.  The two existing contradictions
compose on a single `≤` hypothesis; no nonzero `c7` coefficient is required.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- If the first source load meets or exceeds the weight-two `c7` resonance
`3 * delta ≤ 2 * p`, the singular finite source is inconsistent. -/
theorem TransverseScale.singular_source_inconsistent_at_or_after_c7_resonance
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 : k)
    (hdNormal : S.normal.d = 0)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hrho1 : F.rho1 = GCD369CubeHahnRegular.constant Rho1)
    (hrho2 : F.rho2 = GCD369CubeHahnRegular.constant Rho2)
    (hrho3 : F.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : F.rho4 = GCD369CubeHahnRegular.constant Rho4)
    (hp : 3 * T.delta ≤ 2 * F.scale.p) : False := by
  rcases eq_or_lt_of_le hp with hEq | hlt
  · exact T.singular_source_inconsistent_at_active_c7_of_eq
      F hscale C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
      hdNormal hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
      hEq.symm
  · have hd0 : F.d = 0 := by simpa using hd
    exact T.singular_source_inconsistent_before_c7
      F hscale hdNormal hd0 hlt

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.singular_source_inconsistent_at_or_after_c7_resonance
