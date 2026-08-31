import FiniteC5EarlyRouting
import FiniteC5LoadSourceRoot
import FiniteC5SourceAssembly

/-! # Assembly of the singular source at a nonzero `c5` load

A nonzero weight-four `c5` coefficient is inconsistent on every timing of
the first source load.  Arrival no later than the transverse normal already
forces `c5 = 0`.  After that scale the remaining two source-facing branches
cover the strict active window and the cubic resonance or later.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- If the first nonzero Faber parameter is a weight-four `c5` constant, the
singular finite source is inconsistent at every load timing. -/
theorem TransverseScale.singular_source_inconsistent_of_c5_ne_zero
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 : k)
    (hC5 : C5 ≠ 0)
    (hdNormal : S.normal.d = 0)
    (hc7Normal : S.normal.c7 = 0)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hrho1 : F.rho1 = GCD369CubeHahnRegular.constant Rho1)
    (hrho2 : F.rho2 = GCD369CubeHahnRegular.constant Rho2)
    (hrho3 : F.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : F.rho4 = GCD369CubeHahnRegular.constant Rho4) : False := by
  rcases le_or_gt (2 * F.scale.p) T.delta with hle | hdeltaP
  · have hzero : C5 = 0 :=
      T.c5_eq_zero_at_or_before_transverse F hscale
        C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
        hdNormal hc7Normal hd hc7 hc5 hc4 hc3 hc2 hc1
        hrho1 hrho2 hrho3 hrho4 hle
    exact hC5 hzero
  · rcases lt_or_ge (4 * F.scale.p) (3 * T.delta) with hlt | hge
    · exact T.singular_source_inconsistent_at_active_c5_of_lt
        F hscale C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 hC5
        hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
        hdeltaP hlt
    · exact T.singular_source_inconsistent_at_or_after_c5_resonance
        F hscale C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
        hdNormal hc7Normal hd hc7 hc5 hc4 hc3 hc2 hc1
        hrho1 hrho2 hrho3 hrho4
        hge

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.singular_source_inconsistent_of_c5_ne_zero
