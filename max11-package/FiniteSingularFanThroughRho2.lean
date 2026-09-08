import FiniteDLoadSingularAssembly
import FiniteC7SingularAssembly
import FiniteC5SingularAssembly
import FiniteC4SingularAssembly
import FiniteC2SingularAssembly
import FiniteC1SingularAssembly
import FiniteRho1SingularAssembly
import FiniteRho2SingularAssembly

/-! # The singular early-load fan through weight eleven

The source-facing singular exclusions are triangular: once each lower Faber
load has vanished, the next nonzero load is impossible at every timing of
the first transverse scale.  Chaining them kills all loads through `rho2`.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- In the `c3 = 0` gauge, the singular source exclusions force every Faber
load through weight eleven to vanish. -/
theorem TransverseScale.singular_earlyLoads_zero_through_rho2
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (D C7 C5 C4 C2 C1 R1 R2 R3 R4 : k)
    (hdNormal : S.normal.d = GCD369CubeHahnRegular.constant D)
    (hc7Normal : S.normal.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5Normal : S.normal.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4Normal : S.normal.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3Normal : S.normal.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2Normal : S.normal.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1Normal : S.normal.c1 = GCD369CubeHahnRegular.constant C1)
    (hd : F.d = GCD369CubeHahnRegular.constant D)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : F.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : F.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : F.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : F.rho4 = GCD369CubeHahnRegular.constant R4) :
    D = 0 ∧ C7 = 0 ∧ C5 = 0 ∧ C4 = 0 ∧ C2 = 0 ∧ C1 = 0 ∧
      R1 = 0 ∧ R2 = 0 := by
  have hD : D = 0 := by
    by_contra hne
    exact T.singular_source_inconsistent_of_d_ne_zero F hscale
      D C7 C5 C4 0 C2 C1 R1 R2 R3 R4 hne
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4
  have hfd : F.d = GCD369CubeHahnRegular.constant 0 := by rw [hd, hD]
  have hnd : S.normal.d = 0 := by rw [hdNormal, hD]; simp
  have hC7 : C7 = 0 := by
    by_contra hne
    exact T.singular_source_inconsistent_of_c7_ne_zero F hscale
      C7 C5 C4 0 C2 C1 R1 R2 R3 R4 hne hnd
      hfd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4
  have hfc7 : F.c7 = GCD369CubeHahnRegular.constant 0 := by rw [hc7, hC7]
  have hnc7 : S.normal.c7 = 0 := by rw [hc7Normal, hC7]; simp
  have hC5 : C5 = 0 := by
    by_contra hne
    exact T.singular_source_inconsistent_of_c5_ne_zero F hscale
      C5 C4 0 C2 C1 R1 R2 R3 R4 hne hnd hnc7
      hfd hfc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4
  have hfc5 : F.c5 = GCD369CubeHahnRegular.constant 0 := by rw [hc5, hC5]
  have hnc5 : S.normal.c5 = 0 := by rw [hc5Normal, hC5]; simp
  have hC4 : C4 = 0 := by
    by_contra hne
    exact T.singular_source_inconsistent_of_c4_ne_zero F hscale
      C4 0 C2 C1 R1 R2 R3 R4 hne hnd hnc7 hnc5
      hfd hfc7 hfc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4
  have hfc4 : F.c4 = GCD369CubeHahnRegular.constant 0 := by rw [hc4, hC4]
  have hnc4 : S.normal.c4 = 0 := by rw [hc4Normal, hC4]; simp
  have hnc3 : S.normal.c3 = 0 := by simpa using hc3Normal
  have hfc3 : F.c3 = GCD369CubeHahnRegular.constant 0 := hc3
  have hC2 : C2 = 0 := by
    by_contra hne
    exact T.singular_source_inconsistent_of_c2_ne_zero F hscale
      C2 C1 R1 R2 R3 R4 hne hnd hnc7 hnc5 hnc4 hnc3
      hfd hfc7 hfc5 hfc4 hfc3 hc2 hc1 hr1 hr2 hr3 hr4
  have hfc2 : F.c2 = GCD369CubeHahnRegular.constant 0 := by rw [hc2, hC2]
  have hnc2 : S.normal.c2 = 0 := by rw [hc2Normal, hC2]; simp
  have hC1 : C1 = 0 := by
    by_contra hne
    exact T.singular_source_inconsistent_of_c1_ne_zero F hscale
      C1 R1 R2 R3 R4 hne hnd hnc7 hnc5 hnc4 hnc3 hnc2
      hfd hfc7 hfc5 hfc4 hfc3 hfc2 hc1 hr1 hr2 hr3 hr4
  have hfc1 : F.c1 = GCD369CubeHahnRegular.constant 0 := by rw [hc1, hC1]
  have hnc1 : S.normal.c1 = 0 := by rw [hc1Normal, hC1]; simp
  have hR1 : R1 = 0 := by
    by_contra hne
    exact T.singular_source_inconsistent_of_rho1_ne_zero F hscale
      R1 R2 R3 R4 hne hnd hnc7 hnc5 hnc4 hnc3 hnc2 hnc1
      hfd hfc7 hfc5 hfc4 hfc3 hfc2 hfc1 hr1 hr2 hr3 hr4
  have hfr1 : F.rho1 = GCD369CubeHahnRegular.constant 0 := by rw [hr1, hR1]
  have hR2 : R2 = 0 := by
    by_contra hne
    exact T.singular_source_inconsistent_of_rho2_ne_zero F hscale
      R2 R3 R4 hne hnd hnc7 hnc5 hnc4 hnc3 hnc2 hnc1
      hfd hfc7 hfc5 hfc4 hfc3 hfc2 hfc1 hfr1 hr2 hr3 hr4
  exact ⟨hD, hC7, hC5, hC4, hC2, hC1, hR1, hR2⟩

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.singular_earlyLoads_zero_through_rho2
