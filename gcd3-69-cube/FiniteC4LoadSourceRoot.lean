import FiniteC4EarlyNormal
import FiniteDoubleC4LoadLift

/-! # The strict active-`c4` singular source branch

The leading zero-load rows put every singular common cubic on its standard
double-root parametrization.  The active weight-five contradiction depends
only on that moving cubic root and on the transverse leading coordinates;
it therefore excludes both possible source-coordinate roots at once.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- If `c4` is the first nonzero Faber parameter and its load lies strictly
between the leading quadratic and intrinsic cubic scales, the singular
finite source branch is inconsistent. -/
theorem TransverseScale.singular_source_inconsistent_at_active_c4_of_lt
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 : k)
    (hC4 : C4 ≠ 0)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hrho1 : F.rho1 = GCD369CubeHahnRegular.constant Rho1)
    (hrho2 : F.rho2 = GCD369CubeHahnRegular.constant Rho2)
    (hrho3 : F.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : F.rho4 = GCD369CubeHahnRegular.constant Rho4)
    (hdeltaP : T.delta < (5 * F.scale.p) / 2)
    (hpDelta : 5 * F.scale.p < 3 * T.delta) : False := by
  have hd0 : F.d = 0 := by simpa using hd
  have hc70 : F.c7 = 0 := by simpa using hc7
  have hc50 : F.c5 = 0 := by simpa using hc5
  have hearly : 2 * T.delta < 5 * F.scale.p := by
    have htwice : 2 * ((5 * F.scale.p) / 2) = 5 * F.scale.p := by ring
    linarith
  obtain ⟨h1, h2, h3, h4⟩ :=
    T.factor.zeroLoadLeadingRows_before_c4 F hscale hd0 hc70 hc50
      (by simpa only [TransverseScale.factor] using hearly)
  obtain ⟨r0, hr0, hX, hu, hv, hY, hZ, _hrootCases, _hnormalRoot⟩ :=
    GCD369CubeZeroLoadNormal_root_data
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn)
      S.u S.v
      (GCD369CubeHahnRegular.constantCoeff S.normal.sextic.regularX)
      S.hprojective T.hleading h1 h2 h3 h4 S.leadingCubicRoot
  have hUne : GCD369CubeHahnRegular.constantCoeff S.cubicU ≠ 0 := by
    rw [S.constantCoeff_cubicU, hu]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hr0)
  let r : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.movingDoubleRoot S.cubicU S.cubicV hUne
  have huc : GCD369CubeHahnRegular.constantCoeff S.cubicU =
      -3 * r0 ^ 2 := by
    rw [S.constantCoeff_cubicU, hu]
  have hvc : GCD369CubeHahnRegular.constantCoeff S.cubicV =
      2 * r0 ^ 3 := by
    rw [S.constantCoeff_cubicV, hv]
  have hr : GCD369CubeHahnRegular.constantCoeff r = r0 := by
    exact GCD369CubeHahnRegular.constantCoeff_movingDoubleRoot
      S.cubicU S.cubicV hUne r0 huc hvc hr0
  have hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0 := by
    exact GCD369CubeHahnRegular.movingDoubleRoot_relation
      S.cubicU S.cubicV hUne
  exact T.factor.doubleRoot_c4Load_source_inconsistent_of_lt
    F hscale C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 hC4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
    r r0 (GCD369CubeHahnRegular.constantCoeff T.Xn) hr0 hX hr hu hv
    (by rfl) hY hZ hroot
    (by simpa only [TransverseScale.factor] using hdeltaP)
    (by simpa only [TransverseScale.factor] using hpDelta)

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.singular_source_inconsistent_at_active_c4_of_lt
