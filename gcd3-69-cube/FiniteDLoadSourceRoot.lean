import FiniteEarlyNormal
import FiniteDoubleLoadLift

/-! # The strict active-`d` singular source branch

The leading zero-load rows put every singular common cubic on its standard
double-root parametrization.  The active weight-one contradiction depends
only on that moving cubic root and on the transverse leading coordinates;
it therefore excludes both possible source-coordinate roots at once.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- If `d` is the first nonzero Faber parameter and its load lies strictly
between the leading quadratic and intrinsic cubic scales, the singular
finite source branch is inconsistent. -/
theorem TransverseScale.singular_source_inconsistent_at_active_d_of_lt
    {k : Type*} [Field k] [CharZero k]
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
    (hrho4 : F.rho4 = GCD369CubeHahnRegular.constant Rho4)
    (hdeltaP : 2 * T.delta < F.scale.p)
    (hpDelta : F.scale.p < 3 * T.delta) : False := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    T.factor.zeroLoadLeadingRows_before_d F hscale
      D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
      (by simpa only [TransverseScale.factor] using hdeltaP)
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
  exact T.factor.doubleRoot_dLoad_source_inconsistent_of_lt
    F hscale D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 hD0
    hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
    r r0 (GCD369CubeHahnRegular.constantCoeff T.Xn) hr0 hX hr hu hv
    (by rfl) hY hZ hroot
    (by simpa only [TransverseScale.factor] using hdeltaP)
    (by simpa only [TransverseScale.factor] using hpDelta)

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.singular_source_inconsistent_at_active_d_of_lt
