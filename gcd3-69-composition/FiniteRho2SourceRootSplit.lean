import FiniteDoubleSourceLiftRho2
import FiniteDoubleZeroLoadCubicLiftRho2

/-! # Singular source-root split before `rho2` -/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- Before the weight-eleven load, the literal source excludes the double-root
choice for the recovered source coordinate and leaves the simple root of the
singular leading cubic. -/
theorem TransverseScale.source_coordinate_is_simpleRoot_before_rho2
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (hdNormal : S.normal.d = 0)
    (hc7Normal : S.normal.c7 = 0)
    (hc5Normal : S.normal.c5 = 0)
    (hc4Normal : S.normal.c4 = 0)
    (hc3Normal : S.normal.c3 = 0)
    (hc2Normal : S.normal.c2 = 0)
    (hc1Normal : S.normal.c1 = 0)
    (hd : F.d = 0)
    (hc7 : F.c7 = 0)
    (hc5 : F.c5 = 0)
    (hc4 : F.c4 = 0)
    (hc3 : F.c3 = 0)
    (hc2 : F.c2 = 0)
    (hc1 : F.c1 = 0)
    (hr1 : F.rho1 = 0)
    (hp : 3 * T.delta ≤ 11 * F.scale.p) :
    let x := GCD369CubeHahnRegular.constantCoeff
      S.normal.sextic.regularX
    ∃ r : k, r ≠ 0 ∧
      GCD369CubeHahnRegular.constantCoeff T.Xn ≠ 0 ∧
      S.u = -3 * r ^ 2 ∧ S.v = 2 * r ^ 3 ∧
      GCD369CubeHahnRegular.constantCoeff T.Yn =
        r * GCD369CubeHahnRegular.constantCoeff T.Xn ∧
      GCD369CubeHahnRegular.constantCoeff T.Zn =
        -2 * r ^ 2 * GCD369CubeHahnRegular.constantCoeff T.Xn ∧
      x = -2 * r := by
  dsimp only
  have hearly : 2 * T.delta < 11 * F.scale.p := by
    nlinarith [T.hdelta, hp]
  obtain ⟨h1, h2, h3, h4⟩ :=
    T.factor.zeroLoadLeadingRows_before_rho2 F hscale
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1
      (by simpa only [TransverseScale.factor] using hearly)
  obtain ⟨r0, hr0, hX, hu, hv, hY, hZ, hrootCases, _hnormalRoot⟩ :=
    GCD369CubeZeroLoadNormal_root_data
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn)
      S.u S.v
      (GCD369CubeHahnRegular.constantCoeff S.normal.sextic.regularX)
      S.hprojective T.hleading h1 h2 h3 h4 S.leadingCubicRoot
  rcases hrootCases with hx | hx
  · exfalso
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
    have hmovingRoot : 2 * S.cubicU * r + 3 * S.cubicV = 0 := by
      exact GCD369CubeHahnRegular.movingDoubleRoot_relation
        S.cubicU S.cubicV hUne
    exact T.factor.doubleRoot_source_inconsistent_from_source_before_rho2
      F hscale hdNormal hc7Normal hc5Normal hc4Normal hc3Normal
      hc2Normal hc1Normal
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1
      (by simpa only [TransverseScale.factor] using hp)
      r r0 (GCD369CubeHahnRegular.constantCoeff T.Xn)
      hr0 hX hr huc hx (by rfl) hY hZ hmovingRoot
  · exact ⟨r0, hr0, hX, hu, hv, hY, hZ, hx⟩

/-- Strictly before the weight-eleven load, the balanced zero-load cubic
obstruction excludes the singular source independently of which cubic root
is selected by the literal source coordinate. -/
theorem TransverseScale.singular_source_inconsistent_before_rho2
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (hdNormal : S.normal.d = 0)
    (hc7Normal : S.normal.c7 = 0)
    (hc5Normal : S.normal.c5 = 0)
    (hc4Normal : S.normal.c4 = 0)
    (hc3Normal : S.normal.c3 = 0)
    (hc2Normal : S.normal.c2 = 0)
    (hc1Normal : S.normal.c1 = 0)
    (hd : F.d = 0)
    (hc7 : F.c7 = 0)
    (hc5 : F.c5 = 0)
    (hc4 : F.c4 = 0)
    (hc3 : F.c3 = 0)
    (hc2 : F.c2 = 0)
    (hc1 : F.c1 = 0)
    (hr1 : F.rho1 = 0)
    (hp : 3 * T.delta < 11 * F.scale.p) : False := by
  let _ := hdNormal
  let _ := hc7Normal
  let _ := hc5Normal
  let _ := hc4Normal
  let _ := hc3Normal
  let _ := hc2Normal
  let _ := hc1Normal
  have hearly : 2 * T.delta < 11 * F.scale.p := by
    nlinarith [T.hdelta, hp]
  obtain ⟨h1, h2, h3, h4⟩ :=
    T.factor.zeroLoadLeadingRows_before_rho2 F hscale
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1
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
  exact T.factor.doubleRoot_inconsistent_before_rho2
    F hscale hd hc7 hc5 hc4 hc3 hc2 hc1 hr1
    (by simpa only [TransverseScale.factor] using hp)
    r r0 (GCD369CubeHahnRegular.constantCoeff T.Xn)
    hr0 hX hr huc (by rfl) hY hZ hroot

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.source_coordinate_is_simpleRoot_before_rho2
#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.singular_source_inconsistent_before_rho2
