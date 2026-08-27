import FiniteDoubleSourceLiftC7
import FiniteSimpleSourceStrictFromSourceC7

/-! # Singular source-root split before `c7` -/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- Before the weight-two load, the literal source excludes the double-root
choice for the recovered source coordinate and leaves the simple root of the
singular leading cubic. -/
theorem TransverseScale.source_coordinate_is_simpleRoot_before_c7
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (hdNormal : S.normal.d = 0)
    (hd : F.d = 0)
    (hp : 3 * T.delta < 2 * F.scale.p) :
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
  have hearly : 2 * T.delta < 2 * F.scale.p := by
    nlinarith [T.hdelta, hp]
  obtain ⟨h1, h2, h3, h4⟩ :=
    T.factor.zeroLoadLeadingRows_before_c7 F hscale hd
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
    exact T.factor.doubleRoot_source_inconsistent_from_source_before_c7
      F hscale hdNormal hd
      (by simpa only [TransverseScale.factor] using hp)
      r r0 (GCD369CubeHahnRegular.constantCoeff T.Xn)
      hr0 hX hr huc hx (by rfl) hY hZ hmovingRoot
  · exact ⟨r0, hr0, hX, hu, hv, hY, hZ, hx⟩

/-- The complete singular source-root split is inconsistent before `c7`:
the double root is excluded by the double-root chart, and the remaining
simple root by the primitive third-row obstruction. -/
theorem TransverseScale.singular_source_inconsistent_before_c7
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (hdNormal : S.normal.d = 0)
    (hd : F.d = 0)
    (hp : 3 * T.delta < 2 * F.scale.p) : False := by
  obtain ⟨r0, hr0, hXne, hu, hv, hY, hZ, hx⟩ :=
    T.source_coordinate_is_simpleRoot_before_c7
      F hscale hdNormal hd hp
  have huc : GCD369CubeHahnRegular.constantCoeff S.cubicU =
      -3 * r0 ^ 2 := by
    rw [S.constantCoeff_cubicU, hu]
  have hvc : GCD369CubeHahnRegular.constantCoeff S.cubicV =
      2 * r0 ^ 3 := by
    rw [S.constantCoeff_cubicV, hv]
  exact T.factor.simpleRoot_strictLate_inconsistent_from_source_before_c7
    F hscale hdNormal hd
    (by simpa only [TransverseScale.factor] using hp)
    r0 (GCD369CubeHahnRegular.constantCoeff T.Xn)
    hr0 hXne huc hvc hx (by rfl) hY hZ

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.source_coordinate_is_simpleRoot_before_c7
#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.singular_source_inconsistent_before_c7
