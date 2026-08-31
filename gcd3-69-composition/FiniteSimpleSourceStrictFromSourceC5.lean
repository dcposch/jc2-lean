import FiniteSimpleSourceLiftC5
import FiniteSimpleSourceLateOrderC5
import FiniteSimpleSourceFullScale
import FiniteSimpleSourceFullScaleC5

/-! # Source-facing strict late simple-root obstruction before `c5`

The source-driven order lift and the literal sextic source equation remain
available below the weight-four load.  They promote the simple-root chart to
full-scale coordinates, where the primitive third row is inconsistent.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- If `3 * delta < 4 * p`, the weight-one load vanishes, and the recovered
source residue is the remaining simple root of the singular leading cubic,
then the literal finite source is inconsistent before the `c5` load. -/
theorem TransverseFactor.simpleRoot_strictLate_inconsistent_from_source_before_c5
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (hdNormal : S.normal.d = 0)
    (hc7Normal : S.normal.c7 = 0)
    (hd : F.d = 0)
    (hc7 : F.c7 = 0)
    (hp : 3 * T.delta < 4 * F.scale.p)
    (r0 A0 : k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hu : GCD369CubeHahnRegular.constantCoeff S.cubicU = -3 * r0 ^ 2)
    (hv : GCD369CubeHahnRegular.constantCoeff S.cubicV = 2 * r0 ^ 3)
    (hx : GCD369CubeHahnRegular.constantCoeff
      S.normal.sextic.regularX = -2 * r0)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r0 * A0)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r0 ^ 2 * A0) :
    False := by
  have hpS : 3 * T.delta < 4 * S.normal.sextic.scale.p := by
    rw [hscale]
    exact hp
  let hUne : GCD369CubeHahnRegular.constantCoeff S.cubicU ≠ 0 := by
    rw [hu]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hr0)
  let r : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.movingDoubleRoot S.cubicU S.cubicV hUne
  have hr : GCD369CubeHahnRegular.constantCoeff r = r0 := by
    exact GCD369CubeHahnRegular.constantCoeff_movingDoubleRoot
      S.cubicU S.cubicV hUne r0 hu hv hr0
  have hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0 := by
    exact GCD369CubeHahnRegular.movingDoubleRoot_relation
      S.cubicU S.cubicV hUne
  obtain ⟨hDfull, B, hYcoord, hQfull⟩ :=
    T.doubleRoot_deviations_order_delta_from_source_before_c5
      F hscale hd hc7 (le_of_lt hp) r r0 A0 hr0 hA0 hr hu hX hY hZ hroot
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let M : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial (T.delta / 2)
      (div_nonneg T.hdelta.le (by norm_num))
  let D : GCD369CubeHahnRegular k := S.cubicU + 3 * r ^ 2
  let d : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift D T.delta hDfull
  let e : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.ratCast (-2 / 3) * d * r
  let w : GCD369CubeHahnRegular k := S.normal.sextic.regularX + 2 * r
  let Ztail : GCD369CubeHahnRegular k :=
    T.Zn + 2 * r ^ 2 * T.Xn + M * r * B
  let C2n : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift Ztail T.delta hQfull
  have hDfact : H * d = D := by
    exact GCD369CubeHahnRegular.monomial_mul_shift
      D T.delta T.hdelta.le hDfull
  have hU : S.cubicU = -3 * r ^ 2 + H * d := by
    dsimp only [D] at hDfact
    linear_combination -hDfact
  have hscalar : (3 : GCD369CubeHahnRegular k) *
      GCD369CubeHahnRegular.ratCast (-2 / 3) = -2 := by
    calc
      _ = GCD369CubeHahnRegular.ratCast 3 *
          GCD369CubeHahnRegular.ratCast (-2 / 3) := by rw [map_ofNat]
      _ = GCD369CubeHahnRegular.ratCast (3 * (-2 / 3)) :=
        (map_mul _ _ _).symm
      _ = GCD369CubeHahnRegular.ratCast (-2) := by norm_num
      _ = -2 := by rw [map_neg, map_ofNat]
  have hre : 3 * e + 2 * d * r = 0 := by
    dsimp only [e]
    calc
      _ = (3 * GCD369CubeHahnRegular.ratCast (-2 / 3)) * d * r +
          2 * d * r := by ring
      _ = 0 := by rw [hscalar]; ring
  have hV : S.cubicV = 2 * r ^ 3 + H * e := by
    have hroot' := hroot
    rw [hU] at hroot'
    have hthree : (3 : GCD369CubeHahnRegular k) ≠ 0 := by
      intro hthree
      have h := congrArg
        (fun z : GCD369CubeHahnRegular k =>
          GCD369CubeHahnRegular.constantCoeff z) hthree
      simp only [map_ofNat, map_zero] at h
      exact (by norm_num : (3 : k) ≠ 0) h
    apply mul_left_cancel₀ hthree
    linear_combination hroot' - H * hre
  have hw0 : GCD369CubeHahnRegular.constantCoeff w = 0 := by
    dsimp only [w]
    simp only [map_add, map_mul, map_ofNat, hx, hr]
    ring
  have hxcoord : S.normal.sextic.regularX = -2 * r + w := by
    dsimp only [w]
    ring
  have hZfact : H * C2n = Ztail := by
    exact GCD369CubeHahnRegular.monomial_mul_shift
      Ztail T.delta T.hdelta.le hQfull
  have hZchart : T.Zn = -2 * r ^ 2 * T.Xn - M * r * B + H * C2n := by
    dsimp only [Ztail] at hZfact
    linear_combination -hZfact
  have hYchart : T.Yn = r * T.Xn + M * B + H * 0 := by
    simpa only [M, H, mul_zero, add_zero] using hYcoord
  have hsplit := T.simpleRoot_source_zero_or_order_delta_of_orderBounds_before_c5
    hdNormal hc7Normal r0 A0 r B hr0 hA0 (le_of_lt hpS) hr hx hX hroot
      hDfull hYcoord hQfull
  have hw : (↑T.delta : WithTop ℚ) ≤ w.1.orderTop := by
    rcases hsplit with hz | hord
    · have : w = 0 := by
        dsimp only [w]
        exact hz
      rw [this]
      simp
    · dsimp only [w]
      exact hord
  have hcharts := T.simpleRoot_chart_equations
    r w d e B 0 C2n hxcoord (by simpa only [H] using hU)
    (by simpa only [H] using hV) hre
    (by simpa only [M, H] using hYchart)
    (by simpa only [M, H] using hZchart)
  have hBhalf := T.simpleRoot_sourceLate_normal_order_half_lower_before_c5
    r0 A0 r w d B 0 C2n hr0 hA0 (le_of_lt hpS) hr hX hw0 hw
      hcharts.1 hcharts.2
  obtain ⟨_s, b, _hwfact, hYfull, hZfull⟩ :=
    T.simpleRoot_sourceLate_fullScale_coordinates
      r w B 0 C2n hw hBhalf
      (by simpa only [M, H] using hYchart)
      (by simpa only [M, H] using hZchart)
  have hDcoord : S.cubicU + 3 * r ^ 2 = H * d := by
    simpa only [D] using hDfact.symm
  have hBcoord : T.Yn - r * T.Xn = H * b := by
    have hY' : T.Yn = r * T.Xn + H * b := by
      simpa only [H, add_zero] using hYfull
    linear_combination hY'
  have hCcoord : T.Zn + 2 * r ^ 2 * T.Xn = H * (-r * b + C2n) := by
    have hZ' : T.Zn = -2 * r ^ 2 * T.Xn + H * (-r * b + C2n) := by
      simpa only [H] using hZfull
    linear_combination hZ'
  exact T.simpleRoot_strictLate_inconsistent_of_fullScale_before_c5
    F hscale hd hc7 hp r d b C2n r0 A0 hr hr0 hX hA0 hroot
      (by simpa only [H] using hDcoord)
      (by simpa only [H] using hBcoord)
      (by simpa only [H] using hCcoord)

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.simpleRoot_strictLate_inconsistent_from_source_before_c5
