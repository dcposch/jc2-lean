import FiniteSimpleSourceChartAllC4
import FiniteDoubleLiftSourceC4

/-! # Source-driven simple-root order lift before `c4` -/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- Full-scale cubic and corrected transverse bounds realize the simple-root
chart below `c4`; its displacement is zero or starts at `delta`. -/
theorem TransverseFactor.simpleRoot_source_zero_or_order_delta_of_orderBounds_before_c4
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (hd : S.normal.d = 0)
    (hc7 : S.normal.c7 = 0)
    (hc5 : S.normal.c5 = 0)
    (r0 A0 : k) (r B : GCD369CubeHahnRegular k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hp : 3 * T.delta ≤ 5 * S.normal.sextic.scale.p)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hx : GCD369CubeHahnRegular.constantCoeff
      S.normal.sextic.regularX = -2 * r0)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0)
    (hD : (↑T.delta : WithTop ℚ) ≤
      (S.cubicU + 3 * r ^ 2).1.orderTop)
    (hY : T.Yn = r * T.Xn +
      GCD369CubeHahnRegular.monomial (T.delta / 2)
        (div_nonneg T.hdelta.le (by norm_num)) * B)
    (hZ : (↑T.delta : WithTop ℚ) ≤
      (T.Zn + 2 * r ^ 2 * T.Xn +
        GCD369CubeHahnRegular.monomial (T.delta / 2)
          (div_nonneg T.hdelta.le (by norm_num)) * r * B).1.orderTop) :
    let w := S.normal.sextic.regularX + 2 * r
    w = 0 ∨ (↑T.delta : WithTop ℚ) ≤ w.1.orderTop := by
  dsimp only
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let M : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial (T.delta / 2)
      (div_nonneg T.hdelta.le (by norm_num))
  let D : GCD369CubeHahnRegular k := S.cubicU + 3 * r ^ 2
  let d : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift D T.delta hD
  let e : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.ratCast (-2 / 3) * d * r
  let w : GCD369CubeHahnRegular k := S.normal.sextic.regularX + 2 * r
  let Ztail : GCD369CubeHahnRegular k :=
    T.Zn + 2 * r ^ 2 * T.Xn + M * r * B
  let C2 : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift Ztail T.delta hZ
  have hDfact : H * d = D := by
    exact GCD369CubeHahnRegular.monomial_mul_shift
      D T.delta T.hdelta.le hD
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
  have hZfact : H * C2 = Ztail := by
    exact GCD369CubeHahnRegular.monomial_mul_shift
      Ztail T.delta T.hdelta.le hZ
  have hZcoord : T.Zn = -2 * r ^ 2 * T.Xn - M * r * B + H * C2 := by
    dsimp only [Ztail] at hZfact
    linear_combination -hZfact
  exact T.simpleRoot_source_zero_or_order_delta_of_coordinates_before_c4
    hd hc7 hc5 r0 A0 r w d e B 0 C2 hr0 hA0 hp hr hX hw0 hxcoord
    (by simpa only [H] using hU) (by simpa only [H] using hV) hre
    (by simpa only [M, H, mul_zero, add_zero] using hY)
    (by simpa only [M, H] using hZcoord)

/-- The literal source and the moving double root supply the preceding
simple-root order split before `c4`. -/
theorem TransverseFactor.simpleRoot_source_zero_or_order_delta_from_source_before_c4
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (hdNormal : S.normal.d = 0)
    (hc7Normal : S.normal.c7 = 0)
    (hc5Normal : S.normal.c5 = 0)
    (hd : F.d = 0)
    (hc7 : F.c7 = 0)
    (hc5 : F.c5 = 0)
    (hp : 3 * T.delta < 5 * F.scale.p)
    (r0 A0 : k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hu : GCD369CubeHahnRegular.constantCoeff S.cubicU = -3 * r0 ^ 2)
    (hv : GCD369CubeHahnRegular.constantCoeff S.cubicV = 2 * r0 ^ 3)
    (hx : GCD369CubeHahnRegular.constantCoeff
      S.normal.sextic.regularX = -2 * r0)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r0 * A0)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r0 ^ 2 * A0) :
    let hUne : GCD369CubeHahnRegular.constantCoeff S.cubicU ≠ 0 := by
      rw [hu]
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hr0)
    let r := GCD369CubeHahnRegular.movingDoubleRoot
      S.cubicU S.cubicV hUne
    let w := S.normal.sextic.regularX + 2 * r
    w = 0 ∨ (↑T.delta : WithTop ℚ) ≤ w.1.orderTop := by
  dsimp only
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
    T.doubleRoot_deviations_order_delta_from_source_before_c4
      F hscale hd hc7 hc5 (le_of_lt hp) r r0 A0 hr0 hA0 hr hu hX hY hZ hroot
  have hpS : 3 * T.delta < 5 * S.normal.sextic.scale.p := by
    rw [hscale]
    exact hp
  exact T.simpleRoot_source_zero_or_order_delta_of_orderBounds_before_c4
    hdNormal hc7Normal hc5Normal r0 A0 r B hr0 hA0 (le_of_lt hpS) hr hx hX hroot
    hDfull hYcoord hQfull

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.simpleRoot_source_zero_or_order_delta_of_orderBounds_before_c4
#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.simpleRoot_source_zero_or_order_delta_from_source_before_c4
