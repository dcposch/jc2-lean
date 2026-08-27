import FiniteDoubleSourceChartAll

/-! # Order-bound realization of the late double-root chart

The complete chart exclusion is most useful upstream when expressed through
divisibility/order bounds.  This file constructs the required corrections by
shifting regular Hahn series at `delta / 2` and `delta`.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- A moving cubic relation, a half-scale transverse kernel correction, and
two `delta`-order remainder bounds realize the chart for `p ≥ 3 * delta` and are
therefore inconsistent with the literal sextic/nonic source equations. -/
theorem TransverseFactor.doubleRoot_source_inconsistent_of_orderBounds
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r0 A0 : k) (r B : GCD369CubeHahnRegular k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hp : 3 * T.delta ≤ S.normal.sextic.scale.p)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hx : GCD369CubeHahnRegular.constantCoeff
      S.normal.sextic.regularX = r0)
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
          (div_nonneg T.hdelta.le (by norm_num)) * r * B).1.orderTop) : False := by
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
  let w : GCD369CubeHahnRegular k := S.normal.sextic.regularX - r
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
    simp only [map_sub, hx, hr, sub_self]
  have hxcoord : S.normal.sextic.regularX = r + w := by
    dsimp only [w]
    ring
  have hZfact : H * C2 = Ztail := by
    exact GCD369CubeHahnRegular.monomial_mul_shift
      Ztail T.delta T.hdelta.le hZ
  have hZcoord : T.Zn = -2 * r ^ 2 * T.Xn - M * r * B + H * C2 := by
    dsimp only [Ztail] at hZfact
    linear_combination -hZfact
  exact T.doubleRoot_source_inconsistent_of_coordinates
    r0 A0 r w d e B 0 C2 hr0 hA0 hp hr hX hw0 hxcoord
    (by simpa only [H] using hU) (by simpa only [H] using hV) hre
    (by simpa only [M, H, mul_zero, add_zero] using hY)
    (by simpa only [M, H] using hZcoord)

/-- The half-scale coefficient `B` need not be supplied in advance: an order
bound on `Yn - r*Xn` constructs it canonically by a Hahn shift. -/
theorem TransverseFactor.doubleRoot_source_inconsistent_of_deviationBounds
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r0 A0 : k) (r : GCD369CubeHahnRegular k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hp : 3 * T.delta ≤ S.normal.sextic.scale.p)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hx : GCD369CubeHahnRegular.constantCoeff
      S.normal.sextic.regularX = r0)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0)
    (hD : (↑T.delta : WithTop ℚ) ≤
      (S.cubicU + 3 * r ^ 2).1.orderTop)
    (hB : (↑(T.delta / 2) : WithTop ℚ) ≤
      (T.Yn - r * T.Xn).1.orderTop)
    (hZ :
      let B := GCD369CubeHahnRegular.shift
        (T.Yn - r * T.Xn) (T.delta / 2) hB
      (↑T.delta : WithTop ℚ) ≤
        (T.Zn + 2 * r ^ 2 * T.Xn +
          GCD369CubeHahnRegular.monomial (T.delta / 2)
            (div_nonneg T.hdelta.le (by norm_num)) * r * B).1.orderTop) : False := by
  let M : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial (T.delta / 2)
      (div_nonneg T.hdelta.le (by norm_num))
  let Ydev : GCD369CubeHahnRegular k := T.Yn - r * T.Xn
  let B : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift Ydev (T.delta / 2) hB
  have hBfact : M * B = Ydev := by
    exact GCD369CubeHahnRegular.monomial_mul_shift
      Ydev (T.delta / 2)
        (div_nonneg T.hdelta.le (by norm_num)) hB
  have hY : T.Yn = r * T.Xn + M * B := by
    dsimp only [Ydev] at hBfact
    linear_combination -hBfact
  exact T.doubleRoot_source_inconsistent_of_orderBounds
    r0 A0 r B hr0 hA0 hp hr hx hX hroot hD
    (by simpa only [M] using hY) (by simpa only [B, M] using hZ)

/-- Canonical moving-root form of the preceding theorem.  A double-root
residue makes `cubicU` a unit, so the exact moving root and its relation are
constructed internally. -/
theorem TransverseFactor.doubleRoot_source_inconsistent_of_canonicalBounds
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r0 A0 : k) (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hp : 3 * T.delta ≤ S.normal.sextic.scale.p)
    (hu : GCD369CubeHahnRegular.constantCoeff S.cubicU = -3 * r0 ^ 2)
    (hv : GCD369CubeHahnRegular.constantCoeff S.cubicV = 2 * r0 ^ 3)
    (hx : GCD369CubeHahnRegular.constantCoeff
      S.normal.sextic.regularX = r0)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hD :
      let hUne : GCD369CubeHahnRegular.constantCoeff S.cubicU ≠ 0 := by
        rw [hu]
        exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hr0)
      let r := GCD369CubeHahnRegular.movingDoubleRoot
        S.cubicU S.cubicV hUne
      (↑T.delta : WithTop ℚ) ≤
        (S.cubicU + 3 * r ^ 2).1.orderTop)
    (hB :
      let hUne : GCD369CubeHahnRegular.constantCoeff S.cubicU ≠ 0 := by
        rw [hu]
        exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hr0)
      let r := GCD369CubeHahnRegular.movingDoubleRoot
        S.cubicU S.cubicV hUne
      (↑(T.delta / 2) : WithTop ℚ) ≤
        (T.Yn - r * T.Xn).1.orderTop)
    (hZ :
      let hUne : GCD369CubeHahnRegular.constantCoeff S.cubicU ≠ 0 := by
        rw [hu]
        exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hr0)
      let r := GCD369CubeHahnRegular.movingDoubleRoot
        S.cubicU S.cubicV hUne
      let B := GCD369CubeHahnRegular.shift
        (T.Yn - r * T.Xn) (T.delta / 2) hB
      (↑T.delta : WithTop ℚ) ≤
        (T.Zn + 2 * r ^ 2 * T.Xn +
          GCD369CubeHahnRegular.monomial (T.delta / 2)
            (div_nonneg T.hdelta.le (by norm_num)) * r * B).1.orderTop) : False := by
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
  exact T.doubleRoot_source_inconsistent_of_deviationBounds
    r0 A0 r hr0 hA0 hp hr hx hX hroot hD hB hZ

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_source_inconsistent_of_orderBounds
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_source_inconsistent_of_deviationBounds
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_source_inconsistent_of_canonicalBounds
