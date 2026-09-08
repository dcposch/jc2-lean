import FiniteSimpleSourceChartAll
import FiniteDoubleLiftQuadratic

/-! # Source-driven simple-root order lift

The order-lift inside `doubleRoot_source_inconsistent_from_source`, through
the full-scale cubic remainder `hDfull` and the corrected transverse
remainder `hQfull`, does not use the double-root residue of the source
coordinate.  Reused on the remaining simple residue `-2 * r0`, it supplies
the canonical chart coordinates `d`, `e`, `B`, `C2` for the moving double
root, after which the already verified simple-root split concludes that the
displacement `w = regularX + 2 * r` is either zero or of order at least
`delta`.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- The literal source equations lift the three canonical moving-root
deviations from half-scale to a full `delta` bound on the cubic remainder
and the corrected second-order transverse remainder.  This is the
order-lift portion of `doubleRoot_source_inconsistent_from_source`,
stopping before its double-root chart contradiction. -/
theorem TransverseFactor.doubleRoot_deviations_order_delta_from_source
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 : k)
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
    (hp : 3 * T.delta ≤ F.scale.p)
    (r : GCD369CubeHahnRegular k) (r0 A0 : k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hu : GCD369CubeHahnRegular.constantCoeff S.cubicU = -3 * r0 ^ 2)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r0 * A0)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r0 ^ 2 * A0)
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0) :
    (↑T.delta : WithTop ℚ) ≤
        (S.cubicU + 3 * r ^ 2).1.orderTop ∧
      ∃ B : GCD369CubeHahnRegular k,
        T.Yn = r * T.Xn +
          GCD369CubeHahnRegular.monomial (T.delta / 2)
            (div_nonneg T.hdelta.le (by norm_num)) * B ∧
        (↑T.delta : WithTop ℚ) ≤
          (T.Zn + 2 * r ^ 2 * T.Xn +
            GCD369CubeHahnRegular.monomial (T.delta / 2)
              (div_nonneg T.hdelta.le (by norm_num)) * r * B).1.orderTop := by
  have hhalf := T.doubleRoot_deviations_order_half_lower F hscale
    D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4 hp
    r r0 A0 hr0 hA0 hr hu hX hY hZ hroot
  let mu : ℚ := T.delta / 2
  have hmu : 0 < mu := by dsimp only [mu]; linarith [T.hdelta]
  let M : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial mu hmu.le
  let D : GCD369CubeHahnRegular k := S.cubicU + 3 * r ^ 2
  let Bdev : GCD369CubeHahnRegular k := T.Yn - r * T.Xn
  let C : GCD369CubeHahnRegular k := T.Zn + 2 * r ^ 2 * T.Xn
  have hDhalf : (↑mu : WithTop ℚ) ≤ D.1.orderTop := by
    simpa only [mu, D] using hhalf.1
  have hBhalf : (↑mu : WithTop ℚ) ≤ Bdev.1.orderTop := by
    simpa only [mu, Bdev] using hhalf.2.1
  have hChalf : (↑mu : WithTop ℚ) ≤ C.1.orderTop := by
    simpa only [mu, C] using hhalf.2.2
  let Dn : GCD369CubeHahnRegular k := GCD369CubeHahnRegular.shift D mu hDhalf
  let Bn : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift Bdev mu hBhalf
  let Cn : GCD369CubeHahnRegular k := GCD369CubeHahnRegular.shift C mu hChalf
  have hDfact : M * Dn = D := by
    simpa only [M, Dn] using GCD369CubeHahnRegular.monomial_mul_shift
      D mu hmu.le hDhalf
  have hBfact : M * Bn = Bdev := by
    simpa only [M, Bn] using GCD369CubeHahnRegular.monomial_mul_shift
      Bdev mu hmu.le hBhalf
  have hCfact : M * Cn = C := by
    simpa only [M, Cn] using GCD369CubeHahnRegular.monomial_mul_shift
      C mu hmu.le hChalf
  let Qn : GCD369CubeHahnRegular k := Cn + r * Bn
  let Row1 : GCD369CubeHahnRegular k :=
    T.Xn ^ 2 * D - 2 * T.Xn * Bdev * r - Bdev ^ 2 - 2 * T.Xn * C
  let Row2 : GCD369CubeHahnRegular k :=
    2 * T.Xn ^ 2 * r * D - 3 * T.Xn * Bdev * r ^ 2 - 3 * T.Xn * C * r +
      3 * T.Xn * Bdev * D - 3 * Bdev * C
  have hRow1 : (↑T.delta : WithTop ℚ) ≤ Row1.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro q hq
    have hq' : q < T.delta := WithTop.coe_lt_coe.mp hq
    by_cases hq0 : 0 ≤ q
    · have hrows := T.doubleRoot_rowCoeffs_zero_before_d F hscale
        D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
        hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
        r hroot q hq0 hq' (by linarith [hp])
      simpa only [Row1, D, Bdev, C] using hrows.1
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg Row1
        (lt_of_not_ge hq0)
  have hRow2 : (↑T.delta : WithTop ℚ) ≤ Row2.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro q hq
    have hq' : q < T.delta := WithTop.coe_lt_coe.mp hq
    by_cases hq0 : 0 ≤ q
    · have hrows := T.doubleRoot_rowCoeffs_zero_before_d F hscale
        D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
        hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
        r hroot q hq0 hq' (by linarith [hp])
      simpa only [Row2, D, Bdev, C] using hrows.2.1
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg Row2
        (lt_of_not_ge hq0)
  let FRow1 : GCD369CubeHahnRegular k :=
    M * (T.Xn ^ 2 * Dn - 2 * T.Xn * Qn) - M ^ 2 * Bn ^ 2
  let FRow2 : GCD369CubeHahnRegular k :=
    M * (2 * T.Xn ^ 2 * r * Dn - 3 * T.Xn * r * Qn) +
      M ^ 2 * (3 * T.Xn * Bn * Dn - 3 * Bn * Cn)
  have hfac1 : Row1 = FRow1 := by
    dsimp only [Row1, FRow1, Qn]
    rw [← hDfact, ← hBfact, ← hCfact]
    ring
  have hfac2 : Row2 = FRow2 := by
    dsimp only [Row2, FRow2, Qn]
    rw [← hDfact, ← hBfact, ← hCfact]
    ring
  have hFRow1 : (↑(2 * mu) : WithTop ℚ) ≤ FRow1.1.orderTop := by
    have ht : (2 * mu : ℚ) = T.delta := by dsimp only [mu]; ring
    rw [ht]
    exact hRow1.trans_eq (congrArg (fun z : GCD369CubeHahnRegular k =>
      z.1.orderTop) hfac1)
  have hFRow2 : (↑(2 * mu) : WithTop ℚ) ≤ FRow2.1.orderTop := by
    have ht : (2 * mu : ℚ) = T.delta := by dsimp only [mu]; ring
    rw [ht]
    exact hRow2.trans_eq (congrArg (fun z : GCD369CubeHahnRegular k =>
      z.1.orderTop) hfac2)
  have hlift :=
    GCD369CubeHahnRegular.doubleBlowup_kernelRemainders_order_lower_of_factoredRows
      mu hmu T.Xn r Dn Bn Cn (by rw [hX]; exact hA0)
      (by rw [hr]; exact hr0)
      (by simpa only [FRow1, M, Qn] using hFRow1)
      (by simpa only [FRow2, M, Qn] using hFRow2)
  have hMorder : (↑mu : WithTop ℚ) ≤ M.1.orderTop := by
    exact (GCD369CubeHahnRegular.monomial_orderTop_and_leadingCoeff
      mu hmu.le).1.ge
  have hDfull0 := GCD369CubeHahnRegular.mul_orderTop_lower
    M Dn mu mu hMorder hlift.1
  have hDfull : (↑T.delta : WithTop ℚ) ≤ D.1.orderTop := by
    have ht : mu + mu = T.delta := by dsimp only [mu]; ring
    rw [ht] at hDfull0
    exact hDfull0.trans_eq (congrArg (fun z : GCD369CubeHahnRegular k =>
      z.1.orderTop) hDfact)
  have hQfull0 := GCD369CubeHahnRegular.mul_orderTop_lower
    M Qn mu mu hMorder hlift.2
  have hcorrected : C + M * r * Bn = M * Qn := by
    dsimp only [Qn]
    rw [← hCfact]
    ring
  have hQfull : (↑T.delta : WithTop ℚ) ≤
      (C + M * r * Bn).1.orderTop := by
    have ht : mu + mu = T.delta := by dsimp only [mu]; ring
    rw [ht] at hQfull0
    exact hQfull0.trans_eq (congrArg (fun z : GCD369CubeHahnRegular k =>
      z.1.orderTop) hcorrected.symm)
  have hYcoord : T.Yn = r * T.Xn + M * Bn := by
    dsimp only [Bdev] at hBfact
    linear_combination -hBfact
  refine ⟨by simpa only [D] using hDfull, ⟨Bn, ?_, ?_⟩⟩
  · simpa only [M, mu] using hYcoord
  · simpa only [C, M, mu] using hQfull

/-- A moving cubic relation, a half-scale transverse kernel correction, and
two `delta`-order remainder bounds realize the simple-root chart for
`p ≥ 3 * delta`.  The displacement from `-2 * r` is then either identically
zero or of Hahn order at least `delta`. -/
theorem TransverseFactor.simpleRoot_source_zero_or_order_delta_of_orderBounds
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r0 A0 : k) (r B : GCD369CubeHahnRegular k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hp : 3 * T.delta ≤ S.normal.sextic.scale.p)
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
  exact T.simpleRoot_source_zero_or_order_delta_of_coordinates
    r0 A0 r w d e B 0 C2 hr0 hA0 hp hr hX hw0 hxcoord
    (by simpa only [H] using hU) (by simpa only [H] using hV) hre
    (by simpa only [M, H, mul_zero, add_zero] using hY)
    (by simpa only [M, H] using hZcoord)

/-- If `p ≥ 3 * delta` and the recovered source residue is the remaining
simple root `-2 * r0` of the singular leading cubic, the canonical moving
double root and the literal finite source produce simple-root chart
coordinates in which the displacement is either zero or of order at least
`delta`. -/
theorem TransverseFactor.simpleRoot_source_zero_or_order_delta_from_source
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 : k)
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
    (hp : 3 * T.delta ≤ F.scale.p)
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
    T.doubleRoot_deviations_order_delta_from_source F hscale
      D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4 hp
      r r0 A0 hr0 hA0 hr hu hX hY hZ hroot
  have hpS : 3 * T.delta ≤ S.normal.sextic.scale.p := by
    rw [hscale]
    exact hp
  exact T.simpleRoot_source_zero_or_order_delta_of_orderBounds
    r0 A0 r B hr0 hA0 hpS hr hx hX hroot hDfull hYcoord hQfull

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_deviations_order_delta_from_source
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.simpleRoot_source_zero_or_order_delta_of_orderBounds
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.simpleRoot_source_zero_or_order_delta_from_source
