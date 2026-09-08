import LowScale46PoleBridge

/-! # Regular-load finite-pole exclusions for the `(4,6)` chart

The finite-pole Newton arguments only use that the two boundary loads are
regular.  This module upgrades the scalar-load mismatch exclusions to
arbitrary Hahn-series loads of nonnegative order, as supplied by translated
coefficient polynomials.
-/

noncomputable section

namespace Max11DegreeRoutes

section RegularMismatchLoads

variable {k : Type*} [Field k]

/-- A regular load multiplied by `s^n` lies above every exponent below `n`
when `s` has order one. -/
theorem regularLoad_mul_pow_orderTop_gt46
    (D s : HahnSeries ℚ k) (n : ℕ) (e : ℚ)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (he : e < (n : ℚ)) :
    (↑e : WithTop ℚ) < ((-D) * s ^ n).orderTop := by
  have hsN : (s ^ n).orderTop = (↑(n : ℚ) : WithTop ℚ) := by
    simpa using hahnOrderTop_pow_eq46 s 1 n hs
  rw [HahnSeries.orderTop_mul, HahnSeries.orderTop_neg, hsN]
  exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr he)
    (by simpa [add_comm] using
      add_le_add_right hD (↑(n : ℚ) : WithTop ℚ))

/-- Exact mismatch-face decomposition with an arbitrary boundary load. -/
theorem localChartF46_eq_mismatch_faces_regular
    (D s Q Y Z : HahnSeries ℚ k) :
    localChartF46 s Q Y Z D =
      Y + Q ^ 2 + HahnSeries.C (-1 / 4 : k) * Z +
        (-D) * s ^ 4 := by
  simp only [localChartF46]
  simp only [map_div₀, map_neg, map_ofNat, map_one]
  ring

/-- With a regular first boundary load, the `Q=0` face still forces equal
orders for `Y` and `Z`. -/
theorem mismatchF46_forces_equal_orders_of_Q_eq_zero_regular
    [CharZero k]
    (D : HahnSeries ℚ k) (s Q Y Z : HahnSeries ℚ k) (b c : ℚ)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (hb : 0 < b) (hc : 0 < c) (hbc : b + c = 1)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ))
    (hZ : Z.orderTop = (↑c : WithTop ℚ))
    (hQzero : Q = 0)
    (hF : localChartF46 s Q Y Z D = 0) :
    b = c := by
  let zterm : HahnSeries ℚ k := HahnSeries.C (-1 / 4 : k) * Z
  let dterm : HahnSeries ℚ k := (-D) * s ^ 4
  have hzterm : zterm.orderTop = (↑c : WithTop ℚ) := by
    dsimp [zterm]
    exact hahnOrderTop_C_mul_eq46 _ _ c (by norm_num) hZ
  have hsum : Y + zterm + dterm = 0 := by
    have hfull : Y + Q ^ 2 + HahnSeries.C (-1 / 4 : k) * Z +
        (-D) * s ^ 4 = 0 := by
      rw [← localChartF46_eq_mismatch_faces_regular D s Q Y Z]
      exact hF
    simpa [hQzero, zterm, dterm] using hfull
  by_contra hne
  rcases lt_or_gt_of_ne hne with hblt | hclt
  · have hz0 : zterm.coeff b = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_orderTop (by
        rw [hzterm]
        exact WithTop.coe_lt_coe.mpr hblt)
    have hdHigh := regularLoad_mul_pow_orderTop_gt46 D s 4 b hD hs
      (by norm_num; linarith)
    have hd0 : dterm.coeff b = 0 := by
      apply HahnSeries.coeff_eq_zero_of_lt_orderTop
      simpa [dterm] using hdHigh
    have hcoeff := congrArg (fun z : HahnSeries ℚ k => z.coeff b) hsum
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hz0, hd0,
      add_zero] at hcoeff
    exact HahnSeries.coeff_orderTop_ne hY hcoeff
  · have hY0 : Y.coeff c = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_orderTop (by
        rw [hY]
        exact WithTop.coe_lt_coe.mpr hclt)
    have hdHigh := regularLoad_mul_pow_orderTop_gt46 D s 4 c hD hs
      (by norm_num; linarith)
    have hd0 : dterm.coeff c = 0 := by
      apply HahnSeries.coeff_eq_zero_of_lt_orderTop
      simpa [dterm] using hdHigh
    have hcoeff := congrArg (fun z : HahnSeries ℚ k => z.coeff c) hsum
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hY0, hd0,
      zero_add, add_zero] at hcoeff
    exact HahnSeries.coeff_orderTop_ne hzterm hcoeff

/-- Regular order-four loads do not affect the argument forcing the
quarter-order `Q` face. -/
theorem mismatchF46_forces_Q_order_quarter_regular
    [CharZero k]
    (L beta gamma delta k1 : k) (D : HahnSeries ℚ k)
    (s Q Y Z : HahnSeries ℚ k) (a : ℚ) (ha : 0 < a)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑(1 / 2 : ℚ) : WithTop ℚ))
    (hZ : Z.orderTop = (↑(1 / 2 : ℚ) : WithTop ℚ))
    (hF : localChartF46 s Q Y Z D = 0)
    (hJ1 : localChartJOne46 (HahnSeries.C L) s Q Y Z
      (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C k1) = 0) :
    a = 1 / 4 := by
  have hQ2 := hahnOrderTop_pow_eq46 Q a 2 hQ
  have hY2 := hahnOrderTop_pow_eq46 Y (1 / 2) 2 hY
  have hZ2 := hahnOrderTop_pow_eq46 Z (1 / 2) 2 hZ
  norm_num at hQ2 hY2 hZ2
  have hQ2coe : (Q ^ 2).orderTop = (↑(2 * a) : WithTop ℚ) := by
    rw [hQ2, WithTop.coe_mul]
    norm_num
  have hFsum : Y + Q ^ 2 + HahnSeries.C (-1 / 4 : k) * Z +
      (-D) * s ^ 4 = 0 := by
    rw [← localChartF46_eq_mismatch_faces_regular D s Q Y Z]
    exact hF
  by_cases hbelow : 2 * a < 1 / 2
  · have hY0 : Y.coeff (2 * a) = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_orderTop (by
        rw [hY]
        exact WithTop.coe_lt_coe.mpr hbelow)
    have hZ0 : Z.coeff (2 * a) = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_orderTop (by
        rw [hZ]
        exact WithTop.coe_lt_coe.mpr hbelow)
    have hZterm0 :
        (HahnSeries.C (-1 / 4 : k) * Z).coeff (2 * a) = 0 := by
      rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul, hZ0, mul_zero]
    have hdHigh := regularLoad_mul_pow_orderTop_gt46 D s 4 (2 * a) hD hs
      (by norm_num; linarith)
    have hd0 : ((-D) * s ^ 4).coeff (2 * a) = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_orderTop hdHigh
    have hcoeff := congrArg (fun z : HahnSeries ℚ k => z.coeff (2 * a)) hFsum
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hY0, hZterm0,
      hd0, zero_add, add_zero] at hcoeff
    exact (HahnSeries.coeff_orderTop_ne hQ2coe hcoeff).elim
  · by_cases habove : 1 / 2 < 2 * a
    · have hQ0 : (Q ^ 2).coeff (1 / 2) = 0 :=
        HahnSeries.coeff_eq_zero_of_lt_orderTop (by
          rw [hQ2]
          exact WithTop.coe_lt_coe.mpr habove)
      have hdHigh := regularLoad_mul_pow_orderTop_gt46 D s 4 (1 / 2) hD hs
        (by norm_num)
      have hd0 : ((-D) * s ^ 4).coeff (1 / 2) = 0 :=
        HahnSeries.coeff_eq_zero_of_lt_orderTop hdHigh
      have hcoeffF :=
        congrArg (fun z : HahnSeries ℚ k => z.coeff (1 / 2)) hFsum
      have hYcoeff :=
        hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 Y (1 / 2) hY
      have hZcoeff :=
        hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 Z (1 / 2) hZ
      have hZterm : (HahnSeries.C (-1 / 4 : k) * Z).coeff (1 / 2) =
          (-1 / 4 : k) * Z.leadingCoeff := by
        rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul, hZcoeff]
      simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hQ0, hZterm,
        hd0, add_zero] at hcoeffF
      rw [hYcoeff] at hcoeffF
      have hFlead : Y.leadingCoeff -
          (1 / 4 : k) * Z.leadingCoeff = 0 := by
        linear_combination hcoeffF
      let p : HahnSeries ℚ k := HahnSeries.C (3 / 2 : k) * Y ^ 2
      let q : HahnSeries ℚ k := HahnSeries.C (3 / 32 : k) * Z ^ 2
      let r := mismatchJOneHigher46 L beta gamma delta k1 s Q Y Z
      have hJ1sum : p + q + r = 0 := by
        rw [← localChartJOne46_eq_mismatch_faces L beta gamma delta k1
          s Q Y Z]
        exact hJ1
      have hr := mismatchJOneHigher46_order_gt_min
        L beta gamma delta k1 s Q Y Z a (1 / 2) (1 / 2)
        ha (by norm_num) (by norm_num) (by norm_num) hs hQ hY hZ
      have hr1 : (↑(1 : ℚ) : WithTop ℚ) < r.orderTop := by
        simpa using hr
      have hr0 : r.coeff 1 = 0 :=
        HahnSeries.coeff_eq_zero_of_lt_orderTop hr1
      have hcoeffJ1 := congrArg (fun z : HahnSeries ℚ k => z.coeff 1) hJ1sum
      simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hr0,
        add_zero] at hcoeffJ1
      have hY2one : (Y ^ 2).orderTop = (↑(1 : ℚ) : WithTop ℚ) := by
        simpa using hY2
      have hZ2one : (Z ^ 2).orderTop = (↑(1 : ℚ) : WithTop ℚ) := by
        simpa using hZ2
      have hY2coeff : (Y ^ 2).coeff 1 = Y.leadingCoeff ^ 2 := by
        rw [hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 (Y ^ 2) 1 hY2one]
        simp [pow_two, HahnSeries.leadingCoeff_mul]
      have hZ2coeff : (Z ^ 2).coeff 1 = Z.leadingCoeff ^ 2 := by
        rw [hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 (Z ^ 2) 1 hZ2one]
        simp [pow_two, HahnSeries.leadingCoeff_mul]
      dsimp [p, q] at hcoeffJ1
      simp only [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul,
        hY2coeff, hZ2coeff] at hcoeffJ1
      have hJ1lead : (3 / 2 : k) * Y.leadingCoeff ^ 2 +
          (3 / 32 : k) * Z.leadingCoeff ^ 2 = 0 := hcoeffJ1
      have hYlead : Y.leadingCoeff ≠ 0 := by
        rw [← hYcoeff]
        exact HahnSeries.coeff_orderTop_ne hY
      exact (mismatchQAboveFace_inconsistent46 Y.leadingCoeff Z.leadingCoeff
        hYlead hFlead hJ1lead).elim
    · linarith

/-- The scalar-free part of the mismatch `G` remainder, plus an arbitrary
regular order-six load. -/
def mismatchGHigherRegular46
    (L beta gamma delta : k) (E : HahnSeries ℚ k)
    (s Q Y Z : HahnSeries ℚ k) : HahnSeries ℚ k :=
  mismatchGHigher46 L beta gamma delta 0 s Q Y Z + (-E) * s ^ 6

/-- Exact terminal-face decomposition of `G` for an arbitrary load. -/
theorem localChartG46_eq_mismatch_faces_regular
    (L beta gamma delta : k) (E : HahnSeries ℚ k)
    (s Q Y Z : HahnSeries ℚ k) :
    localChartG46 (HahnSeries.C L) s Q Y Z
        (HahnSeries.C beta) (HahnSeries.C gamma)
        (HahnSeries.C delta) E =
      Q ^ 3 + HahnSeries.C (3 / 2 : k) * (Q * Y) +
        HahnSeries.C (-3 / 8 : k) * (Q * Z) +
        mismatchGHigherRegular46 L beta gamma delta E s Q Y Z := by
  simp only [localChartG46, mismatchGHigherRegular46, mismatchGHigher46]
  simp only [map_mul, map_div₀, map_neg, map_ofNat, map_one,
    HahnSeries.C_zero]
  ring

/-- A regular order-six load remains above the terminal `3/4` face. -/
theorem mismatchGHigherRegular46_order_gt_three_quarters
    (L beta gamma delta : k) (E : HahnSeries ℚ k)
    (s Q Y Z : HahnSeries ℚ k)
    (hE : (0 : WithTop ℚ) ≤ E.orderTop)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑(1 / 4 : ℚ) : WithTop ℚ))
    (hY : Y.orderTop = (↑(1 / 2 : ℚ) : WithTop ℚ))
    (hZ : Z.orderTop = (↑(1 / 2 : ℚ) : WithTop ℚ)) :
    (↑(3 / 4 : ℚ) : WithTop ℚ) <
      (mismatchGHigherRegular46 L beta gamma delta E s Q Y Z).orderTop := by
  have hbase := mismatchGHigher46_order_gt_three_quarters
    L beta gamma delta 0 s Q Y Z hs hQ hY hZ
  have hload := regularLoad_mul_pow_orderTop_gt46 E s 6 (3 / 4) hE hs
    (by norm_num)
  exact hahnOrderTop_add_gt46 (3 / 4) _ _ hbase hload

/-- The terminal `G` leading equation is unchanged by an arbitrary regular
boundary load. -/
theorem mismatchG46_leading_equation_regular
    [CharZero k]
    (L beta gamma delta : k) (E : HahnSeries ℚ k)
    (s Q Y Z : HahnSeries ℚ k)
    (hE : (0 : WithTop ℚ) ≤ E.orderTop)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑(1 / 4 : ℚ) : WithTop ℚ))
    (hY : Y.orderTop = (↑(1 / 2 : ℚ) : WithTop ℚ))
    (hZ : Z.orderTop = (↑(1 / 2 : ℚ) : WithTop ℚ))
    (hG : localChartG46 (HahnSeries.C L) s Q Y Z
      (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) E = 0) :
    Q.leadingCoeff *
      (Q.leadingCoeff ^ 2 + (3 / 2 : k) * Y.leadingCoeff -
        (3 / 8 : k) * Z.leadingCoeff) = 0 := by
  let r := mismatchGHigherRegular46 L beta gamma delta E s Q Y Z
  have hsum : Q ^ 3 + HahnSeries.C (3 / 2 : k) * (Q * Y) +
      HahnSeries.C (-3 / 8 : k) * (Q * Z) + r = 0 := by
    rw [← localChartG46_eq_mismatch_faces_regular
      L beta gamma delta E s Q Y Z]
    exact hG
  have hr := mismatchGHigherRegular46_order_gt_three_quarters
    L beta gamma delta E s Q Y Z hE hs hQ hY hZ
  have hr0 : r.coeff (3 / 4) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop hr
  have hQ3 := hahnOrderTop_pow_eq46 Q (1 / 4) 3 hQ
  have hQY := hahnOrderTop_mul_eq46 Q Y (1 / 4) (1 / 2) hQ hY
  have hQZ := hahnOrderTop_mul_eq46 Q Z (1 / 4) (1 / 2) hQ hZ
  have hQ3order : (Q ^ 3).orderTop =
      (↑(3 / 4 : ℚ) : WithTop ℚ) := by
    calc
      (Q ^ 3).orderTop =
          (↑((3 : ℚ) * (1 / 4)) : WithTop ℚ) := hQ3
      _ = _ := by norm_num
  have hQYorder : (Q * Y).orderTop =
      (↑(3 / 4 : ℚ) : WithTop ℚ) := by
    calc
      (Q * Y).orderTop =
          (↑((1 / 4 : ℚ) + 1 / 2) : WithTop ℚ) := hQY
      _ = _ := by norm_num
  have hQZorder : (Q * Z).orderTop =
      (↑(3 / 4 : ℚ) : WithTop ℚ) := by
    calc
      (Q * Z).orderTop =
          (↑((1 / 4 : ℚ) + 1 / 2) : WithTop ℚ) := hQZ
      _ = _ := by norm_num
  have hQ3coeff : (Q ^ 3).coeff (3 / 4) = Q.leadingCoeff ^ 3 := by
    rw [hahnCoeff_eq_leadingCoeff_of_orderTop_eq46
      (Q ^ 3) (3 / 4) hQ3order]
    simp [pow_succ, HahnSeries.leadingCoeff_mul]
  have hQYcoeff : (Q * Y).coeff (3 / 4) =
      Q.leadingCoeff * Y.leadingCoeff := by
    rw [hahnCoeff_eq_leadingCoeff_of_orderTop_eq46
      (Q * Y) (3 / 4) hQYorder, HahnSeries.leadingCoeff_mul]
  have hQZcoeff : (Q * Z).coeff (3 / 4) =
      Q.leadingCoeff * Z.leadingCoeff := by
    rw [hahnCoeff_eq_leadingCoeff_of_orderTop_eq46
      (Q * Z) (3 / 4) hQZorder, HahnSeries.leadingCoeff_mul]
  have hcoeff :=
    congrArg (fun z : HahnSeries ℚ k => z.coeff (3 / 4)) hsum
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero,
    HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul,
    hQ3coeff, hQYcoeff, hQZcoeff, hr0, add_zero] at hcoeff
  linear_combination hcoeff

/-- The terminal `F` leading equation is unchanged by an arbitrary regular
boundary load. -/
theorem mismatchF46_leading_equation_regular
    [CharZero k]
    (D : HahnSeries ℚ k) (s Q Y Z : HahnSeries ℚ k)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑(1 / 4 : ℚ) : WithTop ℚ))
    (hY : Y.orderTop = (↑(1 / 2 : ℚ) : WithTop ℚ))
    (hZ : Z.orderTop = (↑(1 / 2 : ℚ) : WithTop ℚ))
    (hF : localChartF46 s Q Y Z D = 0) :
    Y.leadingCoeff + Q.leadingCoeff ^ 2 -
      (1 / 4 : k) * Z.leadingCoeff = 0 := by
  have hsum : Y + Q ^ 2 + HahnSeries.C (-1 / 4 : k) * Z +
      (-D) * s ^ 4 = 0 := by
    rw [← localChartF46_eq_mismatch_faces_regular D s Q Y Z]
    exact hF
  have hdHigh := regularLoad_mul_pow_orderTop_gt46 D s 4 (1 / 2) hD hs
    (by norm_num)
  have hd0 : ((-D) * s ^ 4).coeff (1 / 2) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop hdHigh
  have hQ2 := hahnOrderTop_pow_eq46 Q (1 / 4) 2 hQ
  have hQ2order : (Q ^ 2).orderTop =
      (↑(1 / 2 : ℚ) : WithTop ℚ) := by
    calc
      (Q ^ 2).orderTop =
          (↑((2 : ℚ) * (1 / 4)) : WithTop ℚ) := hQ2
      _ = _ := by norm_num
  have hYcoeff :=
    hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 Y (1 / 2) hY
  have hZcoeff :=
    hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 Z (1 / 2) hZ
  have hQ2coeff : (Q ^ 2).coeff (1 / 2) = Q.leadingCoeff ^ 2 := by
    rw [hahnCoeff_eq_leadingCoeff_of_orderTop_eq46
      (Q ^ 2) (1 / 2) hQ2order]
    simp [pow_two, HahnSeries.leadingCoeff_mul]
  have hZterm : (HahnSeries.C (-1 / 4 : k) * Z).coeff (1 / 2) =
      (-1 / 4 : k) * Z.leadingCoeff := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul, hZcoeff]
  have hcoeff :=
    congrArg (fun z : HahnSeries ℚ k => z.coeff (1 / 2)) hsum
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hYcoeff,
    hQ2coeff, hZterm, hd0, add_zero] at hcoeff
  linear_combination hcoeff

/-- The degenerate mismatch face `Q=0` is impossible with any regular first
boundary load. -/
theorem mismatchQZeroFinitePole46_impossible_regular
    [CharZero k]
    (L beta gamma delta : k) (D : HahnSeries ℚ k) (k2 k1 : k)
    (s Q Y Z : HahnSeries ℚ k) (b c : ℚ)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (hb : 0 < b) (hc : 0 < c) (hL : L ≠ 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ))
    (hZ : Z.orderTop = (↑c : WithTop ℚ))
    (hQzero : Q = 0)
    (hF : localChartF46 s Q Y Z D = 0)
    (hJ2 : localChartJTwo46 (HahnSeries.C L) s Q Y Z
      (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C k2) = 0)
    (hJ1 : localChartJOne46 (HahnSeries.C L) s Q Y Z
      (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C k1) = 0) : False := by
  have hQpos : (↑(0 : ℚ) : WithTop ℚ) < Q.orderTop := by
    simp [hQzero]
  have hbc := mismatchJTwo46_forces_order_sum_of_positiveQ
    L beta gamma delta k2 s Q Y Z b c hb hc hL hs hQpos hY hZ hJ2
  have hbeq := mismatchF46_forces_equal_orders_of_Q_eq_zero_regular
    D s Q Y Z b c hD hb hc hbc hs hY hZ hQzero hF
  obtain ⟨hbhalf, hchalf⟩ := mismatchOrders46 b c hbc hbeq
  have hYhalf : Y.orderTop = (↑(1 / 2 : ℚ) : WithTop ℚ) := by
    rw [hY, hbhalf]
  have hZhalf : Z.orderTop = (↑(1 / 2 : ℚ) : WithTop ℚ) := by
    rw [hZ, hchalf]
  have hFsum : Y + HahnSeries.C (-1 / 4 : k) * Z +
      (-D) * s ^ 4 = 0 := by
    have hfull : Y + Q ^ 2 + HahnSeries.C (-1 / 4 : k) * Z +
        (-D) * s ^ 4 = 0 := by
      rw [← localChartF46_eq_mismatch_faces_regular D s Q Y Z]
      exact hF
    simpa [hQzero] using hfull
  have hdHigh := regularLoad_mul_pow_orderTop_gt46 D s 4 (1 / 2) hD hs
    (by norm_num)
  have hd0 : ((-D) * s ^ 4).coeff (1 / 2) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop hdHigh
  have hYcoeff :=
    hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 Y (1 / 2) hYhalf
  have hZcoeff :=
    hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 Z (1 / 2) hZhalf
  have hZterm : (HahnSeries.C (-1 / 4 : k) * Z).coeff (1 / 2) =
      (-1 / 4 : k) * Z.leadingCoeff := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul, hZcoeff]
  have hFcoeff :=
    congrArg (fun z : HahnSeries ℚ k => z.coeff (1 / 2)) hFsum
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_zero, hYcoeff,
    hZterm, hd0, add_zero] at hFcoeff
  have hFlead : Y.leadingCoeff - (1 / 4 : k) * Z.leadingCoeff = 0 := by
    linear_combination hFcoeff
  let p : HahnSeries ℚ k := HahnSeries.C (3 / 2 : k) * Y ^ 2
  let q : HahnSeries ℚ k := HahnSeries.C (3 / 32 : k) * Z ^ 2
  let r := mismatchJOneHigher46 L beta gamma delta k1 s Q Y Z
  have hJ1sum : p + q + r = 0 := by
    rw [← localChartJOne46_eq_mismatch_faces L beta gamma delta k1
      s Q Y Z]
    exact hJ1
  have hr := mismatchJOneHigher46_order_gt_one_of_Q_eq_zero
    L beta gamma delta k1 s Q Y Z hs hYhalf hZhalf hQzero
  have hr0 : r.coeff 1 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop hr
  have hY2 := hahnOrderTop_pow_eq46 Y (1 / 2) 2 hYhalf
  have hZ2 := hahnOrderTop_pow_eq46 Z (1 / 2) 2 hZhalf
  have hY2one : (Y ^ 2).orderTop = (↑(1 : ℚ) : WithTop ℚ) := by
    simpa using hY2
  have hZ2one : (Z ^ 2).orderTop = (↑(1 : ℚ) : WithTop ℚ) := by
    simpa using hZ2
  have hY2coeff : (Y ^ 2).coeff 1 = Y.leadingCoeff ^ 2 := by
    rw [hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 (Y ^ 2) 1 hY2one]
    simp [pow_two, HahnSeries.leadingCoeff_mul]
  have hZ2coeff : (Z ^ 2).coeff 1 = Z.leadingCoeff ^ 2 := by
    rw [hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 (Z ^ 2) 1 hZ2one]
    simp [pow_two, HahnSeries.leadingCoeff_mul]
  have hJ1coeff :=
    congrArg (fun z : HahnSeries ℚ k => z.coeff 1) hJ1sum
  dsimp [p, q] at hJ1coeff
  simp only [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul,
    hY2coeff, hZ2coeff, hr0, add_zero] at hJ1coeff
  have hJ1lead : (3 / 2 : k) * Y.leadingCoeff ^ 2 +
      (3 / 32 : k) * Z.leadingCoeff ^ 2 = 0 := hJ1coeff
  have hYlead : Y.leadingCoeff ≠ 0 := by
    rw [← hYcoeff]
    exact HahnSeries.coeff_orderTop_ne hYhalf
  exact mismatchQAboveFace_inconsistent46 Y.leadingCoeff Z.leadingCoeff
    hYlead hFlead hJ1lead

/-- Complete nondegenerate mismatch exclusion with arbitrary regular
boundary loads. -/
theorem mismatchFinitePole46_impossible_regular
    [CharZero k]
    (L beta gamma delta : k) (D E : HahnSeries ℚ k) (k2 k1 : k)
    (s Q Y Z : HahnSeries ℚ k) (a b c : ℚ)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (hE : (0 : WithTop ℚ) ≤ E.orderTop)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hL : L ≠ 0)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQ : Q.orderTop = (↑a : WithTop ℚ))
    (hY : Y.orderTop = (↑b : WithTop ℚ))
    (hZ : Z.orderTop = (↑c : WithTop ℚ))
    (hF : localChartF46 s Q Y Z D = 0)
    (hG : localChartG46 (HahnSeries.C L) s Q Y Z
      (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) E = 0)
    (hJ2 : localChartJTwo46 (HahnSeries.C L) s Q Y Z
      (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C k2) = 0)
    (hJ1 : localChartJOne46 (HahnSeries.C L) s Q Y Z
      (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C k1) = 0) : False := by
  have hbc := (mismatchJTwo46_forces_order_sum_and_coefficient
    L beta gamma delta k2 s Q Y Z a b c ha hb hc hL hs hQ hY hZ hJ2).1
  have hbeq := mismatchJOne46_forces_equal_orders
    L beta gamma delta k1 s Q Y Z a b c ha hb hc hbc hs hQ hY hZ hJ1
  obtain ⟨hbhalf, hchalf⟩ := mismatchOrders46 b c hbc hbeq
  have hYhalf : Y.orderTop = (↑(1 / 2 : ℚ) : WithTop ℚ) := by
    rw [hY, hbhalf]
  have hZhalf : Z.orderTop = (↑(1 / 2 : ℚ) : WithTop ℚ) := by
    rw [hZ, hchalf]
  have haquarter := mismatchF46_forces_Q_order_quarter_regular
    L beta gamma delta k1 D s Q Y Z a ha hD hs hQ hYhalf hZhalf hF hJ1
  have hQquarter : Q.orderTop = (↑(1 / 4 : ℚ) : WithTop ℚ) := by
    rw [hQ, haquarter]
  have hFlead := mismatchF46_leading_equation_regular
    D s Q Y Z hD hs hQquarter hYhalf hZhalf hF
  have hGlead := mismatchG46_leading_equation_regular
    L beta gamma delta E s Q Y Z hE hs hQquarter hYhalf hZhalf hG
  have hQcoeff :=
    hahnCoeff_eq_leadingCoeff_of_orderTop_eq46 Q (1 / 4) hQquarter
  have hQlead : Q.leadingCoeff ≠ 0 := by
    rw [← hQcoeff]
    exact HahnSeries.coeff_orderTop_ne hQquarter
  exact mismatchLeadingSystem46_inconsistent Q.leadingCoeff Y.leadingCoeff
    Z.leadingCoeff hQlead hFlead hGlead

/-- Exhaustive mismatch exclusion with arbitrary regular boundary loads. -/
theorem mismatchFinitePole46_exhaustive_regular
    [CharZero k]
    (L beta gamma delta : k) (D E : HahnSeries ℚ k) (k2 k1 : k)
    (s Q Y Z : HahnSeries ℚ k) (hL : L ≠ 0)
    (hD : (0 : WithTop ℚ) ≤ D.orderTop)
    (hE : (0 : WithTop ℚ) ≤ E.orderTop)
    (hs : s.orderTop = (↑(1 : ℚ) : WithTop ℚ))
    (hQcase : PositiveFiniteOrZero46 Q)
    (hYcase : PositiveFiniteOrZero46 Y)
    (hZcase : PositiveFiniteOrZero46 Z)
    (hF : localChartF46 s Q Y Z D = 0)
    (hG : localChartG46 (HahnSeries.C L) s Q Y Z
      (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) E = 0)
    (hJ2 : localChartJTwo46 (HahnSeries.C L) s Q Y Z
      (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C k2) = 0)
    (hJ1 : localChartJOne46 (HahnSeries.C L) s Q Y Z
      (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C k1) = 0) : False := by
  have hQpos := orderTop_pos_of_positiveFiniteOrZero46 Q hQcase
  have hYpos := orderTop_pos_of_positiveFiniteOrZero46 Y hYcase
  have hZpos := orderTop_pos_of_positiveFiniteOrZero46 Z hZcase
  rcases hYcase with hYzero | ⟨b, hb, hY⟩
  · exact mismatchJTwo46_impossible_of_YZ_eq_zero
      L beta gamma delta k2 s Q Y Z hL hs hQpos hYpos hZpos
      (by simp [hYzero]) hJ2
  rcases hZcase with hZzero | ⟨c, hc, hZ⟩
  · exact mismatchJTwo46_impossible_of_YZ_eq_zero
      L beta gamma delta k2 s Q Y Z hL hs hQpos hYpos hZpos
      (by simp [hZzero]) hJ2
  rcases hQcase with hQzero | ⟨a, ha, hQ⟩
  · exact mismatchQZeroFinitePole46_impossible_regular
      L beta gamma delta D k2 k1 s Q Y Z b c hD hb hc hL hs hY hZ
      hQzero hF hJ2 hJ1
  · exact mismatchFinitePole46_impossible_regular
      L beta gamma delta D E k2 k1 s Q Y Z a b c hD hE ha hb hc hL
      hs hQ hY hZ hF hG hJ2 hJ1

end RegularMismatchLoads

end Max11DegreeRoutes
