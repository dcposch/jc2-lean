import LowScale68ScaleTwoAlignedSquareRhoOneCubicExceptionalDiscriminant

/-! # The next homogeneous exceptional face -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareRhoOneCubicExceptionalHomogeneousNext68

variable {k : Type*} [Field k] [CharZero k]

local instance exceptionalHomogeneousNextLaurentCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

/-- Killing the coefficient at an integral lower bound improves that bound by
one for a Laurent series. -/
theorem laurent_orderTop_ge_succ_of_coeff_zero68
    (X : LaurentSeries k) (n : ℤ)
    (hord : (↑n : WithTop ℤ) ≤ X.orderTop)
    (hcoeff : X.coeff n = 0) :
    (↑(n + 1) : WithTop ℤ) ≤ X.orderTop := by
  by_cases hX : X = 0
  · simp [hX]
  rw [← HahnSeries.order_eq_orderTop_of_ne_zero hX] at hord ⊢
  simp only [WithTop.coe_le_coe] at hord ⊢
  have hne : n ≠ X.order := by
    intro hn
    apply HahnSeries.orderTop_ne_of_coeff_eq_zero hcoeff
    rw [hn]
    exact (HahnSeries.order_eq_orderTop_of_ne_zero hX).symm
  omega

/-- The coefficient one integral jet above the lower face of a product. -/
theorem laurent_coeff_mul_lower_succ68
    (X Y : LaurentSeries k) (m n : ℤ)
    (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
    (hY : (↑n : WithTop ℤ) ≤ Y.orderTop) :
    (X * Y).coeff (m + n + 1) =
      X.coeff m * Y.coeff (n + 1) + X.coeff (m + 1) * Y.coeff n := by
  let Xt : LaurentSeries k := X - HahnSeries.single m (X.coeff m)
  let Yt : LaurentSeries k := Y - HahnSeries.single n (Y.coeff n)
  have hsm : (↑m : WithTop ℤ) ≤
      (HahnSeries.single m (X.coeff m) : LaurentSeries k).orderTop := by
    by_cases hx : X.coeff m = 0
    · simp [hx]
    · rw [HahnSeries.orderTop_single hx]
  have hsn : (↑n : WithTop ℤ) ≤
      (HahnSeries.single n (Y.coeff n) : LaurentSeries k).orderTop := by
    by_cases hy : Y.coeff n = 0
    · simp [hy]
    · rw [HahnSeries.orderTop_single hy]
  have hXt0 : Xt.coeff m = 0 := by
    simp [Xt]
  have hYt0 : Yt.coeff n = 0 := by
    simp [Yt]
  have hXtBase : (↑m : WithTop ℤ) ≤ Xt.orderTop := by
    exact le_trans (by simpa using min_le_min hX hsm)
      HahnSeries.min_orderTop_le_orderTop_sub
  have hYtBase : (↑n : WithTop ℤ) ≤ Yt.orderTop := by
    exact le_trans (by simpa using min_le_min hY hsn)
      HahnSeries.min_orderTop_le_orderTop_sub
  have hXt := laurent_orderTop_ge_succ_of_coeff_zero68 Xt m hXtBase hXt0
  have hYt := laurent_orderTop_ge_succ_of_coeff_zero68 Yt n hYtBase hYt0
  have hTT : (Xt * Yt).coeff (m + n + 1) = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    have hadd : (↑(m + 1) : WithTop ℤ) + ↑(n + 1) ≤
        (Xt * Yt).orderTop :=
      le_trans (add_le_add hXt hYt) HahnSeries.orderTop_add_le_mul
    rw [← WithTop.coe_add] at hadd
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) hadd
  have hXdec : X = HahnSeries.single m (X.coeff m) + Xt := by
    simp [Xt]
  have hYdec : Y = HahnSeries.single n (Y.coeff n) + Yt := by
    simp [Yt]
  have hSS :
      ((HahnSeries.single m (X.coeff m) : LaurentSeries k) *
          HahnSeries.single n (Y.coeff n)).coeff (m + n + 1) = 0 := by
    rw [HahnSeries.coeff_single_mul]
    have hi : m + n + 1 - m = n + 1 := by omega
    rw [hi]
    simp [HahnSeries.coeff_single]
  have hSY :
      ((HahnSeries.single m (X.coeff m) : LaurentSeries k) * Yt).coeff
          (m + n + 1) = X.coeff m * Y.coeff (n + 1) := by
    rw [HahnSeries.coeff_single_mul]
    have hi : m + n + 1 - m = n + 1 := by omega
    rw [hi]
    simp [Yt]
  have hXS :
      (Xt * (HahnSeries.single n (Y.coeff n) : LaurentSeries k)).coeff
          (m + n + 1) = X.coeff (m + 1) * Y.coeff n := by
    rw [HahnSeries.coeff_mul_single]
    have hi : m + n + 1 - n = m + 1 := by omega
    rw [hi]
    simp [Xt]
  conv_lhs =>
    rw [hXdec, hYdec]
  simp only [add_mul, mul_add, HahnSeries.coeff_add]
  rw [hSS, hSY, hXS, hTT]
  ring

/-- The boundary coefficient of a Laurent product. -/
theorem laurent_coeff_mul_lower68
    (X Y : LaurentSeries k) (m n : ℤ)
    (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
    (hY : (↑n : WithTop ℤ) ≤ Y.orderTop) :
    (X * Y).coeff (m + n) = X.coeff m * Y.coeff n := by
  by_cases hX0 : X = 0
  · simp [hX0]
  by_cases hY0 : Y = 0
  · simp [hY0]
  have hXord : X.orderTop = (↑X.order : WithTop ℤ) :=
    (HahnSeries.order_eq_orderTop_of_ne_zero hX0).symm
  have hYord : Y.orderTop = (↑Y.order : WithTop ℤ) :=
    (HahnSeries.order_eq_orderTop_of_ne_zero hY0).symm
  have hm : m ≤ X.order := by
    rw [hXord, WithTop.coe_le_coe] at hX
    exact hX
  have hn : n ≤ Y.order := by
    rw [hYord, WithTop.coe_le_coe] at hY
    exact hY
  by_cases hme : m = X.order
  · by_cases hne : n = Y.order
    · subst m
      subst n
      rw [HahnSeries.coeff_mul_order_add_order,
        HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq]
    · have hnlt : n < Y.order := lt_of_le_of_ne hn hne
      have hYc : Y.coeff n = 0 :=
        HahnSeries.coeff_eq_zero_of_lt_orderTop (by
          rw [hYord]
          exact WithTop.coe_lt_coe.mpr hnlt)
      have hXYc : (X * Y).coeff (m + n) = 0 :=
        HahnSeries.coeff_eq_zero_of_lt_orderTop (by
          rw [HahnSeries.orderTop_mul, hXord, hYord, ← WithTop.coe_add]
          exact WithTop.coe_lt_coe.mpr (by
            rw [hme]
            simpa [add_comm] using add_lt_add_left hnlt X.order))
      rw [hXYc, hYc, mul_zero]
  · have hmlt : m < X.order := lt_of_le_of_ne hm hme
    have hXc : X.coeff m = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_orderTop (by
        rw [hXord]
        exact WithTop.coe_lt_coe.mpr hmlt)
    have hXYc : (X * Y).coeff (m + n) = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_orderTop (by
        rw [HahnSeries.orderTop_mul, hXord, hYord, ← WithTop.coe_add]
        exact WithTop.coe_lt_coe.mpr (add_lt_add_of_lt_of_le hmlt hn))
    rw [hXYc, hXc, zero_mul]

theorem laurent_coeff_sq_lower_succ68
    (X : LaurentSeries k) (m : ℤ)
    (hX : (↑m : WithTop ℤ) ≤ X.orderTop) :
    (X ^ 2).coeff (2 * m + 1) = 2 * X.coeff m * X.coeff (m + 1) := by
  rw [pow_two]
  have h := laurent_coeff_mul_lower_succ68 X X m m hX hX
  convert h using 1 <;> ring

theorem laurent_coeff_cube_lower68
    (X : LaurentSeries k) (m : ℤ)
    (hX : (↑m : WithTop ℤ) ≤ X.orderTop) :
    (X ^ 3).coeff (3 * m) = (X.coeff m) ^ 3 := by
  rw [pow_succ, pow_two]
  have hXX := HahnSeries.orderTop_add_le_mul.trans' (add_le_add hX hX)
  have h1 := laurent_coeff_mul_lower68 (X * X) X (m + m) m hXX hX
  have h2 := laurent_coeff_mul_lower68 X X m m hX hX
  rw [h2] at h1
  convert h1 using 1 <;> ring

theorem laurent_coeff_mul_three_lower_succ68
    (X Y Z : LaurentSeries k) (m n r : ℤ)
    (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
    (hY : (↑n : WithTop ℤ) ≤ Y.orderTop)
    (hZ : (↑r : WithTop ℤ) ≤ Z.orderTop) :
    (X * Y * Z).coeff (m + n + r + 1) =
      X.coeff (m + 1) * Y.coeff n * Z.coeff r +
      X.coeff m * Y.coeff (n + 1) * Z.coeff r +
      X.coeff m * Y.coeff n * Z.coeff (r + 1) := by
  have hXY : (↑(m + n) : WithTop ℤ) ≤ (X * Y).orderTop := by
    rw [WithTop.coe_add]
    exact le_trans (add_le_add hX hY) HahnSeries.orderTop_add_le_mul
  have hnext := laurent_coeff_mul_lower_succ68 (X * Y) Z (m + n) r hXY hZ
  have hXY0 := laurent_coeff_mul_lower68 X Y m n hX hY
  have hXY1 := laurent_coeff_mul_lower_succ68 X Y m n hX hY
  rw [hXY0, hXY1] at hnext
  convert hnext using 1 <;> ring

theorem laurent_coeff_cube_lower_succ68
    (X : LaurentSeries k) (m : ℤ)
    (hX : (↑m : WithTop ℤ) ≤ X.orderTop) :
    (X ^ 3).coeff (3 * m + 1) =
      3 * (X.coeff m) ^ 2 * X.coeff (m + 1) := by
  rw [pow_succ, pow_two]
  have h := laurent_coeff_mul_three_lower_succ68 X X X m m m hX hX hX
  convert h using 1 <;> ring

def rhoOneZeroLCubicExceptionalHomogeneousNextFour68
    (b1 b2 c1 c2 f1 f2 g1 g2 : k) : k :=
  -b1 ^ 3 + 9 * (b1 * g2 + b2 * g1 + c1 * f2 + c2 * f1)

def rhoOneZeroLCubicExceptionalHomogeneousNextThree68
    (a a1 b1 b2 c1 c2 f1 f2 g1 g2 : k) : k :=
  -2 * (a * b1 * f2 + a * b2 * f1 + a1 * b1 * f1) -
    2 * b1 ^ 2 * c1 + 6 * (c1 * g2 + c2 * g1) + 3 * f1 ^ 2

/-- Over integral exponents, the next homogeneous I4/I3 face after
`delta = 0` is an exact two-jet formula. -/
theorem firstIntegral_mainTangent_exceptional_homogeneous_next_laurent68
    (gamma epsilon zeta : k)
    (A B C F G : LaurentSeries k)
    (hA : (↑(-2 : ℤ) : WithTop ℤ) ≤ A.orderTop)
    (hB : (↑(-1 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (↑(-2 : ℤ) : WithTop ℤ) ≤ C.orderTop)
    (hF : (↑(-2 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-3 : ℤ) : WithTop ℤ) ≤ G.orderTop) :
    (firstIntegralFour68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
      (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C (0 : k))
      (HahnSeries.C gamma) (HahnSeries.C (0 : k))
      (HahnSeries.C epsilon) (HahnSeries.C zeta)).coeff (-3 : ℤ) =
        (8 / 27 : k) * rhoOneZeroLCubicExceptionalHomogeneousNextFour68
          (B.coeff (-1)) (B.coeff 0) (C.coeff (-2)) (C.coeff (-1))
          (F.coeff (-2)) (F.coeff (-1)) (G.coeff (-3)) (G.coeff (-2)) ∧
    (firstIntegralThree68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
      (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C (0 : k))
      (HahnSeries.C gamma) (HahnSeries.C (0 : k))
      (HahnSeries.C epsilon) (HahnSeries.C zeta)).coeff (-4 : ℤ) =
        (4 / 9 : k) * rhoOneZeroLCubicExceptionalHomogeneousNextThree68
          (A.coeff (-2)) (A.coeff (-1)) (B.coeff (-1)) (B.coeff 0)
          (C.coeff (-2)) (C.coeff (-1)) (F.coeff (-2)) (F.coeff (-1))
          (G.coeff (-3)) (G.coeff (-2)) := by
  have hB3 := laurent_coeff_cube_lower68 B (-1) hB
  have hBG := laurent_coeff_mul_lower_succ68 B G (-1) (-3) hB hG
  have hCF := laurent_coeff_mul_lower_succ68 C F (-2) (-2) hC hF
  have hABF := laurent_coeff_mul_three_lower_succ68 A B F
    (-2) (-1) (-2) hA hB hF
  have hBBord : (↑(-2 : ℤ) : WithTop ℤ) ≤ (B * B).orderTop := by
    rw [show (-2 : ℤ) = -1 + -1 by norm_num, WithTop.coe_add]
    exact le_trans (add_le_add hB hB) HahnSeries.orderTop_add_le_mul
  have hBBC := laurent_coeff_mul_lower68 (B * B) C (-2) (-2) hBBord hC
  have hBB := laurent_coeff_mul_lower68 B B (-1) (-1) hB hB
  norm_num at hB3 hBG hCF hABF hBBC hBB
  rw [hBB] at hBBC
  have hCG := laurent_coeff_mul_lower_succ68 C G (-2) (-3) hC hG
  have hFF := laurent_coeff_mul_lower68 F F (-2) (-2) hF hF
  have hFz : F.coeff (-3 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le
      (WithTop.coe_lt_coe.mpr (by omega)) hF)
  have hAz : A.coeff (-3 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le
      (WithTop.coe_lt_coe.mpr (by omega)) hA)
  have hBz : B.coeff (-3 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le
      (WithTop.coe_lt_coe.mpr (by omega)) hB)
  have hGz : G.coeff (-4 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le
      (WithTop.coe_lt_coe.mpr (by omega)) hG)
  have hCz : C.coeff (-4 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le
      (WithTop.coe_lt_coe.mpr (by omega)) hC)
  have hFz4 : F.coeff (-4 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le
      (WithTop.coe_lt_coe.mpr (by omega)) hF)
  have hBz4 : B.coeff (-4 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le
      (WithTop.coe_lt_coe.mpr (by omega)) hB)
  have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
      ((HahnSeries.C s) * X).coeff r = s * X.coeff r := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hc827 : (-8 / 27 : LaurentSeries k) =
      HahnSeries.C (-8 / 27 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_neg, map_ofNat, map_ofNat]
  have hc83 : (8 / 3 : LaurentSeries k) =
      HahnSeries.C (8 / 3 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hcn89 : (-8 / 9 : LaurentSeries k) =
      HahnSeries.C (-8 / 9 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_neg, map_ofNat, map_ofNat]
  have hc43 : (4 / 3 : LaurentSeries k) =
      HahnSeries.C (4 / 3 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hcn23 : (-2 / 3 : LaurentSeries k) =
      HahnSeries.C (-2 / 3 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_neg, map_ofNat, map_ofNat]
  have hc23 : (2 / 3 : LaurentSeries k) =
      HahnSeries.C (2 / 3 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hc4 : (4 : LaurentSeries k) = HahnSeries.C (4 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_ofNat]
  have hc2 : (2 : LaurentSeries k) = HahnSeries.C (2 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_ofNat]
  have hsB3 : ((-8 / 27 : LaurentSeries k) * B ^ 3).coeff (-3) =
      (-8 / 27 : k) * (B.coeff (-1)) ^ 3 := by
    rw [hc827, hscale, hB3]
  have hsBG : ((8 / 3 : LaurentSeries k) * B * G).coeff (-3) =
      (8 / 3 : k) *
        (B.coeff (-1) * G.coeff (-2) + B.coeff 0 * G.coeff (-3)) := by
    rw [mul_assoc, hc83, hscale, hBG]
  have hsCF : ((8 / 3 : LaurentSeries k) * C * F).coeff (-3) =
      (8 / 3 : k) *
        (C.coeff (-2) * F.coeff (-1) + C.coeff (-1) * F.coeff (-2)) := by
    rw [mul_assoc, hc83, hscale, hCF]
  have hsABF : ((-8 / 9 : LaurentSeries k) * A * B * F).coeff (-4) =
      (-8 / 9 : k) *
        (A.coeff (-1) * B.coeff (-1) * F.coeff (-2) +
          A.coeff (-2) * B.coeff 0 * F.coeff (-2) +
          A.coeff (-2) * B.coeff (-1) * F.coeff (-1)) := by
    rw [show (-8 / 9 : LaurentSeries k) * A * B * F =
        (-8 / 9 : LaurentSeries k) * (A * B * F) by ring,
      hcn89, hscale, hABF]
  have hsBBC : ((8 / 9 : LaurentSeries k) * B ^ 2 * C).coeff (-4) =
      (8 / 9 : k) * (B.coeff (-1) ^ 2 * C.coeff (-2)) := by
    have hc89 : (8 / 9 : LaurentSeries k) = HahnSeries.C (8 / 9 : k) := by
      rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
    rw [show (8 / 9 : LaurentSeries k) * B ^ 2 * C =
        (8 / 9 : LaurentSeries k) * (B * B * C) by ring,
      hc89, hscale, hBBC]
    ring
  have hsCG : ((8 / 3 : LaurentSeries k) * C * G).coeff (-4) =
      (8 / 3 : k) *
        (C.coeff (-2) * G.coeff (-2) + C.coeff (-1) * G.coeff (-3)) := by
    norm_num at hCG
    rw [mul_assoc, hc83, hscale, hCG]
  have hsFF : ((4 / 3 : LaurentSeries k) * F ^ 2).coeff (-4) =
      (4 / 3 : k) * F.coeff (-2) ^ 2 := by
    norm_num at hFF
    rw [hc43, hscale, pow_two, hFF]
    ring
  have hsGammaF :
      ((4 : LaurentSeries k) * HahnSeries.C gamma * F).coeff (-3) = 0 := by
    rw [hc4, ← map_mul, hscale, hFz, mul_zero]
  have hsTwoB : ((2 : LaurentSeries k) * B).coeff (-3) = 0 := by
    rw [hc2, hscale, hBz, mul_zero]
  have hsGammaBB :
      ((-2 / 3 : LaurentSeries k) * HahnSeries.C gamma * B ^ 2).coeff
          (-4) = 0 := by
    have hBBz : (B ^ 2).coeff (-4 : ℤ) = 0 := by
      apply HahnSeries.coeff_eq_zero_of_lt_orderTop
      rw [pow_two]
      exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) hBBord
    rw [hcn23, ← map_mul, hscale, hBBz, mul_zero]
  have hsGammaG :
      ((4 : LaurentSeries k) * HahnSeries.C gamma * G).coeff (-4) = 0 := by
    rw [hc4, ← map_mul, hscale, hGz, mul_zero]
  have hsEpsilonC :
      ((2 : LaurentSeries k) * HahnSeries.C epsilon * C).coeff (-4) = 0 := by
    rw [hc2, ← map_mul, hscale, hCz, mul_zero]
  have hsGammaF' :
      ((4 : LaurentSeries k) * HahnSeries.single 0 gamma * F).coeff (-3) = 0 := by
    simpa only [HahnSeries.C_apply] using hsGammaF
  have hsGammaBB' :
      ((-2 / 3 : LaurentSeries k) * HahnSeries.single 0 gamma * B ^ 2).coeff
          (-4) = 0 := by
    simpa only [HahnSeries.C_apply] using hsGammaBB
  have hsGammaBBPos' :
      ((2 / 3 : LaurentSeries k) * HahnSeries.single 0 gamma * B ^ 2).coeff
          (-4) = 0 := by
    have hBBz : (B ^ 2).coeff (-4 : ℤ) = 0 := by
      apply HahnSeries.coeff_eq_zero_of_lt_orderTop
      rw [pow_two]
      exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) hBBord
    rw [← HahnSeries.C_apply, hc23, ← map_mul, hscale, hBBz, mul_zero]
  have hsGammaG' :
      ((4 : LaurentSeries k) * HahnSeries.single 0 gamma * G).coeff (-4) = 0 := by
    simpa only [HahnSeries.C_apply] using hsGammaG
  have hsEpsilonC' :
      ((2 : LaurentSeries k) * HahnSeries.single 0 epsilon * C).coeff (-4) = 0 := by
    simpa only [HahnSeries.C_apply] using hsEpsilonC
  have h4dec := firstIntegralFour_mainTangent_decomposition68
    (k := LaurentSeries k) (HahnSeries.C (0 : k)) (HahnSeries.C gamma)
      (HahnSeries.C (0 : k)) (HahnSeries.C epsilon) (HahnSeries.C zeta)
      A B C F G
  have h3dec := firstIntegralThree_mainTangent_decomposition68
    (k := LaurentSeries k) (HahnSeries.C (0 : k)) (HahnSeries.C gamma)
      (HahnSeries.C (0 : k)) (HahnSeries.C epsilon) (HahnSeries.C zeta)
      A B C F G
  constructor
  · rw [h4dec]
    simp only [firstIntegralFourMainTangentTop68,
      firstIntegralFourMainTangentLower68, HahnSeries.coeff_add,
      HahnSeries.coeff_sub, HahnSeries.coeff_neg]
    simp only [HahnSeries.C_zero, zero_mul, mul_zero, zero_add, sub_zero]
    simp only [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul,
      HahnSeries.coeff_mul_single_zero]
    rw [hsB3, hsBG, hsCF, hsGammaF', hAz, hsTwoB]
    simp only [HahnSeries.coeff_zero, mul_zero, zero_mul, add_zero]
    simp only [rhoOneZeroLCubicExceptionalHomogeneousNextFour68]
    ring
  · rw [h3dec]
    simp only [firstIntegralThreeMainTangentTop68,
      firstIntegralThreeMainTangentLower68, HahnSeries.coeff_add,
      HahnSeries.coeff_sub, HahnSeries.coeff_neg]
    simp only [HahnSeries.C_zero, zero_mul, mul_zero, zero_add, sub_zero]
    simp only [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul,
      HahnSeries.coeff_mul_single_zero]
    rw [hsABF, hsBBC, hsCG, hsFF, hsGammaBBPos', hsGammaG',
      hsEpsilonC', hBz4]
    simp only [HahnSeries.coeff_zero, mul_zero, zero_mul, add_zero]
    simp only [rhoOneZeroLCubicExceptionalHomogeneousNextThree68]
    ring

def rhoOneZeroLCubicExceptionalHomogeneousCompatibility68
    (a a1 b1 b2 c1 c2 f1 g1 : k) : k :=
  -2 * a * b1 ^ 4 + 18 * a * b1 * b2 * g1 +
    18 * a * b1 * c2 * f1 - 18 * a * b2 * c1 * f1 -
    18 * a1 * b1 * c1 * f1 - 18 * b1 ^ 2 * c1 ^ 2 +
    54 * c1 * c2 * g1 + 27 * c1 * f1 ^ 2

/-- On the singular second determinant, the next I4/I3 equations eliminate
the new `f2,g2` jet and leave one explicit compatibility polynomial. -/
theorem rhoOneZeroLCubicExceptional_homogeneous_compatibility68
    (a a1 b1 b2 c1 c2 f1 f2 g1 g2 : k)
    (h4 : rhoOneZeroLCubicExceptionalHomogeneousNextFour68
      b1 b2 c1 c2 f1 f2 g1 g2 = 0)
    (h3 : rhoOneZeroLCubicExceptionalHomogeneousNextThree68
      a a1 b1 b2 c1 c2 f1 f2 g1 g2 = 0)
    (hdisc : rhoOneZeroLCubicExceptionalSecondDiscriminant68 a b1 c1 = 0) :
    rhoOneZeroLCubicExceptionalHomogeneousCompatibility68
      a a1 b1 b2 c1 c2 f1 g1 = 0 := by
  simp only [rhoOneZeroLCubicExceptionalHomogeneousNextFour68] at h4
  simp only [rhoOneZeroLCubicExceptionalHomogeneousNextThree68] at h3
  simp only [rhoOneZeroLCubicExceptionalSecondDiscriminant68] at hdisc
  simp only [rhoOneZeroLCubicExceptionalHomogeneousCompatibility68]
  linear_combination 2 * a * b1 * h4 + 9 * c1 * h3 - 18 * g2 * hdisc

theorem ratFuncAtLaurent46_C68 (a c : k) :
    ratFuncAtLaurent46 a (RatFunc.C c) = HahnSeries.C c := by
  simp only [ratFuncAtLaurent46, RatFunc.liftRingHom_C,
    polynomialAtLaurent46, RingHom.comp_apply, polynomialTranslate46,
    Polynomial.coe_compRingHom_apply, C_comp, map_C]
  simp

theorem ratFuncAtHahn46_coeff_int68 (a : k) (R : RatFunc k) (n : ℤ) :
    (ratFuncAtHahn46 a R).coeff (n : ℚ) =
      (ratFuncAtLaurent46 a R).coeff n := by
  let e : ℤ ↪o ℚ :=
    ⟨⟨Int.castAddHom ℚ, intCastAddHom46_injective⟩,
      intCastAddHom46_le _ _⟩
  change (HahnSeries.embDomain e (ratFuncAtLaurent46 a R)).coeff
      (e n) = (ratFuncAtLaurent46 a R).coeff n
  exact HahnSeries.embDomain_coeff

/-- A rational Hahn lower bound at an integral exponent reflects to the
underlying Laurent series. -/
theorem ratFuncAtLaurent46_orderTop_ge_of_hahn68
    (a : k) (R : RatFunc k) (n : ℤ)
    (h : (↑(n : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 a R).orderTop) :
    (↑n : WithTop ℤ) ≤ (ratFuncAtLaurent46 a R).orderTop := by
  let y : LaurentSeries k := ratFuncAtLaurent46 a R
  let e : ℤ ↪o ℚ :=
    ⟨⟨Int.castAddHom ℚ, intCastAddHom46_injective⟩,
      intCastAddHom46_le _ _⟩
  have hX : ratFuncAtHahn46 a R = HahnSeries.embDomain e y := by
    dsimp only [e, y, ratFuncAtHahn46, laurentToRationalHahn46]
    rfl
  rw [hX, HahnSeries.orderTop_embDomain] at h
  cases hm : y.orderTop with
  | top => simp [y, hm]
  | coe m =>
      simp only [hm, WithTop.map_coe, WithTop.coe_le_coe] at h ⊢
      dsimp only [e, Int.castAddHom] at h
      change (n : ℚ) ≤ (m : ℚ) at h
      exact_mod_cast h

/-- Exact rational-function source transport of the homogeneous next face.
The hypotheses are identities in `k(x)`, so this does not allow arbitrary
Hahn-series pairs. -/
theorem ratFunc_exceptional_homogeneous_compatibility68
    (root : k) (A B C F G : RatFunc k)
    (gamma epsilon zeta i4 i3 : k)
    (hA : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root A).orderTop)
    (hB : (↑(-1 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root B).orderTop)
    (hC : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root C).orderTop)
    (hF : (↑(-2 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root F).orderTop)
    (hG : (↑(-3 : ℚ) : WithTop ℚ) ≤ (ratFuncAtHahn46 root G).orderTop)
    (hi4 : firstIntegralFour68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
      (A ^ 3 / 27 + A * C / 3 + G) (RatFunc.C (0 : k))
      (RatFunc.C gamma) (RatFunc.C (0 : k)) (RatFunc.C epsilon)
      (RatFunc.C zeta) = RatFunc.C i4)
    (hi3 : firstIntegralThree68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
      (A ^ 3 / 27 + A * C / 3 + G) (RatFunc.C (0 : k))
      (RatFunc.C gamma) (RatFunc.C (0 : k)) (RatFunc.C epsilon)
      (RatFunc.C zeta) = RatFunc.C i3)
    (hdisc : rhoOneZeroLCubicExceptionalSecondDiscriminant68
      ((ratFuncAtHahn46 root A).coeff (-2 : ℚ))
      ((ratFuncAtHahn46 root B).coeff (-1 : ℚ))
      ((ratFuncAtHahn46 root C).coeff (-2 : ℚ)) = 0) :
    rhoOneZeroLCubicExceptionalHomogeneousCompatibility68
      ((ratFuncAtLaurent46 root A).coeff (-2))
      ((ratFuncAtLaurent46 root A).coeff (-1))
      ((ratFuncAtLaurent46 root B).coeff (-1))
      ((ratFuncAtLaurent46 root B).coeff 0)
      ((ratFuncAtLaurent46 root C).coeff (-2))
      ((ratFuncAtLaurent46 root C).coeff (-1))
      ((ratFuncAtLaurent46 root F).coeff (-2))
      ((ratFuncAtLaurent46 root G).coeff (-3)) = 0 := by
  let aL := ratFuncAtLaurent46 root A
  let bL := ratFuncAtLaurent46 root B
  let cL := ratFuncAtLaurent46 root C
  let fL := ratFuncAtLaurent46 root F
  let gL := ratFuncAtLaurent46 root G
  have hAL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root A (-2) hA
  have hBL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root B (-1) hB
  have hCL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root C (-2) hC
  have hFL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root F (-2) hF
  have hGL := ratFuncAtLaurent46_orderTop_ge_of_hahn68 root G (-3) hG
  have hi4L := congrArg (ratFuncAtLaurent46 root) hi4
  have hi3L := congrArg (ratFuncAtLaurent46 root) hi3
  have hi4L' :
      firstIntegralFour68 0 aL bL (aL ^ 2 / 3 + cL) (aL * bL / 3 + fL)
        (aL ^ 3 / 27 + aL * cL / 3 + gL) (HahnSeries.C (0 : k))
        (HahnSeries.C gamma) (HahnSeries.C (0 : k))
        (HahnSeries.C epsilon) (HahnSeries.C zeta) = HahnSeries.C i4 := by
    dsimp only [aL, bL, cL, fL, gL]
    simpa only [firstIntegralFour68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_zero, map_one,
      ratFuncAtLaurent46_C68] using hi4L
  have hi3L' :
      firstIntegralThree68 0 aL bL (aL ^ 2 / 3 + cL) (aL * bL / 3 + fL)
        (aL ^ 3 / 27 + aL * cL / 3 + gL) (HahnSeries.C (0 : k))
        (HahnSeries.C gamma) (HahnSeries.C (0 : k))
        (HahnSeries.C epsilon) (HahnSeries.C zeta) = HahnSeries.C i3 := by
    dsimp only [aL, bL, cL, fL, gL]
    simpa only [firstIntegralThree68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_zero, map_one,
      ratFuncAtLaurent46_C68] using hi3L
  have hface := firstIntegral_mainTangent_exceptional_homogeneous_next_laurent68
    gamma epsilon zeta aL bL cL fL gL hAL hBL hCL hFL hGL
  have h4coeff := congrArg (fun X : LaurentSeries k => X.coeff (-3 : ℤ)) hi4L'
  have h3coeff := congrArg (fun X : LaurentSeries k => X.coeff (-4 : ℤ)) hi3L'
  have h4const : (HahnSeries.C i4 : LaurentSeries k).coeff (-3 : ℤ) = 0 := by
    simp [HahnSeries.C_apply]
  have h3const : (HahnSeries.C i3 : LaurentSeries k).coeff (-4 : ℤ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hface.1, h4const] at h4coeff
  rw [hface.2, h3const] at h3coeff
  have h4zero : rhoOneZeroLCubicExceptionalHomogeneousNextFour68
      (bL.coeff (-1)) (bL.coeff 0) (cL.coeff (-2)) (cL.coeff (-1))
      (fL.coeff (-2)) (fL.coeff (-1)) (gL.coeff (-3)) (gL.coeff (-2)) = 0 := by
    linear_combination (27 / 8 : k) * h4coeff
  have h3zero : rhoOneZeroLCubicExceptionalHomogeneousNextThree68
      (aL.coeff (-2)) (aL.coeff (-1)) (bL.coeff (-1)) (bL.coeff 0)
      (cL.coeff (-2)) (cL.coeff (-1)) (fL.coeff (-2)) (fL.coeff (-1))
      (gL.coeff (-3)) (gL.coeff (-2)) = 0 := by
    linear_combination (9 / 4 : k) * h3coeff
  have hdiscL : rhoOneZeroLCubicExceptionalSecondDiscriminant68
      (aL.coeff (-2)) (bL.coeff (-1)) (cL.coeff (-2)) = 0 := by
    dsimp only [aL, bL, cL]
    have hAc := ratFuncAtHahn46_coeff_int68 root A (-2)
    have hBc := ratFuncAtHahn46_coeff_int68 root B (-1)
    have hCc := ratFuncAtHahn46_coeff_int68 root C (-2)
    norm_num at hAc hBc hCc
    rw [hAc, hBc, hCc] at hdisc
    exact hdisc
  exact rhoOneZeroLCubicExceptional_homogeneous_compatibility68
    _ _ _ _ _ _ _ _ _ _ h4zero h3zero hdiscL

end AlignedSquareRhoOneCubicExceptionalHomogeneousNext68

end Max11DegreeRoutes
