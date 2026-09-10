import Sol68ScaleTwoAlignedSquareSourceSelectorHierarchyScratch
import LowScale68ScaleTwoAlignedSquareRhoOneCubicExceptionalHomogeneousNext

/-! # Consuming the two nonexceptional main-tangent limbs

Starting from the verified source selector hierarchy, this file attacks the
two nonexceptional main-tangent invariant limbs of
`RhoOneAlignedSquareEarlyCubicSibling68`:

* the `c = 0, b ≠ 0, F[-3] = 0` limb carrying the row
  `-64 b³ + 15 β a³ + 576 b g₄ = 0`, and
* the `c ≠ 0, b ≠ 0, c² = a b²` limb carrying the two I4/I3 invariants.

Both limbs are refined by the next unused I4/I3 coefficient pair — the
Hahn exponents `-5` (I4) and `-6` (I3), one jet above the invariant rows
already consumed.  Over integral exponents these rows are exact two-jet
formulas obtained from the Laurent-level convolution helpers.  The rows are
transported to the normalized source through the same ground first-integral
identities used by the invariant faces; no septic-nonzero packet, X-degree
input, or finite-root shortcut is used anywhere (the local septic
coefficient is exactly zero on this component).

Exact scalar gains:

* `c = 0` limb: the reduced I4 row solves the new `g₃` jet
  (`192 b g₃ = 64 b² b₁ - 15 β a² a₁ - 192 b₁ g₄`), the reduced I3 row is a
  `g₃, b₁, a₁`-free tie `64 a b f₂ + 64 b² c₂ - 192 c₂ g₄ + 5 β a² b = 0`
  on the two reappearing defect jets, and eliminating `g₄` through the old
  row gives the closed tie
  `192 a b² f₂ + 128 b³ c₂ + 15 β a³ c₂ + 15 β a² b² = 0`.
* `c ≠ 0` limb: the previously unconsumed reduction
  `rhoOneZeroLCubicMainTangent_nonzero_reduced68` is wired in
  (`3 c g₄ = a b f + b² c` and `128 b³ + 15 β a³ + 768 c f = 0`), the
  root-square relation upgrades it to the exact solve
  `2304 b g₄ = 640 b³ - 15 β a³`, and eliminating the new `g₃` jet between
  the two next rows leaves a single explicit compatibility tie on the
  fresh jets `a₁, b₁, c₂, f₂`.

Every other source sibling (the divisibility descent, the noncubic packet,
the second cubic component, the row-one exceptional `b=c=d=e=0` locus and
the exceptional `b=c=β=0` main entry) is preserved verbatim.
-/

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section AlignedSquareMainTangentNonexceptionalConsumer68

variable {k : Type*} [Field k] [CharZero k]

local instance mainTangentNonexceptionalConsumerHahnCharZero68 :
    CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

local instance mainTangentNonexceptionalConsumerLaurentCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

/-- The next I4 coefficient row (Hahn exponent `-5`) on the main tangent,
one jet above `rhoOneZeroLCubicMainTangentFour68`. -/
def rhoOneZeroLCubicMainTangentNextFour68
    (beta a a1 b b1 c c2 f f2 g4 g3 : k) : k :=
  -64 * b ^ 2 * b1 + 15 * beta * a ^ 2 * a1 + 60 * beta * a * c +
    192 * b * g3 + 192 * b1 * g4 + 192 * c * f2 + 192 * c2 * f

/-- The next I3 coefficient row (Hahn exponent `-6`) on the main tangent,
one jet above `rhoOneZeroLCubicMainTangentThree68`. -/
def rhoOneZeroLCubicMainTangentNextThree68
    (beta a a1 b b1 c c2 f f2 g4 g3 : k) : k :=
  -5 * beta * a ^ 2 * b - 64 * a * b * f2 - 64 * a * b1 * f -
    64 * a1 * b * f - 64 * b ^ 2 * c2 - 128 * b * b1 * c +
    192 * c * g3 + 192 * c2 * g4 + 96 * f ^ 2

/-- Exact reduction of the next coefficient pair on the `c = 0, f = 0`
limb: the I4 row solves the new `g₃` jet, the I3 row is a `g₃`-free tie on
the reappearing `c₂, f₂` jets, and eliminating `g₄` through the old row
gives a closed tie. -/
theorem rhoOneZeroLCubicMainTangentNext_cZero_reduction68
    (beta a a1 b b1 c c2 f f2 g4 g3 : k)
    (hc : c = 0) (hf : f = 0)
    (h4A : -64 * b ^ 3 + 15 * beta * a ^ 3 + 576 * b * g4 = 0)
    (hN4 : rhoOneZeroLCubicMainTangentNextFour68
      beta a a1 b b1 c c2 f f2 g4 g3 = 0)
    (hN3 : rhoOneZeroLCubicMainTangentNextThree68
      beta a a1 b b1 c c2 f f2 g4 g3 = 0) :
    192 * b * g3 = 64 * b ^ 2 * b1 - 15 * beta * a ^ 2 * a1 -
      192 * b1 * g4 ∧
    64 * a * b * f2 + 64 * b ^ 2 * c2 - 192 * c2 * g4 +
      5 * beta * a ^ 2 * b = 0 ∧
    192 * a * b ^ 2 * f2 + 128 * b ^ 3 * c2 + 15 * beta * a ^ 3 * c2 +
      15 * beta * a ^ 2 * b ^ 2 = 0 := by
  simp only [rhoOneZeroLCubicMainTangentNextFour68,
    rhoOneZeroLCubicMainTangentNextThree68] at hN4 hN3
  refine ⟨?_, ?_, ?_⟩
  · linear_combination hN4 + (-60 * beta * a - 192 * f2) * hc +
      (-192 * c2) * hf
  · linear_combination -hN3 + (-128 * b * b1 + 192 * g3) * hc +
      (-64 * a * b1 - 64 * a1 * b + 96 * f) * hf
  · linear_combination (-3 * b) * hN3 + c2 * h4A +
      (-384 * b ^ 2 * b1 + 576 * b * g3) * hc +
      (-192 * a * b * b1 - 192 * a1 * b ^ 2 + 288 * b * f) * hf

/-- Exact reduction of the next coefficient pair on the
`c ≠ 0, c² = a b²` limb: the root-square relation upgrades the reduced
old rows to the exact `g₄` solve, and eliminating the new `g₃` jet
between the two next rows leaves one explicit compatibility tie on the
fresh jets. -/
theorem rhoOneZeroLCubicMainTangentNext_nonzero_reduction68
    (beta a a1 b b1 c c2 f f2 g4 g3 : k)
    (hb : b ≠ 0) (hc0 : c ≠ 0) (hcsq : c ^ 2 = a * b ^ 2)
    (hg : 3 * c * g4 = a * b * f + b ^ 2 * c)
    (hcf : 128 * b ^ 3 + 15 * beta * a ^ 3 + 768 * c * f = 0)
    (hN4 : rhoOneZeroLCubicMainTangentNextFour68
      beta a a1 b b1 c c2 f f2 g4 g3 = 0)
    (hN3 : rhoOneZeroLCubicMainTangentNextThree68
      beta a a1 b b1 c c2 f f2 g4 g3 = 0) :
    a ≠ 0 ∧
    2304 * b * g4 = 640 * b ^ 3 - 15 * beta * a ^ 3 ∧
    90 * beta * a ^ 2 * a1 * c + 384 * a1 * b ^ 2 * f +
      768 * a * b * b1 * f + 768 * b ^ 2 * b1 * c +
      1536 * a * b ^ 2 * f2 - 128 * b ^ 3 * c2 -
      15 * beta * a ^ 3 * c2 + 390 * beta * a ^ 2 * b ^ 2 -
      576 * b * f ^ 2 = 0 := by
  have ha : a ≠ 0 := by
    intro ha0
    apply hc0
    have hcc : c * c = 0 := by
      linear_combination hcsq + b ^ 2 * ha0
    exact mul_self_eq_zero.mp hcc
  have hq : a * b ^ 2 *
      (2304 * b * g4 - (640 * b ^ 3 - 15 * beta * a ^ 3)) = 0 := by
    linear_combination (768 * b ^ 3 - 2304 * b * g4) * hcsq +
      768 * b * c * hg + a * b ^ 2 * hcf
  have habsq : a * b ^ 2 ≠ 0 := mul_ne_zero ha (pow_ne_zero 2 hb)
  have hbg : 2304 * b * g4 = 640 * b ^ 3 - 15 * beta * a ^ 3 := by
    have hzero := (mul_eq_zero.mp hq).resolve_left habsq
    linear_combination hzero
  refine ⟨ha, hbg, ?_⟩
  simp only [rhoOneZeroLCubicMainTangentNextFour68,
    rhoOneZeroLCubicMainTangentNextThree68] at hN4 hN3
  linear_combination 6 * c * hN4 - 6 * b * hN3 +
    (-360 * beta * a - 1152 * f2) * hcsq + (-384 * b1) * hg +
    (-3 / 2 * c2) * hcf + (1 / 2 * c2) * hbg

set_option maxHeartbeats 1600000 in
/-- Over integral exponents, the next I4/I3 coefficient pair after the two
main-tangent invariant rows is an exact two-jet formula, valid on the whole
generic main-tangent box (no order improvement is assumed, so the formula
covers both nonexceptional limbs simultaneously). -/
theorem firstIntegral_mainTangent_nonexceptionalNext_laurent68
    (beta gamma delta epsilon zeta : k)
    (A B C F G : LaurentSeries k)
    (hA : (↑(-2 : ℤ) : WithTop ℤ) ≤ A.orderTop)
    (hB : (↑(-2 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (↑(-3 : ℤ) : WithTop ℤ) ≤ C.orderTop)
    (hF : (↑(-3 : ℤ) : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-4 : ℤ) : WithTop ℤ) ≤ G.orderTop) :
    (firstIntegralFour68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
      (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C beta)
      (HahnSeries.C gamma) (HahnSeries.C delta) (HahnSeries.C epsilon)
      (HahnSeries.C zeta)).coeff (-5 : ℤ) =
        (1 / 72 : k) * rhoOneZeroLCubicMainTangentNextFour68 beta
          (A.coeff (-2 : ℤ)) (A.coeff (-1 : ℤ))
          (B.coeff (-2 : ℤ)) (B.coeff (-1 : ℤ))
          (C.coeff (-3 : ℤ)) (C.coeff (-2 : ℤ))
          (F.coeff (-3 : ℤ)) (F.coeff (-2 : ℤ))
          (G.coeff (-4 : ℤ)) (G.coeff (-3 : ℤ)) ∧
    (firstIntegralThree68 0 A B (A ^ 2 / 3 + C) (A * B / 3 + F)
      (A ^ 3 / 27 + A * C / 3 + G) (HahnSeries.C beta)
      (HahnSeries.C gamma) (HahnSeries.C delta) (HahnSeries.C epsilon)
      (HahnSeries.C zeta)).coeff (-6 : ℤ) =
        (1 / 72 : k) * rhoOneZeroLCubicMainTangentNextThree68 beta
          (A.coeff (-2 : ℤ)) (A.coeff (-1 : ℤ))
          (B.coeff (-2 : ℤ)) (B.coeff (-1 : ℤ))
          (C.coeff (-3 : ℤ)) (C.coeff (-2 : ℤ))
          (F.coeff (-3 : ℤ)) (F.coeff (-2 : ℤ))
          (G.coeff (-4 : ℤ)) (G.coeff (-3 : ℤ)) := by
  have hscale (s : k) (X : LaurentSeries k) (r : ℤ) :
      ((HahnSeries.C s) * X).coeff r = s * X.coeff r := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  -- numeral constants
  have hc827 : (-8 / 27 : LaurentSeries k) = HahnSeries.C (-8 / 27 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_neg, map_ofNat, map_ofNat]
  have hc572 : (5 / 72 : LaurentSeries k) = HahnSeries.C (5 / 72 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hc83 : (8 / 3 : LaurentSeries k) = HahnSeries.C (8 / 3 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hc56 : (5 / 6 : LaurentSeries k) = HahnSeries.C (5 / 6 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hc512 : (5 / 12 : LaurentSeries k) = HahnSeries.C (5 / 12 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hc14 : (1 / 4 : LaurentSeries k) = HahnSeries.C (1 / 4 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_one, map_ofNat]
  have hc5 : (5 : LaurentSeries k) = HahnSeries.C (5 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_ofNat]
  have hc3 : (3 : LaurentSeries k) = HahnSeries.C (3 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_ofNat]
  have hc4 : (4 : LaurentSeries k) = HahnSeries.C (4 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_ofNat]
  have hc2 : (2 : LaurentSeries k) = HahnSeries.C (2 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_ofNat]
  have hcn89 : (-8 / 9 : LaurentSeries k) = HahnSeries.C (-8 / 9 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_neg, map_ofNat, map_ofNat]
  have hc89 : (8 / 9 : LaurentSeries k) = HahnSeries.C (8 / 9 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hcn572 : (-5 / 72 : LaurentSeries k) = HahnSeries.C (-5 / 72 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_neg, map_ofNat, map_ofNat]
  have hc43 : (4 / 3 : LaurentSeries k) = HahnSeries.C (4 / 3 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  have hc12 : (1 / 2 : LaurentSeries k) = HahnSeries.C (1 / 2 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_one, map_ofNat]
  have hc23 : (2 / 3 : LaurentSeries k) = HahnSeries.C (2 / 3 : k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_ofNat, map_ofNat]
  -- product order bounds
  have hBBord : (↑(-4 : ℤ) : WithTop ℤ) ≤ (B * B).orderTop := by
    rw [show (-4 : ℤ) = -2 + -2 by norm_num, WithTop.coe_add]
    exact le_trans (add_le_add hB hB) HahnSeries.orderTop_add_le_mul
  have hAAord : (↑(-4 : ℤ) : WithTop ℤ) ≤ (A * A).orderTop := by
    rw [show (-4 : ℤ) = -2 + -2 by norm_num, WithTop.coe_add]
    exact le_trans (add_le_add hA hA) HahnSeries.orderTop_add_le_mul
  have hABord : (↑(-4 : ℤ) : WithTop ℤ) ≤ (A * B).orderTop := by
    rw [show (-4 : ℤ) = -2 + -2 by norm_num, WithTop.coe_add]
    exact le_trans (add_le_add hA hB) HahnSeries.orderTop_add_le_mul
  have hAFord : (↑(-5 : ℤ) : WithTop ℤ) ≤ (A * F).orderTop := by
    rw [show (-5 : ℤ) = -2 + -3 by norm_num, WithTop.coe_add]
    exact le_trans (add_le_add hA hF) HahnSeries.orderTop_add_le_mul
  have hBCord : (↑(-5 : ℤ) : WithTop ℤ) ≤ (B * C).orderTop := by
    rw [show (-5 : ℤ) = -2 + -3 by norm_num, WithTop.coe_add]
    exact le_trans (add_le_add hB hC) HahnSeries.orderTop_add_le_mul
  -- convolution facts
  have hB3 := laurent_coeff_cube_lower_succ68 B (-2) hB
  have hA3 := laurent_coeff_cube_lower_succ68 A (-2) hA
  have hBG := laurent_coeff_mul_lower_succ68 B G (-2) (-4) hB hG
  have hCF := laurent_coeff_mul_lower_succ68 C F (-3) (-3) hC hF
  have hAC := laurent_coeff_mul_lower68 A C (-2) (-3) hA hC
  have hABF := laurent_coeff_mul_three_lower_succ68 A B F
    (-2) (-2) (-3) hA hB hF
  have hBBC := laurent_coeff_mul_three_lower_succ68 B B C
    (-2) (-2) (-3) hB hB hC
  have hCG := laurent_coeff_mul_lower_succ68 C G (-3) (-4) hC hG
  have hAA := laurent_coeff_mul_lower68 A A (-2) (-2) hA hA
  have hAAB := laurent_coeff_mul_lower68 (A * A) B (-4) (-2) hAAord hB
  have hFF := laurent_coeff_mul_lower68 F F (-3) (-3) hF hF
  norm_num at hB3 hA3 hBG hCF hAC hABF hBBC hCG hAA hAAB hFF
  rw [hAA] at hAAB
  -- single-series zero coefficients
  have hA5 : A.coeff (-5 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le
      (WithTop.coe_lt_coe.mpr (by omega)) hA)
  have hB5 : B.coeff (-5 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le
      (WithTop.coe_lt_coe.mpr (by omega)) hB)
  have hC5 : C.coeff (-5 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le
      (WithTop.coe_lt_coe.mpr (by omega)) hC)
  have hF5 : F.coeff (-5 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le
      (WithTop.coe_lt_coe.mpr (by omega)) hF)
  have hG5 : G.coeff (-5 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le
      (WithTop.coe_lt_coe.mpr (by omega)) hG)
  have hB6 : B.coeff (-6 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le
      (WithTop.coe_lt_coe.mpr (by omega)) hB)
  have hC6 : C.coeff (-6 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le
      (WithTop.coe_lt_coe.mpr (by omega)) hC)
  have hF6 : F.coeff (-6 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le
      (WithTop.coe_lt_coe.mpr (by omega)) hF)
  have hG6 : G.coeff (-6 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le
      (WithTop.coe_lt_coe.mpr (by omega)) hG)
  -- product zero coefficients
  have hzB2at5 : (B ^ 2).coeff (-5 : ℤ) = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    rw [pow_two]
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) hBBord
  have hzA2at5 : (A ^ 2).coeff (-5 : ℤ) = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    rw [pow_two]
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) hAAord
  have hzB2at6 : (B ^ 2).coeff (-6 : ℤ) = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    rw [pow_two]
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) hBBord
  have hzAF6 : (A * F).coeff (-6 : ℤ) = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) hAFord
  have hzBC6 : (B * C).coeff (-6 : ℤ) = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) hBCord
  have hzAB6 : (A * B).coeff (-6 : ℤ) = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) hABord
  -- I4 terms at exponent -5
  have hs1 : ((-8 / 27 : LaurentSeries k) * B ^ 3).coeff (-5 : ℤ) =
      (-8 / 27 : k) * (3 * B.coeff (-2 : ℤ) ^ 2 * B.coeff (-1 : ℤ)) := by
    rw [hc827, hscale, hB3]
  have hs2 : ((5 / 72 : LaurentSeries k) * HahnSeries.C beta *
      A ^ 3).coeff (-5 : ℤ) =
      (5 / 72 : k) * beta *
        (3 * A.coeff (-2 : ℤ) ^ 2 * A.coeff (-1 : ℤ)) := by
    rw [show (5 / 72 : LaurentSeries k) * HahnSeries.C beta * A ^ 3 =
        HahnSeries.C ((5 / 72 : k) * beta) * A ^ 3 from by
      rw [map_mul, hc572], hscale, hA3]
  have hs3 : ((8 / 3 : LaurentSeries k) * B * G).coeff (-5 : ℤ) =
      (8 / 3 : k) * (B.coeff (-2 : ℤ) * G.coeff (-3 : ℤ) +
        B.coeff (-1 : ℤ) * G.coeff (-4 : ℤ)) := by
    rw [mul_assoc, hc83, hscale, hBG]
  have hs4 : ((8 / 3 : LaurentSeries k) * C * F).coeff (-5 : ℤ) =
      (8 / 3 : k) * (C.coeff (-3 : ℤ) * F.coeff (-2 : ℤ) +
        C.coeff (-2 : ℤ) * F.coeff (-3 : ℤ)) := by
    rw [mul_assoc, hc83, hscale, hCF]
  have hs5 : ((5 / 6 : LaurentSeries k) * HahnSeries.C beta * A *
      C).coeff (-5 : ℤ) =
      (5 / 6 : k) * beta * (A.coeff (-2 : ℤ) * C.coeff (-3 : ℤ)) := by
    rw [show (5 / 6 : LaurentSeries k) * HahnSeries.C beta * A * C =
        HahnSeries.C ((5 / 6 : k) * beta) * (A * C) from by
      rw [map_mul, hc56]; ring, hscale, hAC]
  have hs6 : ((5 / 12 : LaurentSeries k) * HahnSeries.C beta *
      B ^ 2).coeff (-5 : ℤ) = 0 := by
    rw [show (5 / 12 : LaurentSeries k) * HahnSeries.C beta * B ^ 2 =
        HahnSeries.C ((5 / 12 : k) * beta) * B ^ 2 from by
      rw [map_mul, hc512], hscale, hzB2at5, mul_zero]
  have hs7 : ((1 / 4 : LaurentSeries k) * HahnSeries.C delta *
      A ^ 2).coeff (-5 : ℤ) = 0 := by
    rw [show (1 / 4 : LaurentSeries k) * HahnSeries.C delta * A ^ 2 =
        HahnSeries.C ((1 / 4 : k) * delta) * A ^ 2 from by
      rw [map_mul, hc14], hscale, hzA2at5, mul_zero]
  have hs8 : ((5 : LaurentSeries k) * HahnSeries.C beta * G).coeff
      (-5 : ℤ) = 0 := by
    rw [show (5 : LaurentSeries k) * HahnSeries.C beta * G =
        HahnSeries.C ((5 : k) * beta) * G from by
      rw [map_mul, hc5], hscale, hG5, mul_zero]
  have hs9 : ((3 : LaurentSeries k) * HahnSeries.C delta * C).coeff
      (-5 : ℤ) = 0 := by
    rw [show (3 : LaurentSeries k) * HahnSeries.C delta * C =
        HahnSeries.C ((3 : k) * delta) * C from by
      rw [map_mul, hc3], hscale, hC5, mul_zero]
  have hs10 : ((4 : LaurentSeries k) * HahnSeries.C gamma * F).coeff
      (-5 : ℤ) = 0 := by
    rw [show (4 : LaurentSeries k) * HahnSeries.C gamma * F =
        HahnSeries.C ((4 : k) * gamma) * F from by
      rw [map_mul, hc4], hscale, hF5, mul_zero]
  have hs11 : (A * HahnSeries.C zeta).coeff (-5 : ℤ) = 0 := by
    rw [mul_comm A (HahnSeries.C zeta), hscale, hA5, mul_zero]
  have hs12 : ((2 : LaurentSeries k) * B * HahnSeries.C epsilon).coeff
      (-5 : ℤ) = 0 := by
    rw [show (2 : LaurentSeries k) * B * HahnSeries.C epsilon =
        HahnSeries.C ((2 : k) * epsilon) * B from by
      rw [map_mul, hc2]; ring, hscale, hB5, mul_zero]
  -- I3 terms at exponent -6
  have hq1 : ((-8 / 9 : LaurentSeries k) * A * B * F).coeff (-6 : ℤ) =
      (-8 / 9 : k) *
        (A.coeff (-1 : ℤ) * B.coeff (-2 : ℤ) * F.coeff (-3 : ℤ) +
          A.coeff (-2 : ℤ) * B.coeff (-1 : ℤ) * F.coeff (-3 : ℤ) +
          A.coeff (-2 : ℤ) * B.coeff (-2 : ℤ) * F.coeff (-2 : ℤ)) := by
    rw [show (-8 / 9 : LaurentSeries k) * A * B * F =
        HahnSeries.C (-8 / 9 : k) * (A * B * F) from by
      rw [hcn89]; ring, hscale, hABF]
  have hq2 : ((8 / 9 : LaurentSeries k) * B ^ 2 * C).coeff (-6 : ℤ) =
      (8 / 9 : k) *
        (B.coeff (-1 : ℤ) * B.coeff (-2 : ℤ) * C.coeff (-3 : ℤ) +
          B.coeff (-2 : ℤ) * B.coeff (-1 : ℤ) * C.coeff (-3 : ℤ) +
          B.coeff (-2 : ℤ) * B.coeff (-2 : ℤ) * C.coeff (-2 : ℤ)) := by
    rw [show (8 / 9 : LaurentSeries k) * B ^ 2 * C =
        HahnSeries.C (8 / 9 : k) * (B * B * C) from by
      rw [hc89]; ring, hscale, hBBC]
  have hq3 : ((8 / 3 : LaurentSeries k) * C * G).coeff (-6 : ℤ) =
      (8 / 3 : k) * (C.coeff (-3 : ℤ) * G.coeff (-3 : ℤ) +
        C.coeff (-2 : ℤ) * G.coeff (-4 : ℤ)) := by
    rw [mul_assoc, hc83, hscale, hCG]
  have hq4 : ((-5 / 72 : LaurentSeries k) * HahnSeries.C beta * A ^ 2 *
      B).coeff (-6 : ℤ) =
      (-5 / 72 : k) * beta *
        (A.coeff (-2 : ℤ) * A.coeff (-2 : ℤ) * B.coeff (-2 : ℤ)) := by
    rw [show (-5 / 72 : LaurentSeries k) * HahnSeries.C beta * A ^ 2 * B =
        HahnSeries.C ((-5 / 72 : k) * beta) * (A * A * B) from by
      rw [map_mul, hcn572]; ring, hscale, hAAB]
  have hq5 : ((4 / 3 : LaurentSeries k) * F ^ 2).coeff (-6 : ℤ) =
      (4 / 3 : k) * (F.coeff (-3 : ℤ) * F.coeff (-3 : ℤ)) := by
    rw [show (4 / 3 : LaurentSeries k) * F ^ 2 =
        HahnSeries.C (4 / 3 : k) * (F * F) from by
      rw [hc43]; ring, hscale, hFF]
  have hq6 : ((5 / 6 : LaurentSeries k) * HahnSeries.C beta * A *
      F).coeff (-6 : ℤ) = 0 := by
    rw [show (5 / 6 : LaurentSeries k) * HahnSeries.C beta * A * F =
        HahnSeries.C ((5 / 6 : k) * beta) * (A * F) from by
      rw [map_mul, hc56]; ring, hscale, hzAF6, mul_zero]
  have hq7 : ((5 / 6 : LaurentSeries k) * HahnSeries.C beta * B *
      C).coeff (-6 : ℤ) = 0 := by
    rw [show (5 / 6 : LaurentSeries k) * HahnSeries.C beta * B * C =
        HahnSeries.C ((5 / 6 : k) * beta) * (B * C) from by
      rw [map_mul, hc56]; ring, hscale, hzBC6, mul_zero]
  have hq8 : ((1 / 2 : LaurentSeries k) * HahnSeries.C delta * A *
      B).coeff (-6 : ℤ) = 0 := by
    rw [show (1 / 2 : LaurentSeries k) * HahnSeries.C delta * A * B =
        HahnSeries.C ((1 / 2 : k) * delta) * (A * B) from by
      rw [map_mul, hc12]; ring, hscale, hzAB6, mul_zero]
  have hq9 : ((2 / 3 : LaurentSeries k) * HahnSeries.C gamma *
      B ^ 2).coeff (-6 : ℤ) = 0 := by
    rw [show (2 / 3 : LaurentSeries k) * HahnSeries.C gamma * B ^ 2 =
        HahnSeries.C ((2 / 3 : k) * gamma) * B ^ 2 from by
      rw [map_mul, hc23], hscale, hzB2at6, mul_zero]
  have hq10 : ((4 : LaurentSeries k) * HahnSeries.C gamma * G).coeff
      (-6 : ℤ) = 0 := by
    rw [show (4 : LaurentSeries k) * HahnSeries.C gamma * G =
        HahnSeries.C ((4 : k) * gamma) * G from by
      rw [map_mul, hc4], hscale, hG6, mul_zero]
  have hq11 : ((2 : LaurentSeries k) * HahnSeries.C epsilon * C).coeff
      (-6 : ℤ) = 0 := by
    rw [show (2 : LaurentSeries k) * HahnSeries.C epsilon * C =
        HahnSeries.C ((2 : k) * epsilon) * C from by
      rw [map_mul, hc2], hscale, hC6, mul_zero]
  have hq12 : ((3 : LaurentSeries k) * HahnSeries.C delta * F).coeff
      (-6 : ℤ) = 0 := by
    rw [show (3 : LaurentSeries k) * HahnSeries.C delta * F =
        HahnSeries.C ((3 : k) * delta) * F from by
      rw [map_mul, hc3], hscale, hF6, mul_zero]
  have hq13 : (B * HahnSeries.C zeta).coeff (-6 : ℤ) = 0 := by
    rw [mul_comm B (HahnSeries.C zeta), hscale, hB6, mul_zero]
  have h4dec := firstIntegralFour_mainTangent_decomposition68
    (k := LaurentSeries k) (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C epsilon) (HahnSeries.C zeta)
      A B C F G
  have h3dec := firstIntegralThree_mainTangent_decomposition68
    (k := LaurentSeries k) (HahnSeries.C beta) (HahnSeries.C gamma)
      (HahnSeries.C delta) (HahnSeries.C epsilon) (HahnSeries.C zeta)
      A B C F G
  constructor
  · rw [h4dec]
    simp only [firstIntegralFourMainTangentTop68,
      firstIntegralFourMainTangentLower68, HahnSeries.coeff_add,
      HahnSeries.coeff_sub]
    rw [hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12]
    simp only [rhoOneZeroLCubicMainTangentNextFour68]
    ring
  · rw [h3dec]
    simp only [firstIntegralThreeMainTangentTop68,
      firstIntegralThreeMainTangentLower68, HahnSeries.coeff_add,
      HahnSeries.coeff_sub]
    rw [hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9, hq10, hq11, hq12, hq13]
    simp only [rhoOneZeroLCubicMainTangentNextThree68]
    ring

set_option maxHeartbeats 1600000 in
/-- Source transport of the next I4/I3 coefficient pair on the main
tangent.  Only the canonical source packet and the differential main-tangent
relations are used; the improved tangent-defect orders are discharged by
`rhoOne_mainTangent_defect_orders` exactly as for the invariant rows. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_mainTangent_nextRows
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (P : RhoOneZeroLCubicNextSourcePacket68 T g u)
    (hmain :
      let A := ratFuncAtHahn46 T.root T.source.A
      let B := ratFuncAtHahn46 T.root T.source.B
      let C0 := ratFuncAtHahn46 T.root T.source.C0
      let D := ratFuncAtHahn46 T.root T.source.D
      let E := ratFuncAtHahn46 T.root T.source.E
      let C := rhoOneCDefectHahn68 A C0
      let ER := rhoOneEDefectHahn68 A E
      A.coeff (-2 : ℚ) * B.coeff (-2 : ℚ) = 3 * D.coeff (-4 : ℚ) ∧
      3 * ER.coeff (-5 : ℚ) = A.coeff (-2 : ℚ) * C.coeff (-3 : ℚ)) :
    let A := ratFuncAtHahn46 T.root T.source.A
    let B := ratFuncAtHahn46 T.root T.source.B
    let C0 := ratFuncAtHahn46 T.root T.source.C0
    let D := ratFuncAtHahn46 T.root T.source.D
    let E := ratFuncAtHahn46 T.root T.source.E
    let C := rhoOneCDefectHahn68 A C0
    let ER := rhoOneEDefectHahn68 A E
    let F := rhoOneTangentDDefectHahn68 A B D
    let G := rhoOneTangentEDefectHahn68 A C ER
    rhoOneZeroLCubicMainTangentNextFour68 T.source.beta
      (A.coeff (-2 : ℚ)) (A.coeff (-1 : ℚ))
      (B.coeff (-2 : ℚ)) (B.coeff (-1 : ℚ))
      (C.coeff (-3 : ℚ)) (C.coeff (-2 : ℚ))
      (F.coeff (-3 : ℚ)) (F.coeff (-2 : ℚ))
      (G.coeff (-4 : ℚ)) (G.coeff (-3 : ℚ)) = 0 ∧
    rhoOneZeroLCubicMainTangentNextThree68 T.source.beta
      (A.coeff (-2 : ℚ)) (A.coeff (-1 : ℚ))
      (B.coeff (-2 : ℚ)) (B.coeff (-1 : ℚ))
      (C.coeff (-3 : ℚ)) (C.coeff (-2 : ℚ))
      (F.coeff (-3 : ℚ)) (F.coeff (-2 : ℚ))
      (G.coeff (-4 : ℚ)) (G.coeff (-3 : ℚ)) = 0 := by
  have hord := T.rhoOne_mainTangent_defect_orders hp hH hp6 hp5 hp4 P hmain
  dsimp only at hord ⊢
  dsimp only [RhoOneZeroLCubicNextSourcePacket68,
    RhoOneZeroLCubicImprovedHahnBounds68] at P
  rcases P with ⟨P0, ⟨hA, hB, hC0, hC, hD, hE, hER⟩, hAne,
    htaut, h4old, h3old, hsplit⟩
  let AR : RatFunc k := T.source.A
  let BR : RatFunc k := T.source.B
  let C0R : RatFunc k := T.source.C0
  let DR : RatFunc k := T.source.D
  let E0R : RatFunc k := T.source.E
  let CR : RatFunc k := C0R - RatFunc.C (1 / 3 : k) * AR ^ 2
  let ERR : RatFunc k := E0R - RatFunc.C (1 / 27 : k) * AR ^ 3
  let FR : RatFunc k := DR - RatFunc.C (1 / 3 : k) * AR * BR
  let GR : RatFunc k := ERR - RatFunc.C (1 / 3 : k) * AR * CR
  have hCRmap : ratFuncAtHahn46 T.root CR =
      rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0) := by
    dsimp only [CR, C0R, AR, rhoOneCDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hERmap : ratFuncAtHahn46 T.root ERR =
      rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E) := by
    dsimp only [ERR, E0R, AR, rhoOneEDefectHahn68]
    simp only [map_sub, map_mul, map_pow, ratFuncAtHahn46_C]
  have hFRmap : ratFuncAtHahn46 T.root FR =
      rhoOneTangentDDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.B)
        (ratFuncAtHahn46 T.root T.source.D) := by
    dsimp only [FR, DR, AR, BR, rhoOneTangentDDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  have hGRmap : ratFuncAtHahn46 T.root GR =
      rhoOneTangentEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.C0))
        (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
          (ratFuncAtHahn46 T.root T.source.E)) := by
    rw [← hCRmap, ← hERmap]
    dsimp only [GR, AR, rhoOneTangentEDefectHahn68]
    simp only [map_sub, map_mul, ratFuncAtHahn46_C]
  let aL : LaurentSeries k := ratFuncAtLaurent46 T.root AR
  let bL : LaurentSeries k := ratFuncAtLaurent46 T.root BR
  let c0L : LaurentSeries k := ratFuncAtLaurent46 T.root C0R
  let dL : LaurentSeries k := ratFuncAtLaurent46 T.root DR
  let eL : LaurentSeries k := ratFuncAtLaurent46 T.root E0R
  let cL : LaurentSeries k := ratFuncAtLaurent46 T.root CR
  let fL : LaurentSeries k := ratFuncAtLaurent46 T.root FR
  let gL : LaurentSeries k := ratFuncAtLaurent46 T.root GR
  have haL : (↑(-2 : ℤ) : WithTop ℤ) ≤ aL.orderTop :=
    ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root AR (-2) hA
  have hbL : (↑(-2 : ℤ) : WithTop ℤ) ≤ bL.orderTop :=
    ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root BR (-2) hB
  have hcL : (↑(-3 : ℤ) : WithTop ℤ) ≤ cL.orderTop :=
    ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root CR (-3) (by
      rw [hCRmap]; exact hC)
  have hfL : (↑(-3 : ℤ) : WithTop ℤ) ≤ fL.orderTop :=
    ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root FR (-3) (by
      rw [hFRmap]; exact hord.1)
  have hgL : (↑(-4 : ℤ) : WithTop ℤ) ≤ gL.orderTop :=
    ratFuncAtLaurent46_orderTop_ge_of_hahn68 T.root GR (-4) (by
      rw [hGRmap]; exact hord.2)
  obtain ⟨i4, i3, hi4, hi3⟩ := integratedFirstIntegrals_exist_ground68
    T.source.A T.source.B T.source.C0 T.source.D T.source.E
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      0 T.source.alpha T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta T.source.eta (by
        simpa only [RatFunc.algebraMap_eq_C] using T.source.bracket_eq)
  have hi4L := congrArg (ratFuncAtLaurent46 T.root) hi4
  have hi4L' :
      firstIntegralFour68 0 aL bL c0L dL eL
          (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
          (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
          (HahnSeries.C T.source.zeta) = HahnSeries.C i4 := by
    dsimp only [aL, bL, c0L, dL, eL, AR, BR, C0R, DR, E0R]
    simpa only [firstIntegralFour68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_zero, map_one, RatFunc.algebraMap_eq_C,
      ratFuncAtLaurent46_C68] using hi4L
  have hi3L := congrArg (ratFuncAtLaurent46 T.root) hi3
  have hi3L' :
      firstIntegralThree68 0 aL bL c0L dL eL
          (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
          (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
          (HahnSeries.C T.source.zeta) = HahnSeries.C i3 := by
    dsimp only [aL, bL, c0L, dL, eL, AR, BR, C0R, DR, E0R]
    simpa only [firstIntegralThree68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_zero, map_one, RatFunc.algebraMap_eq_C,
      ratFuncAtLaurent46_C68] using hi3L
  have hthirdL : HahnSeries.C (1 / 3 : k) = (1 / 3 : LaurentSeries k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_one]
    simp only [map_ofNat]
  have h27L : HahnSeries.C (1 / 27 : k) = (1 / 27 : LaurentSeries k) := by
    rw [HahnSeries.C_eq_algebraMap, map_div₀, map_one]
    simp only [map_ofNat]
  have hCrecL : aL ^ 2 / 3 + cL = c0L := by
    dsimp only [aL, cL, c0L, CR, C0R, AR]
    simp only [map_sub, map_mul, map_pow, ratFuncAtLaurent46_C68]
    rw [hthirdL]
    ring
  have hDrecL : aL * bL / 3 + fL = dL := by
    dsimp only [aL, bL, fL, dL, FR, DR, AR, BR]
    simp only [map_sub, map_mul, ratFuncAtLaurent46_C68]
    rw [hthirdL]
    ring
  have hErecL : aL ^ 3 / 27 + aL * cL / 3 + gL = eL := by
    dsimp only [aL, cL, gL, eL, GR, ERR, CR, C0R, E0R, AR]
    simp only [map_sub, map_mul, map_pow, ratFuncAtLaurent46_C68]
    rw [hthirdL, h27L]
    ring
  have hface := firstIntegral_mainTangent_nonexceptionalNext_laurent68
    T.source.beta T.source.gamma T.source.delta T.source.epsilon
    T.source.zeta aL bL cL fL gL haL hbL hcL hfL hgL
  have h4coeff := congrArg (fun X : LaurentSeries k => X.coeff (-5 : ℤ)) hi4L'
  have h3coeff := congrArg (fun X : LaurentSeries k => X.coeff (-6 : ℤ)) hi3L'
  have h4const : (HahnSeries.C i4 : LaurentSeries k).coeff (-5 : ℤ) = 0 := by
    simp [HahnSeries.C_apply]
  have h3const : (HahnSeries.C i3 : LaurentSeries k).coeff (-6 : ℤ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [← hCrecL, ← hDrecL, ← hErecL, hface.1, h4const] at h4coeff
  rw [← hCrecL, ← hDrecL, ← hErecL, hface.2, h3const] at h3coeff
  have hrow4 : rhoOneZeroLCubicMainTangentNextFour68 T.source.beta
      (aL.coeff (-2 : ℤ)) (aL.coeff (-1 : ℤ))
      (bL.coeff (-2 : ℤ)) (bL.coeff (-1 : ℤ))
      (cL.coeff (-3 : ℤ)) (cL.coeff (-2 : ℤ))
      (fL.coeff (-3 : ℤ)) (fL.coeff (-2 : ℤ))
      (gL.coeff (-4 : ℤ)) (gL.coeff (-3 : ℤ)) = 0 :=
    (mul_eq_zero.mp h4coeff).resolve_left (by norm_num)
  have hrow3 : rhoOneZeroLCubicMainTangentNextThree68 T.source.beta
      (aL.coeff (-2 : ℤ)) (aL.coeff (-1 : ℤ))
      (bL.coeff (-2 : ℤ)) (bL.coeff (-1 : ℤ))
      (cL.coeff (-3 : ℤ)) (cL.coeff (-2 : ℤ))
      (fL.coeff (-3 : ℤ)) (fL.coeff (-2 : ℤ))
      (gL.coeff (-4 : ℤ)) (gL.coeff (-3 : ℤ)) = 0 :=
    (mul_eq_zero.mp h3coeff).resolve_left (by norm_num)
  have hbrA2 : (ratFuncAtHahn46 T.root T.source.A).coeff (-2 : ℚ) =
      (ratFuncAtLaurent46 T.root AR).coeff (-2 : ℤ) := by
    have h := ratFuncAtHahn46_coeff_int68 T.root T.source.A (-2)
    norm_num at h
    exact h
  have hbrA1 : (ratFuncAtHahn46 T.root T.source.A).coeff (-1 : ℚ) =
      (ratFuncAtLaurent46 T.root AR).coeff (-1 : ℤ) := by
    have h := ratFuncAtHahn46_coeff_int68 T.root T.source.A (-1)
    norm_num at h
    exact h
  have hbrB2 : (ratFuncAtHahn46 T.root T.source.B).coeff (-2 : ℚ) =
      (ratFuncAtLaurent46 T.root BR).coeff (-2 : ℤ) := by
    have h := ratFuncAtHahn46_coeff_int68 T.root T.source.B (-2)
    norm_num at h
    exact h
  have hbrB1 : (ratFuncAtHahn46 T.root T.source.B).coeff (-1 : ℚ) =
      (ratFuncAtLaurent46 T.root BR).coeff (-1 : ℤ) := by
    have h := ratFuncAtHahn46_coeff_int68 T.root T.source.B (-1)
    norm_num at h
    exact h
  have hbrC3 : (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff (-3 : ℚ) =
      (ratFuncAtLaurent46 T.root CR).coeff (-3 : ℤ) := by
    rw [← hCRmap]
    have h := ratFuncAtHahn46_coeff_int68 T.root CR (-3)
    norm_num at h
    exact h
  have hbrC2 : (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.C0)).coeff (-2 : ℚ) =
      (ratFuncAtLaurent46 T.root CR).coeff (-2 : ℤ) := by
    rw [← hCRmap]
    have h := ratFuncAtHahn46_coeff_int68 T.root CR (-2)
    norm_num at h
    exact h
  have hbrF3 : (rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff (-3 : ℚ) =
      (ratFuncAtLaurent46 T.root FR).coeff (-3 : ℤ) := by
    rw [← hFRmap]
    have h := ratFuncAtHahn46_coeff_int68 T.root FR (-3)
    norm_num at h
    exact h
  have hbrF2 : (rhoOneTangentDDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (ratFuncAtHahn46 T.root T.source.B)
      (ratFuncAtHahn46 T.root T.source.D)).coeff (-2 : ℚ) =
      (ratFuncAtLaurent46 T.root FR).coeff (-2 : ℤ) := by
    rw [← hFRmap]
    have h := ratFuncAtHahn46_coeff_int68 T.root FR (-2)
    norm_num at h
    exact h
  have hbrG4 : (rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-4 : ℚ) =
      (ratFuncAtLaurent46 T.root GR).coeff (-4 : ℤ) := by
    rw [← hGRmap]
    have h := ratFuncAtHahn46_coeff_int68 T.root GR (-4)
    norm_num at h
    exact h
  have hbrG3 : (rhoOneTangentEDefectHahn68
      (ratFuncAtHahn46 T.root T.source.A)
      (rhoOneCDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.C0))
      (rhoOneEDefectHahn68 (ratFuncAtHahn46 T.root T.source.A)
        (ratFuncAtHahn46 T.root T.source.E))).coeff (-3 : ℚ) =
      (ratFuncAtLaurent46 T.root GR).coeff (-3 : ℤ) := by
    rw [← hGRmap]
    have h := ratFuncAtHahn46_coeff_int68 T.root GR (-3)
    norm_num at h
    exact h
  rw [hbrA2, hbrA1, hbrB2, hbrB1, hbrC3, hbrC2, hbrF3, hbrF2, hbrG4, hbrG3]
  exact ⟨hrow4, hrow3⟩

/-- The consumed `c = 0` nonexceptional main-tangent limb: the original
limb data plus the next I4/I3 rows, the solved `g₃` jet, the `g₃`-free
`c₂, f₂` tie and its `g₄`-eliminated closed form. -/
def RhoOneAlignedSquareMainTangentCZeroConsumed68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let C := rhoOneCDefectHahn68 A C0
  let ER := rhoOneEDefectHahn68 A E
  let F := rhoOneTangentDDefectHahn68 A B D
  let G := rhoOneTangentEDefectHahn68 A C ER
  let a := A.coeff (-2 : ℚ)
  let a1 := A.coeff (-1 : ℚ)
  let b := B.coeff (-2 : ℚ)
  let b1 := B.coeff (-1 : ℚ)
  let c := C.coeff (-3 : ℚ)
  let c2 := C.coeff (-2 : ℚ)
  let d := D.coeff (-4 : ℚ)
  let e := ER.coeff (-5 : ℚ)
  let f := F.coeff (-3 : ℚ)
  let f2 := F.coeff (-2 : ℚ)
  let g4 := G.coeff (-4 : ℚ)
  let g3 := G.coeff (-3 : ℚ)
  RhoOneZeroLCubicNextSourcePacket68 T g u ∧
  (a * b = 3 * d ∧ 3 * e = a * c) ∧
  c = 0 ∧ b ≠ 0 ∧ f = 0 ∧
  -64 * b ^ 3 + 15 * T.source.beta * a ^ 3 + 576 * b * g4 = 0 ∧
  rhoOneZeroLCubicMainTangentNextFour68 T.source.beta
    a a1 b b1 c c2 f f2 g4 g3 = 0 ∧
  rhoOneZeroLCubicMainTangentNextThree68 T.source.beta
    a a1 b b1 c c2 f f2 g4 g3 = 0 ∧
  192 * b * g3 = 64 * b ^ 2 * b1 - 15 * T.source.beta * a ^ 2 * a1 -
    192 * b1 * g4 ∧
  64 * a * b * f2 + 64 * b ^ 2 * c2 - 192 * c2 * g4 +
    5 * T.source.beta * a ^ 2 * b = 0 ∧
  192 * a * b ^ 2 * f2 + 128 * b ^ 3 * c2 +
    15 * T.source.beta * a ^ 3 * c2 +
    15 * T.source.beta * a ^ 2 * b ^ 2 = 0

/-- The consumed `c ≠ 0, c² = a b²` nonexceptional main-tangent limb: the
original limb data, the wired-in nonzero reduction, the exact `f, g₄`
solves, the next I4/I3 rows and the `g₃`-eliminated compatibility tie. -/
def RhoOneAlignedSquareMainTangentNonzeroConsumed68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let C := rhoOneCDefectHahn68 A C0
  let ER := rhoOneEDefectHahn68 A E
  let F := rhoOneTangentDDefectHahn68 A B D
  let G := rhoOneTangentEDefectHahn68 A C ER
  let a := A.coeff (-2 : ℚ)
  let a1 := A.coeff (-1 : ℚ)
  let b := B.coeff (-2 : ℚ)
  let b1 := B.coeff (-1 : ℚ)
  let c := C.coeff (-3 : ℚ)
  let c2 := C.coeff (-2 : ℚ)
  let d := D.coeff (-4 : ℚ)
  let e := ER.coeff (-5 : ℚ)
  let f := F.coeff (-3 : ℚ)
  let f2 := F.coeff (-2 : ℚ)
  let g4 := G.coeff (-4 : ℚ)
  let g3 := G.coeff (-3 : ℚ)
  RhoOneZeroLCubicNextSourcePacket68 T g u ∧
  (a * b = 3 * d ∧ 3 * e = a * c) ∧
  c ≠ 0 ∧ b ≠ 0 ∧ a ≠ 0 ∧ c ^ 2 = a * b ^ 2 ∧
  rhoOneZeroLCubicMainTangentFour68 T.source.beta a b c f g4 = 0 ∧
  rhoOneZeroLCubicMainTangentThree68 a b c f g4 = 0 ∧
  3 * c * g4 = a * b * f + b ^ 2 * c ∧
  128 * b ^ 3 + 15 * T.source.beta * a ^ 3 + 768 * c * f = 0 ∧
  2304 * b * g4 = 640 * b ^ 3 - 15 * T.source.beta * a ^ 3 ∧
  rhoOneZeroLCubicMainTangentNextFour68 T.source.beta
    a a1 b b1 c c2 f f2 g4 g3 = 0 ∧
  rhoOneZeroLCubicMainTangentNextThree68 T.source.beta
    a a1 b b1 c c2 f f2 g4 g3 = 0 ∧
  90 * T.source.beta * a ^ 2 * a1 * c + 384 * a1 * b ^ 2 * f +
    768 * a * b * b1 * f + 768 * b ^ 2 * b1 * c +
    1536 * a * b ^ 2 * f2 - 128 * b ^ 3 * c2 -
    15 * T.source.beta * a ^ 3 * c2 +
    390 * T.source.beta * a ^ 2 * b ^ 2 - 576 * b * f ^ 2 = 0

/-- The early cubic sibling inventory with both nonexceptional
main-tangent limbs consumed.  The second component and the row-one
exceptional locus are preserved verbatim. -/
def RhoOneAlignedSquareEarlyCubicSiblingConsumed68
    {p q : k[X][X]} {j : k} {h0 : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (g u : k[X]) : Prop :=
  let A := ratFuncAtHahn46 T.root T.source.A
  let B := ratFuncAtHahn46 T.root T.source.B
  let C0 := ratFuncAtHahn46 T.root T.source.C0
  let D := ratFuncAtHahn46 T.root T.source.D
  let E := ratFuncAtHahn46 T.root T.source.E
  let b := B.coeff (-2 : ℚ)
  let c := (rhoOneCDefectHahn68 A C0).coeff (-3 : ℚ)
  let d := D.coeff (-4 : ℚ)
  let e := (rhoOneEDefectHahn68 A E).coeff (-5 : ℚ)
  RhoOneZeroLCubicSecondNextComponent68 T g u ∨
  (RhoOneZeroLCubicNextSourcePacket68 T g u ∧
    b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0) ∨
  RhoOneAlignedSquareMainTangentCZeroConsumed68 T g u ∨
  RhoOneAlignedSquareMainTangentNonzeroConsumed68 T g u

set_option maxHeartbeats 1600000 in
/-- Consuming the two nonexceptional main-tangent limbs of the early
cubic sibling.  All other components pass through verbatim. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_earlyCubicSibling_nonexceptional_consume
    {p q : k[X][X]} {j : k} {h0 H g u : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3)
    (hp5 : p.coeff 5 = h0 ^ 4 * g) (hp4 : p.coeff 4 = h0 ^ 2 * u)
    (hsib : RhoOneAlignedSquareEarlyCubicSibling68 T g u) :
    RhoOneAlignedSquareEarlyCubicSiblingConsumed68 T g u := by
  dsimp only [RhoOneAlignedSquareEarlyCubicSibling68,
    RhoOneAlignedSquareEarlyCubicSiblingConsumed68,
    RhoOneAlignedSquareMainTangentCZeroConsumed68,
    RhoOneAlignedSquareMainTangentNonzeroConsumed68] at hsib ⊢
  rcases hsib with hsecond | hrowex | ⟨P0, hmain, hlimb⟩
  · exact Or.inl hsecond
  · exact Or.inr (Or.inl hrowex)
  · have hnext := T.rhoOne_mainTangent_nextRows hp hH hp6 hp5 hp4 P0 hmain
    dsimp only at hnext
    rcases hlimb with ⟨hc, hb, hf, hrow⟩ | ⟨hc0, hb, hcsq, h4, h3⟩
    · have hred := rhoOneZeroLCubicMainTangentNext_cZero_reduction68
        T.source.beta _ _ _ _ _ _ _ _ _ _ hc hf hrow hnext.1 hnext.2
      exact Or.inr (Or.inr (Or.inl ⟨P0, hmain, hc, hb, hf, hrow,
        hnext.1, hnext.2, hred.1, hred.2.1, hred.2.2⟩))
    · have hnz := rhoOneZeroLCubicMainTangent_nonzero_reduced68
        T.source.beta _ _ _ _ _ hc0 hcsq h4 h3
      have hred := rhoOneZeroLCubicMainTangentNext_nonzero_reduction68
        T.source.beta _ _ _ _ _ _ _ _ _ _ hb hc0 hcsq hnz.1 hnz.2
        hnext.1 hnext.2
      exact Or.inr (Or.inr (Or.inr ⟨P0, hmain, hc0, hb, hred.1, hcsq,
        h4, h3, hnz.1, hnz.2, hred.2.1, hnext.1, hnext.2, hred.2.2⟩))

end AlignedSquareMainTangentNonexceptionalConsumer68

section AlignedSquareMainTangentNonexceptionalConsumerHierarchy68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The full aligned square-source inventory with the two nonexceptional
main-tangent limbs consumed.  The divisibility descent, the noncubic
packet, the second cubic component, the row-one exceptional locus and the
exceptional main entry are all preserved verbatim. -/
theorem SquareZeroLIntegratedLocalRootData68.rhoOne_alignedSquare_mainTangentNonexceptionalConsumerHierarchy
    {p q : k[X][X]} {j : k} {h0 H : k[X]}
    (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    ∃ g u : k[X],
      p.coeff 5 = h0 ^ 4 * g ∧ p.coeff 4 = h0 ^ 2 * u ∧
      ((h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧ h0 ∣ p.coeff 3) ∨
       RhoOneZeroLNoncubicSourcePacket68 T g u ∨
       RhoOneAlignedSquareEarlyCubicSiblingConsumed68 T g u ∨
       RhoOneAlignedSquareExceptionalMainEntry68 T g u) := by
  obtain ⟨g, u, hp5, hp4, hroutes⟩ :=
    T.rhoOne_alignedSquare_sourceSelectorHierarchy hp hH hp6
  refine ⟨g, u, hp5, hp4, ?_⟩
  rcases hroutes with hdesc | hnon | hsib | hentry
  · exact Or.inl hdesc
  · exact Or.inr (Or.inl hnon)
  · exact Or.inr (Or.inr (Or.inl
      (T.rhoOne_earlyCubicSibling_nonexceptional_consume
        hp hH hp6 hp5 hp4 hsib)))
  · exact Or.inr (Or.inr (Or.inr hentry))

/-- Normalized aligned-square source wrapper for the consumed hierarchy. -/
theorem normalized68ScaleTwo_alignedSquare_mainTangentNonexceptionalConsumerHierarchy
    {P Q : MvPolynomial (Fin 2) k} {H h0 : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    ∃ (j : k) (T : SquareZeroLIntegratedLocalRootData68 p q j h0)
        (g u : k[X]),
      p.coeff 5 = h0 ^ 4 * g ∧ p.coeff 4 = h0 ^ 2 * u ∧
      ((h0 ^ 5 ∣ p.coeff 5 ∧ h0 ^ 3 ∣ p.coeff 4 ∧ h0 ∣ p.coeff 3) ∨
       RhoOneZeroLNoncubicSourcePacket68 T g u ∨
       RhoOneAlignedSquareEarlyCubicSiblingConsumed68 T g u ∨
       RhoOneAlignedSquareExceptionalMainEntry68 T g u) := by
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hsource.2.2.1
  have hp6 : p.coeff 6 = H ^ 3 := by
    simpa only [p] using hsource.2.2.2.2.1
  obtain ⟨j, ⟨T⟩⟩ :=
    normalized68ScaleTwo_alignedSquareBranch_localRootData
      hsource hh0 hH haligned
  obtain ⟨g, u, hp5, hp4, hroutes⟩ :=
    T.rhoOne_alignedSquare_mainTangentNonexceptionalConsumerHierarchy
      hp hH hp6
  exact ⟨j, T, g, u, hp5, hp4, hroutes⟩

end AlignedSquareMainTangentNonexceptionalConsumerHierarchy68

end Max11DegreeRoutes
