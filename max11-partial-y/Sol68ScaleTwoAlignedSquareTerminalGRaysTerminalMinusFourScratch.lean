import Sol68ScaleTwoAlignedSquareTerminalGRaysSecondJetScratch

/-! # The genuine terminal coefficient minus four on the two nonzero rays -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section AlignedSquareTerminalGRaysTerminalMinusFour68

variable {k : Type*} [Field k] [CharZero k]

local instance terminalGRaysMinusFourLaurentCharZero68 :
    CharZero (LaurentSeries k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℤ))

theorem laurent_coeff_mul_three_lower_terminal68
    (X Y Z : LaurentSeries k) (m n r : ℤ)
    (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
    (hY : (↑n : WithTop ℤ) ≤ Y.orderTop)
    (hZ : (↑r : WithTop ℤ) ≤ Z.orderTop) :
    (X * Y * Z).coeff (m + n + r) =
      X.coeff m * Y.coeff n * Z.coeff r := by
  have hXY : (↑(m + n) : WithTop ℤ) ≤ (X * Y).orderTop :=
    le_trans (by simpa using add_le_add hX hY) HahnSeries.orderTop_add_le_mul
  rw [laurent_coeff_mul_lower68 (X * Y) Z (m + n) r hXY hZ,
    laurent_coeff_mul_lower68 X Y m n hX hY]

theorem laurent_coeff_mul_four_lower_succ_terminal68
    (X Y Z W : LaurentSeries k) (m n r s : ℤ)
    (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
    (hY : (↑n : WithTop ℤ) ≤ Y.orderTop)
    (hZ : (↑r : WithTop ℤ) ≤ Z.orderTop)
    (hW : (↑s : WithTop ℤ) ≤ W.orderTop) :
    (X * Y * Z * W).coeff (m + n + r + s + 1) =
      X.coeff (m + 1) * Y.coeff n * Z.coeff r * W.coeff s +
      X.coeff m * Y.coeff (n + 1) * Z.coeff r * W.coeff s +
      X.coeff m * Y.coeff n * Z.coeff (r + 1) * W.coeff s +
      X.coeff m * Y.coeff n * Z.coeff r * W.coeff (s + 1) := by
  have hXYZ : (↑(m + n + r) : WithTop ℤ) ≤ (X * Y * Z).orderTop := by
    have hXY : (↑(m + n) : WithTop ℤ) ≤ (X * Y).orderTop :=
      le_trans (by simpa using add_le_add hX hY) HahnSeries.orderTop_add_le_mul
    exact le_trans (by simpa using add_le_add hXY hZ)
      HahnSeries.orderTop_add_le_mul
  have hnext := laurent_coeff_mul_lower_succ68
    (X * Y * Z) W (m + n + r) s hXYZ hW
  have hzero := laurent_coeff_mul_three_lower_terminal68 X Y Z m n r hX hY hZ
  have hone := laurent_coeff_mul_three_lower_succ68 X Y Z m n r hX hY hZ
  rw [hzero, hone] at hnext
  convert hnext using 1 <;> ring

/-- At the actual ray orders, terminal coefficient `-4` is the old terminal
face and `I₄[1]`, plus one genuinely new `F[0]G[-1]` factor.  The unknown
next derivative coefficient of `A` occurs only against the old terminal
face, so no cleared-source derivative assumption is needed. -/
theorem rhoOneMainTangentTerminal_coeff_negFour_gRay68
    (gamma epsilon : k)
    (A B C F G dA dB dC dF dG : LaurentSeries k)
    (hA : (↑(-2 : ℤ) : WithTop ℤ) ≤ A.orderTop)
    (hB : (↑(1 : ℤ) : WithTop ℤ) ≤ B.orderTop)
    (hC : (0 : WithTop ℤ) ≤ C.orderTop)
    (hF : (0 : WithTop ℤ) ≤ F.orderTop)
    (hG : (↑(-1 : ℤ) : WithTop ℤ) ≤ G.orderTop)
    (hdA : (↑(-3 : ℤ) : WithTop ℤ) ≤ dA.orderTop)
    (hdB : (0 : WithTop ℤ) ≤ dB.orderTop)
    (hdC : (0 : WithTop ℤ) ≤ dC.orderTop)
    (hdF : (0 : WithTop ℤ) ≤ dF.orderTop)
    (hdG : (↑(-2 : ℤ) : WithTop ℤ) ≤ dG.orderTop)
    (hdAco : dA.coeff (-3 : ℤ) = (-2 : k) * A.coeff (-2 : ℤ)) :
    (rhoOneMainTangentTerminal68 (HahnSeries.C gamma)
      (HahnSeries.C epsilon) A B C F G dA dB dC dF dG).coeff (-4 : ℤ) =
      (2 / 27 : k) * A.coeff (-2 : ℤ) *
        (A.coeff (-2 : ℤ) *
            (4 * (B.coeff 1 * G.coeff 0 + B.coeff 2 * G.coeff (-1)) +
              2 * ((2 * C.coeff 0 + 3 * gamma) * F.coeff 1 +
                2 * C.coeff 1 * F.coeff 0) +
              3 * epsilon * B.coeff 1) +
          (2 * A.coeff (-1 : ℤ) - dA.coeff (-2 : ℤ)) *
            ((2 * C.coeff 0 + 3 * gamma) * F.coeff 0 +
              2 * B.coeff 1 * G.coeff (-1)) +
          12 * F.coeff 0 * G.coeff (-1)) := by
  have lower2 (X Y : LaurentSeries k) (m n : ℤ)
      (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
      (hY : (↑n : WithTop ℤ) ≤ Y.orderTop) :
      (↑(m + n) : WithTop ℤ) ≤ (X * Y).orderTop :=
    le_trans (by simpa using add_le_add hX hY) HahnSeries.orderTop_add_le_mul
  have lower3 (X Y Z : LaurentSeries k) (m n r : ℤ)
      (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
      (hY : (↑n : WithTop ℤ) ≤ Y.orderTop)
      (hZ : (↑r : WithTop ℤ) ≤ Z.orderTop) :
      (↑(m + n + r) : WithTop ℤ) ≤ (X * Y * Z).orderTop :=
    lower2 (X * Y) Z (m + n) r (lower2 X Y m n hX hY) hZ
  have lower4 (X Y Z W : LaurentSeries k) (m n r s : ℤ)
      (hX : (↑m : WithTop ℤ) ≤ X.orderTop)
      (hY : (↑n : WithTop ℤ) ≤ Y.orderTop)
      (hZ : (↑r : WithTop ℤ) ≤ Z.orderTop)
      (hW : (↑s : WithTop ℤ) ≤ W.orderTop) :
      (↑(m + n + r + s) : WithTop ℤ) ≤ (X * Y * Z * W).orderTop :=
    lower2 (X * Y * Z) W (m + n + r) s
      (lower3 X Y Z m n r hX hY hZ) hW
  have zero_of_lower (X : LaurentSeries k) (n : ℤ)
      (hX : (↑n : WithTop ℤ) ≤ X.orderTop) (hlt : (-4 : ℤ) < n) :
      X.coeff (-4 : ℤ) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hlt) hX)
  have h1 := zero_of_lower (F * dC) 0 (lower2 F dC 0 0 hF hdC) (by norm_num)
  have h2 := zero_of_lower (F * dA) (-3) (lower2 F dA 0 (-3) hF hdA)
    (by norm_num)
  have h3 := laurent_coeff_mul_three_lower_terminal68
    F G dA 0 (-1) (-3) hF hG hdA
  have h4 := zero_of_lower (F * F * dB) 0
    (lower3 F F dB 0 0 0 hF hF hdB) (by norm_num)
  have h5 := zero_of_lower (C * F * dC) 0
    (lower3 C F dC 0 0 0 hC hF hdC) (by norm_num)
  have h6 := zero_of_lower (B * dG) (-1)
    (lower2 B dG 1 (-2) hB hdG) (by norm_num)
  have h7 := zero_of_lower (B * F * dF) 1
    (lower3 B F dF 1 0 0 hB hF hdF) (by norm_num)
  have h8 := zero_of_lower (B * C * dG) (-1)
    (lower3 B C dG 1 0 (-2) hB hC hdG) (by norm_num)
  have h9 := zero_of_lower (B * C * dA) (-2)
    (lower3 B C dA 1 0 (-3) hB hC hdA) (by norm_num)
  have h10 := zero_of_lower (B * C * C * dA) (-2)
    (lower4 B C C dA 1 0 0 (-3) hB hC hC hdA) (by norm_num)
  have h11 := laurent_coeff_mul_three_lower_succ68
    A F dA (-2) 0 (-3) hA hF hdA
  have h12 := laurent_coeff_mul_four_lower_succ_terminal68
    A C F dA (-2) 0 0 (-3) hA hC hF hdA
  have h13 := laurent_coeff_mul_three_lower_terminal68
    A B dA (-2) 1 (-3) hA hB hdA
  have h14 := laurent_coeff_mul_four_lower_succ_terminal68
    A B G dA (-2) 1 (-1) (-3) hA hB hG hdA
  have h15 := zero_of_lower (A * B * F * dB) (-1)
    (lower4 A B F dB (-2) 1 0 0 hA hB hF hdB) (by norm_num)
  have h16 := zero_of_lower (A * B * B * dF) 0
    (lower4 A B B dF (-2) 1 1 0 hA hB hB hdF) (by norm_num)
  norm_num at h3 h11 h12 h13 h14
  have hscale (s : k) (X : LaurentSeries k) (n : ℤ) :
      (HahnSeries.C s * X).coeff n = s * X.coeff n := by
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
  have hrewrite :
      rhoOneMainTangentTerminal68 (HahnSeries.C gamma)
        (HahnSeries.C epsilon) A B C F G dA dB dC dF dG =
      HahnSeries.C (-(2 / 3 : k) * gamma) * (F * dC) +
      HahnSeries.C (-(1 / 3 : k) * epsilon) * (F * dA) +
      HahnSeries.C (-(4 / 9 : k)) * (F * G * dA) +
      HahnSeries.C (-(4 / 9 : k)) * (F * F * dB) +
      HahnSeries.C (-(4 / 9 : k)) * (C * F * dC) +
      HahnSeries.C ((2 / 3 : k) * gamma) * (B * dG) +
      HahnSeries.C (-(4 / 9 : k)) * (B * F * dF) +
      HahnSeries.C (4 / 9 : k) * (B * C * dG) +
      HahnSeries.C ((2 / 9 : k) * gamma) * (B * C * dA) +
      HahnSeries.C (4 / 27 : k) * (B * C * C * dA) +
      HahnSeries.C (-(2 / 9 : k) * gamma) * (A * F * dA) +
      HahnSeries.C (-(4 / 27 : k)) * (A * C * F * dA) +
      HahnSeries.C (-(1 / 9 : k) * epsilon) * (A * B * dA) +
      HahnSeries.C (-(4 / 27 : k)) * (A * B * G * dA) +
      HahnSeries.C (-(4 / 27 : k)) * (A * B * F * dB) +
      HahnSeries.C (-(4 / 27 : k)) * (A * B * B * dF) := by
    simp only [rhoOneMainTangentTerminal68, HahnSeries.C_eq_algebraMap,
      map_mul, map_neg, map_div₀, map_ofNat, map_one]
    ring
  rw [hrewrite]
  simp only [HahnSeries.coeff_add, hscale]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, hdAco]
  ring

/-- Algebraic dependence audit and its consequence: terminal `-4` is not
redundant; after removing the old terminal and `I₄[1]` rows it is exactly
the nonzero factor `F[0]G[-1]`, which contradicts either signed ray. -/
theorem rhoOneDoubleZero_gRay_terminal_negFour_impossible68
    (sigma r a a1 da2 b b2 c c1 f f1 g g0 gamma epsilon : k)
    (ha : a ≠ 0) (hg : g ≠ 0) (hsigma : sigma ^ 2 = 1)
    (hray : 3 * (2 * c + 3 * gamma) = 2 * sigma * r * b)
    (hlinear : r * f + 3 * sigma * g = 0)
    (hterminal : (2 * c + 3 * gamma) * f + 2 * b * g = 0)
    (hi4one : 4 * (b * g0 + b2 * g) +
      2 * ((2 * c + 3 * gamma) * f1 + 2 * c1 * f) +
      3 * epsilon * b = 0)
    (hminus4 : (2 / 27 : k) * a *
      (a * (4 * (b * g0 + b2 * g) +
          2 * ((2 * c + 3 * gamma) * f1 + 2 * c1 * f) +
          3 * epsilon * b) +
        (2 * a1 - da2) * ((2 * c + 3 * gamma) * f + 2 * b * g) +
        12 * f * g) = 0) : False := by
  have hconst : (2 / 27 : k) ≠ 0 := by norm_num
  have hinside : a * (4 * (b * g0 + b2 * g) +
          2 * ((2 * c + 3 * gamma) * f1 + 2 * c1 * f) +
          3 * epsilon * b) +
        (2 * a1 - da2) * ((2 * c + 3 * gamma) * f + 2 * b * g) +
        12 * f * g = 0 := by
    exact (mul_eq_zero.mp hminus4).resolve_left (mul_ne_zero hconst ha)
  have hfg : f * g = 0 := by
    linear_combination (1 / 12 : k) *
      (hinside - a * hi4one - (2 * a1 - da2) * hterminal)
  have hf : f = 0 := (mul_eq_zero.mp hfg).resolve_right hg
  have hsigma0 : sigma ≠ 0 := by
    intro hs
    subst sigma
    norm_num at hsigma
  simp only [hf, mul_zero, zero_add] at hlinear
  exact hg ((mul_eq_zero.mp hlinear).resolve_left
    (mul_ne_zero (by norm_num) hsigma0))

end AlignedSquareTerminalGRaysTerminalMinusFour68

end Max11DegreeRoutes
