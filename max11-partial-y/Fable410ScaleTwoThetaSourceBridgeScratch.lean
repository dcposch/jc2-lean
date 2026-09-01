import Fable410ScaleTwoIotaSourceBridgeScratch
import Fable410ScaleTwoIotaLinearPolarBranchScratch

/-! # Theta source bridge for the normalized `(4,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₃ H³ - 2 q₉ = λ h⁹` with
`h.natDegree = 1`, the ninth face isolated the degree-`4` Jacobian row
`5 S C' + 4 T B' + 3 U A' - B T' - 2 A U' - 4 W' = 0` and proved that
its first integral `θ` (`thetaResidual410`) is a differential constant,
but `θ` was never cleared against any jet: the ninth-face defect had
weight twenty-nine.  This file clears `θ` against the thirteenth-face
jet `p₃ = h³ t₂`, `p₂ = h² a₂₂`, `q₈ = h⁸ s₂₂`, `q₇ = h⁶ v`,
`q₆ = h⁵ w`, `q₅ = h⁴ u`, `q₄ = h² b₄₂`, `q₃ = h b₃₁` — the genuinely
unused degree-`4` exact mechanism.

First, the decic `z¹` coordinate of the affine depression is computed
(`affineDepress_degreeTen_coeff1_410`) and cleared on the ninth-power
face (`depressedW410_eq_cleared`).  On the thirteenth-face jet the
residual `θ` clears against `h³` exactly:
`16777216 h³ θ = Θ₃ + h (Θ₂ + h (Θ₁ + h Θ₀))` with explicit polynomial
blocks (`thetaDefect_eq_cleared410`).  Tracing `θ` through the affine
depression of the literal source and the degree-`4` row shows the
cleared defect is a scalar multiple of `h³`
(`nonzeroFace410_thetaResidualPowerRelation`).

Second, the power relation is peeled `h`-adically to the bottom
(`thetaBridge_fullPeel410`): cofactors `v₁, v₂, v₃` with `Θ₃ = h v₁`,
`v₁ + Θ₂ = h v₂`, `v₂ + Θ₁ = h v₃`, `v₃ + Θ₀ = C c_θ`, and the root
evaluations.

Third, the polar split of the iota bridge collapses.  On the
thirteenth-face root data the order-`-3` block of `θ` evaluates to
`-5242880 p₁(a)³` with no branch factor, so `Θ₃(a) = 0` forces
`p₁(a) = 0` unconditionally (`thetaBridge_pOneVanishes410`) — unlike
`ι`, whose order-`-3` coefficient carried the factor `λ + 4 t₂(a)`.
The bridge disjunction `p₁(a) = 0 ∨ λ + 4 t₂(a) = 0` therefore resolves
to its first branch on every nonzero face; the branch hypothesis
`λ + 4 t₂(a) = 0` is no longer needed for the residual tower.

Consequently all thirteenth-face jet letters vanish at the root
(`v(a) = w(a) = u(a) = b₄₂(a) = b₃₁(a) = q₂(a) = 0`), the order-`-2`
blocks of both towers vanish (`v₁(a) = 0`, `w₁(a) = 0`), and the next
unused source coefficient `q₁` is pinned twice: by the `θ` tower,
`v₂(a) + 16777216 q₁(a) = 0`, and by the `ι` tower,
`w₂(a) = 2 q₁(a) t₂(a)`.  The degree-`0` Keller row loses its `q₀'`
term, `p₀'(a) q₁(a) = j`, and eliminating `q₁(a)` links the literal
Keller constant to the `θ` cofactor:
`p₀'(a) v₂(a) + 16777216 j = 0`.

On the branch `λ + 4 t₂(a) = 0` requested by the split, the two towers
and the Keller row combine exactly:
`2 w₂(a) + λ q₁(a) = 0`, `33554432 w₂(a) = λ v₂(a)`, and
`2 p₀'(a) w₂(a) + λ j = 0`.

Nothing here closes the face or a branch: `p₁(a) = 0` eliminates no
configuration by itself, `t₂(a), a₂₂, s₂₂, q₁(a), q₀(a), c, c_θ, j,
p₀'(a), q₀'(a)` remain free or tied-not-determined, the ground
constants `α, β, γ, δ` are not touched, no total-degree or twice-prime
theorem is used, and the aligned face `N = 0` is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Decic `z¹` coefficient of the affine depression -/

section ThetaAffineCoeffOne410

variable {k : Type*} [Field k] [CharZero k]

/-- The `z¹` coefficient of the affine depression of a degree-ten
source. -/
theorem affineDepress_degreeTen_coeff1_410
    (p : (RatFunc k)[X]) (h r : RatFunc k) (hh : h ≠ 0)
    (hp10 : p.coeff 10 = h ^ 10)
    (hp_high : ∀ n, 10 < n → p.coeff n = 0) :
    (affineDepress68 h r p).coeff 1 =
      -10 * r ^ 9 + 9 * (p.coeff 9 / h ^ 9) * r ^ 8 -
        8 * (p.coeff 8 / h ^ 8) * r ^ 7 +
        7 * (p.coeff 7 / h ^ 7) * r ^ 6 -
        6 * (p.coeff 6 / h ^ 6) * r ^ 5 +
        5 * (p.coeff 5 / h ^ 5) * r ^ 4 -
        4 * (p.coeff 4 / h ^ 4) * r ^ 3 +
        3 * (p.coeff 3 / h ^ 3) * r ^ 2 -
        2 * (p.coeff 2 / h ^ 2) * r + p.coeff 1 / h := by
  let plow : (RatFunc k)[X] :=
    p - C (p.coeff 10) * X ^ 10 - C (p.coeff 9) * X ^ 9 -
      C (p.coeff 8) * X ^ 8 - C (p.coeff 7) * X ^ 7 -
      C (p.coeff 6) * X ^ 6 - C (p.coeff 5) * X ^ 5 -
      C (p.coeff 4) * X ^ 4 - C (p.coeff 3) * X ^ 3 -
      C (p.coeff 2) * X ^ 2 - C (p.coeff 1) * X ^ 1
  have hplow : ∀ n, 1 ≤ n → plow.coeff n = 0 := by
    intro n hn
    simp only [plow, coeff_sub, coeff_C_mul, coeff_X_pow]
    rcases Nat.eq_or_lt_of_le hn with h1 | hlt1
    · subst n; simp
    · have : 2 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with h2 | hlt2
      · subst n; simp
      · have : 3 ≤ n := by omega
        rcases Nat.eq_or_lt_of_le this with h3 | hlt3
        · subst n; simp
        · have : 4 ≤ n := by omega
          rcases Nat.eq_or_lt_of_le this with h4 | hlt4
          · subst n; simp
          · have : 5 ≤ n := by omega
            rcases Nat.eq_or_lt_of_le this with h5 | hlt5
            · subst n; simp
            · have : 6 ≤ n := by omega
              rcases Nat.eq_or_lt_of_le this with h6 | hlt6
              · subst n; simp
              · have : 7 ≤ n := by omega
                rcases Nat.eq_or_lt_of_le this with h7 | hlt7
                · subst n; simp
                · have : 8 ≤ n := by omega
                  rcases Nat.eq_or_lt_of_le this with h8 | hlt8
                  · subst n; simp
                  · have : 9 ≤ n := by omega
                    rcases Nat.eq_or_lt_of_le this with h9 | hlt9
                    · subst n; simp
                    · have : 10 ≤ n := by omega
                      rcases Nat.eq_or_lt_of_le this with h10 | hlt10
                      · subst n; simp [hp10]
                      · simp [hp_high n (by omega),
                          show n ≠ 10 by omega, show n ≠ 9 by omega,
                          show n ≠ 8 by omega, show n ≠ 7 by omega,
                          show n ≠ 6 by omega, show n ≠ 5 by omega,
                          show n ≠ 4 by omega, show n ≠ 3 by omega,
                          show n ≠ 2 by omega, show n ≠ 1 by omega]
  have hplowDeg : plow.natDegree ≤ 0 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
      intro n hn
      exact hplow n (by omega))
  have hp_split :
      p = C (p.coeff 10) * X ^ 10 + C (p.coeff 9) * X ^ 9 +
        C (p.coeff 8) * X ^ 8 + C (p.coeff 7) * X ^ 7 +
        C (p.coeff 6) * X ^ 6 + C (p.coeff 5) * X ^ 5 +
        C (p.coeff 4) * X ^ 4 + C (p.coeff 3) * X ^ 3 +
        C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X ^ 1 + plow := by
    simp only [plow]; ring
  have hq :
      affineDepress68 h r p =
        (C (p.coeff 10) * X ^ 10).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 9) * X ^ 9).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 8) * X ^ 8).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 7) * X ^ 7).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 6) * X ^ 6).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 5) * X ^ 5).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 4) * X ^ 4).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 3) * X ^ 3).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 2) * X ^ 2).comp ((X - C r) * C h⁻¹) +
          (C (p.coeff 1) * X ^ 1).comp ((X - C r) * C h⁻¹) +
          plow.comp ((X - C r) * C h⁻¹) := by
    have hdef : affineDepress68 h r p =
        p.comp ((X - C r) * C h⁻¹) := rfl
    have hsum (A B D E G H I J K M s t : (RatFunc k)[X]) :
        (A + B + D + E + G + H + I + J + K + M + s).comp t =
          A.comp t + B.comp t + D.comp t + E.comp t + G.comp t +
            H.comp t + I.comp t + J.comp t + K.comp t + M.comp t +
            s.comp t := by
      have h1 : (A + B + D + E + G + H + I + J + K + M + s).comp t =
          (A + B + D + E + G + H + I + J + K + M).comp t + s.comp t :=
        add_comp
      have h2 : (A + B + D + E + G + H + I + J + K + M).comp t =
          (A + B + D + E + G + H + I + J + K).comp t + M.comp t :=
        add_comp
      have h3 : (A + B + D + E + G + H + I + J + K).comp t =
          (A + B + D + E + G + H + I + J).comp t + K.comp t := add_comp
      have h4 : (A + B + D + E + G + H + I + J).comp t =
          (A + B + D + E + G + H + I).comp t + J.comp t := add_comp
      have h5 : (A + B + D + E + G + H + I).comp t =
          (A + B + D + E + G + H).comp t + I.comp t := add_comp
      have h6 : (A + B + D + E + G + H).comp t =
          (A + B + D + E + G).comp t + H.comp t := add_comp
      have h7 : (A + B + D + E + G).comp t =
          (A + B + D + E).comp t + G.comp t := add_comp
      have h8 : (A + B + D + E).comp t =
          (A + B + D).comp t + E.comp t := add_comp
      have h9 : (A + B + D).comp t = (A + B).comp t + D.comp t :=
        add_comp
      have h10 : (A + B).comp t = A.comp t + B.comp t := add_comp
      rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
    exact hdef.trans ((congrArg (fun t => t.comp ((X - C r) * C h⁻¹))
      hp_split).trans (hsum _ _ _ _ _ _ _ _ _ _ _ _))
  have hlow1 :
      (plow.comp ((X - C r) * C h⁻¹)).coeff 1 = 0 := by
    have hC : plow = C (plow.coeff 0) :=
      Polynomial.eq_C_of_natDegree_le_zero hplowDeg
    rw [hC, Polynomial.C_comp, Polynomial.coeff_C]
    simp
  have h10_1 :
      ((C (p.coeff 10) * X ^ 10).comp ((X - C r) * C h⁻¹)).coeff 1 =
        -10 * r ^ 9 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 10) h r 10 1 hh]
    have hle : (1 : ℕ) ≤ 10 := by omega
    have hbin : (10 : ℕ).choose 1 = 10 := by decide
    have hsub : (10 : ℕ) - 1 = 9 := by omega
    simp only [hle, ite_true, hp10, hbin, hsub]
    push_cast
    field_simp [hh]
  have h9_1 :
      ((C (p.coeff 9) * X ^ 9).comp ((X - C r) * C h⁻¹)).coeff 1 =
        9 * (p.coeff 9 / h ^ 9) * r ^ 8 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 9) h r 9 1 hh]
    have hle : (1 : ℕ) ≤ 9 := by omega
    have hbin : (9 : ℕ).choose 1 = 9 := by decide
    have hsub : (9 : ℕ) - 1 = 8 := by omega
    simp only [hle, ite_true, hbin, hsub]
    push_cast
    field_simp [hh]
  have h8_1 :
      ((C (p.coeff 8) * X ^ 8).comp ((X - C r) * C h⁻¹)).coeff 1 =
        -(8 * (p.coeff 8 / h ^ 8)) * r ^ 7 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 8) h r 8 1 hh]
    have hle : (1 : ℕ) ≤ 8 := by omega
    have hbin : (8 : ℕ).choose 1 = 8 := by decide
    have hsub : (8 : ℕ) - 1 = 7 := by omega
    simp only [hle, ite_true, hbin, hsub]
    push_cast
    field_simp [hh]
  have h7_1 :
      ((C (p.coeff 7) * X ^ 7).comp ((X - C r) * C h⁻¹)).coeff 1 =
        7 * (p.coeff 7 / h ^ 7) * r ^ 6 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 7) h r 7 1 hh]
    have hle : (1 : ℕ) ≤ 7 := by omega
    have hbin : (7 : ℕ).choose 1 = 7 := by decide
    have hsub : (7 : ℕ) - 1 = 6 := by omega
    simp only [hle, ite_true, hbin, hsub]
    push_cast
    field_simp [hh]
  have h6_1 :
      ((C (p.coeff 6) * X ^ 6).comp ((X - C r) * C h⁻¹)).coeff 1 =
        -(6 * (p.coeff 6 / h ^ 6)) * r ^ 5 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 6) h r 6 1 hh]
    have hle : (1 : ℕ) ≤ 6 := by omega
    have hbin : (6 : ℕ).choose 1 = 6 := by decide
    have hsub : (6 : ℕ) - 1 = 5 := by omega
    simp only [hle, ite_true, hbin, hsub]
    push_cast
    field_simp [hh]
  have h5_1 :
      ((C (p.coeff 5) * X ^ 5).comp ((X - C r) * C h⁻¹)).coeff 1 =
        5 * (p.coeff 5 / h ^ 5) * r ^ 4 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 5) h r 5 1 hh]
    have hle : (1 : ℕ) ≤ 5 := by omega
    have hbin : (5 : ℕ).choose 1 = 5 := by decide
    have hsub : (5 : ℕ) - 1 = 4 := by omega
    simp only [hle, ite_true, hbin, hsub]
    push_cast
    field_simp [hh]
  have h4_1 :
      ((C (p.coeff 4) * X ^ 4).comp ((X - C r) * C h⁻¹)).coeff 1 =
        -(4 * (p.coeff 4 / h ^ 4)) * r ^ 3 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 4) h r 4 1 hh]
    have hle : (1 : ℕ) ≤ 4 := by omega
    have hbin : (4 : ℕ).choose 1 = 4 := by decide
    have hsub : (4 : ℕ) - 1 = 3 := by omega
    simp only [hle, ite_true, hbin, hsub]
    push_cast
    field_simp [hh]
  have h3_1 :
      ((C (p.coeff 3) * X ^ 3).comp ((X - C r) * C h⁻¹)).coeff 1 =
        3 * (p.coeff 3 / h ^ 3) * r ^ 2 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 3) h r 3 1 hh]
    have hle : (1 : ℕ) ≤ 3 := by omega
    have hbin : (3 : ℕ).choose 1 = 3 := by decide
    have hsub : (3 : ℕ) - 1 = 2 := by omega
    simp only [hle, ite_true, hbin, hsub]
    push_cast
    field_simp [hh]
  have h2_1 :
      ((C (p.coeff 2) * X ^ 2).comp ((X - C r) * C h⁻¹)).coeff 1 =
        -(2 * (p.coeff 2 / h ^ 2)) * r := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 2) h r 2 1 hh]
    have hle : (1 : ℕ) ≤ 2 := by omega
    have hbin : (2 : ℕ).choose 1 = 2 := by decide
    have hsub : (2 : ℕ) - 1 = 1 := by omega
    simp only [hle, ite_true, hbin, hsub]
    push_cast
    field_simp [hh]
  have h1_1 :
      ((C (p.coeff 1) * X ^ 1).comp ((X - C r) * C h⁻¹)).coeff 1 =
        p.coeff 1 / h := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 1) h r 1 1 hh]
    have hle : (1 : ℕ) ≤ 1 := by omega
    have hbin : (1 : ℕ).choose 1 = 1 := by decide
    have hsub : (1 : ℕ) - 1 = 0 := by omega
    simp only [hle, ite_true, hbin, hsub, pow_zero, pow_one,
      Nat.cast_one, mul_one]
    rw [div_eq_mul_inv]
  rw [hq, coeff_add, coeff_add, coeff_add, coeff_add, coeff_add,
    coeff_add, coeff_add, coeff_add, coeff_add, coeff_add, h10_1, h9_1,
    h8_1, h7_1, h6_1, h5_1, h4_1, h3_1, h2_1, h1_1, hlow1]
  ring

end ThetaAffineCoeffOne410

/-! ## Exact `h³` clearing of `θ` on the thirteenth-face jet -/

section ThetaClearing410

variable {F : Type*} [Field F] [CharZero F]

/-- Exact denominator clearing for the depressed decic `z¹` coordinate
on the ninth-power face. -/
theorem depressedW410_eq_cleared
    (h a3 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a3 * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    depressedW410 h (quarticDepressionR410 h a3) b9 b8 b7 b6 b5 b4 b3
        b2 b1 =
      ((40 : F) * a3 ^ 9 * h ^ 2 - (9 : F) * lambda * a3 ^ 8 * h ^ 5 -
          (64 : F) * a3 ^ 7 * b8 + (224 : F) * a3 ^ 6 * b7 * h ^ 4 -
          (768 : F) * a3 ^ 5 * b6 * h ^ 8 +
          (2560 : F) * a3 ^ 4 * b5 * h ^ 12 -
          (8192 : F) * a3 ^ 3 * b4 * h ^ 16 +
          (24576 : F) * a3 ^ 2 * b3 * h ^ 20 -
          (65536 : F) * a3 * b2 * h ^ 24 +
          (131072 : F) * b1 * h ^ 28) /
        ((131072 : F) * h ^ 29) := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have hb9 : 2 * b9 = 5 * a3 * h ^ 6 - lambda * h ^ 9 := by
    linear_combination -hN
  have hb9div : b9 = (5 * a3 * h ^ 6 - lambda * h ^ 9) / 2 :=
    eq_div_of_mul_eq h2 (by rw [mul_comm]; exact hb9)
  rw [hb9div]
  simp only [depressedW410, quarticDepressionR410, quarticDepressionR46]
  field_simp [hh]
  ring

/-- Order-`-3` numerator block of the cleared `θ`: `16777216` times the
order-`-3` polar coefficient. -/
def thetaPolarThreeNumerator410 (vis a1 b42 : F[X]) : F[X] :=
  -(19660800 : F[X]) * a1 ^ 3 +
    (18350080 : F[X]) * a1 ^ 2 * vis -
    (16777216 : F[X]) * a1 * b42

/-- Order-`-2` numerator block of the cleared `θ`. -/
def thetaPolarTwoNumerator410 (t2 a22 s22 vis w73 q54 a1 b42 b31 b2 :
    F[X]) (lambda : F) : F[X] :=
  (58982400 : F[X]) * a1 ^ 2 * a22 * t2 +
    (26542080 : F[X]) * a1 ^ 2 * a22 * Polynomial.C lambda -
    (47185920 : F[X]) * a1 ^ 2 * s22 * t2 +
    (79872000 : F[X]) * a1 ^ 2 * t2 ^ 3 -
    (43130880 : F[X]) * a1 ^ 2 * t2 ^ 2 * Polynomial.C lambda -
    (82575360 : F[X]) * a1 * a22 * vis * t2 +
    (31457280 : F[X]) * a1 * a22 * w73 +
    (44728320 : F[X]) * a1 * vis * t2 ^ 3 -
    (35389440 : F[X]) * a1 * w73 * t2 ^ 2 +
    (26214400 : F[X]) * a1 * q54 * t2 +
    (20971520 : F[X]) * a22 * b42 * t2 -
    (12582912 : F[X]) * a22 * b31 -
    (7864320 : F[X]) * b42 * t2 ^ 3 +
    (7864320 : F[X]) * b31 * t2 ^ 2 -
    (8388608 : F[X]) * b2 * t2

/-- Order-`-1` numerator block of the cleared `θ`.  The next unused
source coefficient `q₁ = b₁` enters exactly once, with coefficient
`16777216`. -/
def thetaPolarOneNumerator410 (t2 a22 s22 vis w73 q54 a1 a0 b1 : F[X])
    (lambda : F) : F[X] :=
  -(117964800 : F[X]) * a0 * a1 * a22 +
    (41943040 : F[X]) * a0 * a1 * s22 -
    (73728000 : F[X]) * a0 * a1 * t2 ^ 2 +
    (53084160 : F[X]) * a0 * a1 * t2 * Polynomial.C lambda +
    (36700160 : F[X]) * a0 * a22 * vis -
    (41287680 : F[X]) * a0 * vis * t2 ^ 2 +
    (31457280 : F[X]) * a0 * w73 * t2 -
    (20971520 : F[X]) * a0 * q54 +
    (63897600 : F[X]) * a1 * a22 ^ 3 -
    (47185920 : F[X]) * a1 * a22 ^ 2 * s22 +
    (23961600 : F[X]) * a1 * a22 ^ 2 * t2 ^ 2 -
    (86261760 : F[X]) * a1 * a22 ^ 2 * t2 * Polynomial.C lambda +
    (153354240 : F[X]) * a1 * a22 * s22 * t2 ^ 2 -
    (254592000 : F[X]) * a1 * a22 * t2 ^ 4 +
    (122204160 : F[X]) * a1 * a22 * t2 ^ 3 * Polynomial.C lambda -
    (54312960 : F[X]) * a1 * s22 * t2 ^ 4 +
    (86136960 : F[X]) * a1 * t2 ^ 6 -
    (32078592 : F[X]) * a1 * t2 ^ 5 * Polynomial.C lambda -
    (13762560 : F[X]) * a22 ^ 3 * vis +
    (67092480 : F[X]) * a22 ^ 2 * vis * t2 ^ 2 -
    (35389440 : F[X]) * a22 ^ 2 * w73 * t2 +
    (13107200 : F[X]) * a22 ^ 2 * q54 -
    (47523840 : F[X]) * a22 * vis * t2 ^ 4 +
    (38338560 : F[X]) * a22 * w73 * t2 ^ 3 -
    (29491200 : F[X]) * a22 * q54 * t2 ^ 2 +
    (8316672 : F[X]) * vis * t2 ^ 6 -
    (8146944 : F[X]) * w73 * t2 ^ 5 +
    (7987200 : F[X]) * q54 * t2 ^ 4 +
    (16777216 : F[X]) * b1

/-- Regular (order-`0`) numerator block of the cleared `θ`. -/
def thetaRegularNumerator410 (t2 a22 s22 a0 : F[X]) (lambda : F) :
    F[X] :=
  -(11796480 : F[X]) * a0 ^ 2 * Polynomial.C lambda +
    (58982400 : F[X]) * a0 * a22 ^ 2 * t2 +
    (26542080 : F[X]) * a0 * a22 ^ 2 * Polynomial.C lambda -
    (94371840 : F[X]) * a0 * a22 * s22 * t2 +
    (159744000 : F[X]) * a0 * a22 * t2 ^ 3 -
    (86261760 : F[X]) * a0 * a22 * t2 ^ 2 * Polynomial.C lambda +
    (51118080 : F[X]) * a0 * s22 * t2 ^ 3 -
    (81469440 : F[X]) * a0 * t2 ^ 5 +
    (30551040 : F[X]) * a0 * t2 ^ 4 * Polynomial.C lambda -
    (31948800 : F[X]) * a22 ^ 4 * t2 -
    (7188480 : F[X]) * a22 ^ 4 * Polynomial.C lambda +
    (51118080 : F[X]) * a22 ^ 3 * s22 * t2 -
    (67891200 : F[X]) * a22 ^ 3 * t2 ^ 3 +
    (61102080 : F[X]) * a22 ^ 3 * t2 ^ 2 * Polynomial.C lambda -
    (108625920 : F[X]) * a22 ^ 2 * s22 * t2 ^ 3 +
    (178214400 : F[X]) * a22 ^ 2 * t2 ^ 5 -
    (80196480 : F[X]) * a22 ^ 2 * t2 ^ 4 * Polynomial.C lambda +
    (57028608 : F[X]) * a22 * s22 * t2 ^ 5 -
    (90168000 : F[X]) * a22 * t2 ^ 7 +
    (33415200 : F[X]) * a22 * t2 ^ 6 * Polynomial.C lambda -
    (8486400 : F[X]) * s22 * t2 ^ 7 +
    (12818000 : F[X]) * t2 ^ 9 -
    (4326075 : F[X]) * t2 ^ 8 * Polynomial.C lambda

/-- Polynomial numerator of `16777216 h³ θ` on the thirteenth-face jet,
in `h`-nested form. -/
def localClearedThetaResidual410 (h t2 a22 s22 vis w73 q54 a1 a0 b42
    b31 b2 b1 : F[X]) (lambda : F) : F[X] :=
  thetaPolarThreeNumerator410 vis a1 b42 +
    h * (thetaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1 b42 b31
        b2 lambda +
      h * (thetaPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b1
          lambda +
        h * thetaRegularNumerator410 t2 a22 s22 a0 lambda))

set_option maxHeartbeats 80000000 in
/-- Exact `h³` clearing of the ninth-face residual `θ` on the
thirteenth-face jet substitutions. -/
theorem thetaDefect_eq_cleared410
    (h t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 b1 b9 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * (h ^ 3 * t2) * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    (16777216 : F) * h ^ 3 *
        thetaResidual410
          (depressedL410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9)
          (depressedA410 h (quarticDepressionR410 h (h ^ 3 * t2))
            (h ^ 3 * t2) (h ^ 2 * a22))
          (depressedB410 h (quarticDepressionR410 h (h ^ 3 * t2))
            (h ^ 3 * t2) (h ^ 2 * a22) a1)
          (depressedC410 h (quarticDepressionR410 h (h ^ 3 * t2))
            (h ^ 3 * t2) (h ^ 2 * a22) a1 a0)
          (depressedP410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
            (h ^ 8 * s22))
          (depressedQ410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
            (h ^ 8 * s22) (h ^ 6 * vis))
          (depressedR410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
            (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73))
          (depressedS410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
            (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54))
          (depressedT410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
            (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
            (h ^ 2 * b42))
          (depressedU410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
            (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
            (h ^ 2 * b42) (h * b31))
          (depressedW410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
            (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
            (h ^ 2 * b42) (h * b31) b2 b1) =
      (-(19660800 : F) * a1 ^ 3 +
          (18350080 : F) * a1 ^ 2 * vis -
          (16777216 : F) * a1 * b42) +
        h * (((58982400 : F) * a1 ^ 2 * a22 * t2 +
            (26542080 : F) * a1 ^ 2 * a22 * lambda -
            (47185920 : F) * a1 ^ 2 * s22 * t2 +
            (79872000 : F) * a1 ^ 2 * t2 ^ 3 -
            (43130880 : F) * a1 ^ 2 * t2 ^ 2 * lambda -
            (82575360 : F) * a1 * a22 * vis * t2 +
            (31457280 : F) * a1 * a22 * w73 +
            (44728320 : F) * a1 * vis * t2 ^ 3 -
            (35389440 : F) * a1 * w73 * t2 ^ 2 +
            (26214400 : F) * a1 * q54 * t2 +
            (20971520 : F) * a22 * b42 * t2 -
            (12582912 : F) * a22 * b31 -
            (7864320 : F) * b42 * t2 ^ 3 +
            (7864320 : F) * b31 * t2 ^ 2 -
            (8388608 : F) * b2 * t2) +
          h * ((-(117964800 : F) * a0 * a1 * a22 +
              (41943040 : F) * a0 * a1 * s22 -
              (73728000 : F) * a0 * a1 * t2 ^ 2 +
              (53084160 : F) * a0 * a1 * t2 * lambda +
              (36700160 : F) * a0 * a22 * vis -
              (41287680 : F) * a0 * vis * t2 ^ 2 +
              (31457280 : F) * a0 * w73 * t2 -
              (20971520 : F) * a0 * q54 +
              (63897600 : F) * a1 * a22 ^ 3 -
              (47185920 : F) * a1 * a22 ^ 2 * s22 +
              (23961600 : F) * a1 * a22 ^ 2 * t2 ^ 2 -
              (86261760 : F) * a1 * a22 ^ 2 * t2 * lambda +
              (153354240 : F) * a1 * a22 * s22 * t2 ^ 2 -
              (254592000 : F) * a1 * a22 * t2 ^ 4 +
              (122204160 : F) * a1 * a22 * t2 ^ 3 * lambda -
              (54312960 : F) * a1 * s22 * t2 ^ 4 +
              (86136960 : F) * a1 * t2 ^ 6 -
              (32078592 : F) * a1 * t2 ^ 5 * lambda -
              (13762560 : F) * a22 ^ 3 * vis +
              (67092480 : F) * a22 ^ 2 * vis * t2 ^ 2 -
              (35389440 : F) * a22 ^ 2 * w73 * t2 +
              (13107200 : F) * a22 ^ 2 * q54 -
              (47523840 : F) * a22 * vis * t2 ^ 4 +
              (38338560 : F) * a22 * w73 * t2 ^ 3 -
              (29491200 : F) * a22 * q54 * t2 ^ 2 +
              (8316672 : F) * vis * t2 ^ 6 -
              (8146944 : F) * w73 * t2 ^ 5 +
              (7987200 : F) * q54 * t2 ^ 4 +
              (16777216 : F) * b1) +
            h * (-(11796480 : F) * a0 ^ 2 * lambda +
              (58982400 : F) * a0 * a22 ^ 2 * t2 +
              (26542080 : F) * a0 * a22 ^ 2 * lambda -
              (94371840 : F) * a0 * a22 * s22 * t2 +
              (159744000 : F) * a0 * a22 * t2 ^ 3 -
              (86261760 : F) * a0 * a22 * t2 ^ 2 * lambda +
              (51118080 : F) * a0 * s22 * t2 ^ 3 -
              (81469440 : F) * a0 * t2 ^ 5 +
              (30551040 : F) * a0 * t2 ^ 4 * lambda -
              (31948800 : F) * a22 ^ 4 * t2 -
              (7188480 : F) * a22 ^ 4 * lambda +
              (51118080 : F) * a22 ^ 3 * s22 * t2 -
              (67891200 : F) * a22 ^ 3 * t2 ^ 3 +
              (61102080 : F) * a22 ^ 3 * t2 ^ 2 * lambda -
              (108625920 : F) * a22 ^ 2 * s22 * t2 ^ 3 +
              (178214400 : F) * a22 ^ 2 * t2 ^ 5 -
              (80196480 : F) * a22 ^ 2 * t2 ^ 4 * lambda +
              (57028608 : F) * a22 * s22 * t2 ^ 5 -
              (90168000 : F) * a22 * t2 ^ 7 +
              (33415200 : F) * a22 * t2 ^ 6 * lambda -
              (8486400 : F) * s22 * t2 ^ 7 +
              (12818000 : F) * t2 ^ 9 -
              (4326075 : F) * t2 ^ 8 * lambda))) := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h128 : (128 : F) ≠ 0 := by norm_num
  have h256 : (256 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h131072 : (131072 : F) ≠ 0 := by norm_num
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  have hh3 : h ^ 3 ≠ 0 := pow_ne_zero 3 hh
  have hL :
      depressedL410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9 =
        -lambda / 2 :=
    depressedL410_eq_of_ninthPower h (h ^ 3 * t2) b9 lambda hh hN
  have hA :
      depressedA410 h (quarticDepressionR410 h (h ^ 3 * t2))
          (h ^ 3 * t2) (h ^ 2 * a22) =
        (8 * a22 - 3 * t2 ^ 2) / 8 := by
    rw [depressedA410_eq_cleared h (h ^ 3 * t2) (h ^ 2 * a22) hh]
    field_simp [hh]
  have hB :
      depressedB410 h (quarticDepressionR410 h (h ^ 3 * t2))
          (h ^ 3 * t2) (h ^ 2 * a22) a1 =
        (8 * a1 - 4 * a22 * h * t2 + h * t2 ^ 3) / (8 * h) := by
    rw [depressedB410_eq_cleared h (h ^ 3 * t2) (h ^ 2 * a22) a1 hh]
    field_simp [hh]
    ring
  have hC :
      depressedC410 h (quarticDepressionR410 h (h ^ 3 * t2))
          (h ^ 3 * t2) (h ^ 2 * a22) a1 a0 =
        (256 * a0 * h - 64 * a1 * t2 + 16 * a22 * h * t2 ^ 2 -
            3 * h * t2 ^ 4) / (256 * h) := by
    rw [depressedC410_eq_cleared h (h ^ 3 * t2) (h ^ 2 * a22) a1 a0 hh]
    field_simp [hh]
  have hP :
      depressedP410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
          (h ^ 8 * s22) =
        (18 * lambda * t2 + 16 * s22 - 45 * t2 ^ 2) / 16 := by
    rw [depressedP410_eq_cleared_ninthPower h (h ^ 3 * t2) b9
      (h ^ 8 * s22) lambda hh hN]
    field_simp [hh]
    ring
  have hQ :
      depressedQ410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
          (h ^ 8 * s22) (h ^ 6 * vis) =
        (-(9 : F) * h * lambda * t2 ^ 2 - 16 * h * s22 * t2 +
            30 * h * t2 ^ 3 + 8 * vis) / (8 * h) := by
    rw [depressedQ410_eq_cleared h (h ^ 3 * t2) b9 (h ^ 8 * s22)
      (h ^ 6 * vis) lambda hh hN]
    field_simp [hh]
    ring
  have hR :
      depressedR410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
          (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) =
        (84 * h * lambda * t2 ^ 3 + 224 * h * s22 * t2 ^ 2 -
            315 * h * t2 ^ 4 - 224 * t2 * vis + 128 * w73) /
          (128 * h) := by
    rw [depressedR410_eq_cleared h (h ^ 3 * t2) b9 (h ^ 8 * s22)
      (h ^ 6 * vis) (h ^ 5 * w73) lambda hh hN]
    field_simp [hh]
    ring
  have hS :
      depressedS410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
          (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54) =
        (-(63 : F) * h * lambda * t2 ^ 4 - 224 * h * s22 * t2 ^ 3 +
            252 * h * t2 ^ 5 + 256 * q54 + 336 * t2 ^ 2 * vis -
            384 * t2 * w73) / (256 * h) := by
    rw [depressedS410_eq_cleared h (h ^ 3 * t2) b9 (h ^ 8 * s22)
      (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54) lambda hh hN]
    field_simp [hh]
    ring
  have hT :
      depressedT410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
          (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
          (h ^ 2 * b42) =
        (2048 * b42 + 126 * h ^ 2 * lambda * t2 ^ 5 +
            560 * h ^ 2 * s22 * t2 ^ 4 - 525 * h ^ 2 * t2 ^ 6 -
            2560 * h * q54 * t2 - 1120 * h * t2 ^ 3 * vis +
            1920 * h * t2 ^ 2 * w73) / (2048 * h ^ 2) := by
    rw [depressedT410_eq_cleared h (h ^ 3 * t2) b9 (h ^ 8 * s22)
      (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54) (h ^ 2 * b42) lambda hh
      hN]
    field_simp [hh]
    ring
  have hU :
      depressedU410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
          (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
          (h ^ 2 * b42) (h * b31) =
        (2048 * b31 - 2048 * b42 * t2 - 21 * h ^ 2 * lambda * t2 ^ 6 -
            112 * h ^ 2 * s22 * t2 ^ 5 + 90 * h ^ 2 * t2 ^ 7 +
            1280 * h * q54 * t2 ^ 2 + 280 * h * t2 ^ 4 * vis -
            640 * h * t2 ^ 3 * w73) / (2048 * h ^ 2) := by
    rw [depressedU410_eq_cleared h (h ^ 3 * t2) b9 (h ^ 8 * s22)
      (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54) (h ^ 2 * b42)
      (h * b31) lambda hh hN]
    field_simp [hh]
    ring
  have hW0 :
      depressedW410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
          (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
          (h ^ 2 * b42) (h * b31) b2 b1 =
        (-(65536 : F) * b2 * t2 + 24576 * b31 * t2 ^ 2 -
            8192 * b42 * t2 ^ 3 + 131072 * b1 * h +
            2560 * h * q54 * t2 ^ 4 + 224 * h * t2 ^ 6 * vis -
            768 * h * t2 ^ 5 * w73 + 40 * h ^ 2 * t2 ^ 9 -
            9 * h ^ 2 * lambda * t2 ^ 8 -
            64 * h ^ 2 * s22 * t2 ^ 7) / (131072 * h ^ 2) := by
    rw [depressedW410_eq_cleared h (h ^ 3 * t2) b9 (h ^ 8 * s22)
      (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54) (h ^ 2 * b42)
      (h * b31) b2 b1 lambda hh hN]
    field_simp [hh]
    ring
  simp only [thetaResidual410, alphaResidual410, betaResidual410,
    gammaResidual410, deltaResidual410, epsilonResidual410,
    zetaResidual410, hL, hA, hB, hC, hP, hQ, hR, hS, hT, hU, hW0]
  field_simp [hh]
  ring

end ThetaClearing410

/-! ## Source-facing power relation -/

section NonzeroThetaBridge410

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

set_option maxHeartbeats 80000000 in
/-- The ninth-face residual `θ` on a square-core ninth-power source is
a differential constant of the degree-`4` Jacobian row, and on the
thirteenth-face jet its cleared defect is a scalar times `h³`. -/
theorem nonzeroFace410_thetaResidualPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (t2 a22 s22 vis w73 q54 b42 b31 : k[X])
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hp3 : p.coeff 3 = h0 ^ 3 * t2) (hp2 : p.coeff 2 = h0 ^ 2 * a22)
    (hq8 : q.coeff 8 = h0 ^ 8 * s22) (hq7 : q.coeff 7 = h0 ^ 6 * vis)
    (hq6 : q.coeff 6 = h0 ^ 5 * w73) (hq5 : q.coeff 5 = h0 ^ 4 * q54)
    (hq4 : q.coeff 4 = h0 ^ 2 * b42) (hq3 : q.coeff 3 = h0 * b31) :
    ∃ c : k,
      localClearedThetaResidual410 h0 t2 a22 s22 vis w73 q54
          (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1)
          lambda =
        Polynomial.C c * h0 ^ 3 := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let a1 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 1)
  let a0 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 0)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
  let b7 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
  let b6 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 6)
  let b5 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 5)
  let b4 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 4)
  let b3 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 3)
  let b2 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 2)
  let b1 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 1)
  let t2R : RatFunc k := algebraMap k[X] (RatFunc k) t2
  let a22R : RatFunc k := algebraMap k[X] (RatFunc k) a22
  let s22R : RatFunc k := algebraMap k[X] (RatFunc k) s22
  let visR : RatFunc k := algebraMap k[X] (RatFunc k) vis
  let w73R : RatFunc k := algebraMap k[X] (RatFunc k) w73
  let q54R : RatFunc k := algebraMap k[X] (RatFunc k) q54
  let b42R : RatFunc k := algebraMap k[X] (RatFunc k) b42
  let b31R : RatFunc k := algebraMap k[X] (RatFunc k) b31
  have hh : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 4) = hRF ^ 4 := by
    simp only [hp4, hH, hRF, map_pow]
    ring
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = hRF ^ 10 := by
    simp only [hq10, hH, hRF, map_pow]
    ring
  have hpDep :
      affineDepress68 hRF (quarticDepressionR410 hRF a3)
          (sourceToRatFunc68 p) =
        depressedQuartic46
          (depressedA46 hRF (quarticDepressionR410 hRF a3) a3 a2)
          (depressedB46 hRF (quarticDepressionR410 hRF a3) a3 a2 a1)
          (depressedC46 hRF (quarticDepressionR410 hRF a3) a3 a2 a1
            a0) := by
    change affineDepress46 hRF (quarticDepressionR410 hRF a3)
        (sourceToRatFunc46 p) = _
    exact affineDepress_sourceQuartic46 p hRF
      (quarticDepressionR410 hRF a3) hp hh hpTop
      (by simp [a3, quarticDepressionR410])
  have hNrat : 5 * a3 * hRF ^ 6 - 2 * b9 = RatFunc.C lambda * hRF ^ 9 := by
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hN
    have hH3 : algebraMap k[X] (RatFunc k) (H ^ 3) = hRF ^ 6 := by
      simp only [hH, hRF, map_pow]
      ring
    have hh9 : algebraMap k[X] (RatFunc k) (h0 ^ 9) = hRF ^ 9 := by
      simp only [hRF, map_pow]
    have hleft : algebraMap k[X] (RatFunc k)
        ((5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9) =
        5 * a3 * hRF ^ 6 - 2 * b9 := by
      simp only [map_sub, map_mul, map_ofNat, a3, b9, hH3]
    have hright : algebraMap k[X] (RatFunc k)
        (Polynomial.C lambda * h0 ^ 9) =
        RatFunc.C lambda * hRF ^ 9 := by
      simp only [map_mul, RatFunc.algebraMap_C, hh9]
    exact hleft.symm.trans (hmapped.trans hright)
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j hRF (quarticDepressionR410 hRF a3) hh hD
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (quarticDepressionR410 hRF a3)
      (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (quarticDepressionR410 hRF a3)
      (sourceToRatFunc68 q)
  have hf3 : f.coeff 3 = 0 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedQuartic46_three]
  have hf4 : f.coeff 4 = 1 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedQuartic46_four]
  have hf_high : ∀ n, 4 < n → f.coeff n = 0 := by
    intro n hn
    dsimp only [f]
    rw [hpDep, coeff_depressedQuartic46_of_gt_four _ _ _ hn]
  have hg_high_src : ∀ n, 10 < n → (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = hRF ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) hRF
      (quarticDepressionR410 hRF a3) hh hgTop hg_high_src
  have hg7 :
      g.coeff 7 =
        depressedQ410 hRF (quarticDepressionR410 hRF a3) b9 b8 b7 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff7_810 (sourceToRatFunc68 q) hRF
      (quarticDepressionR410 hRF a3) hh hgTop hg_high_src]
    simp [depressedQ410, depressedQ810, quarticDepressionR410,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8, b7]
  have hg6 :
      g.coeff 6 =
        depressedR410 hRF (quarticDepressionR410 hRF a3) b9 b8 b7
          b6 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff6_410 (sourceToRatFunc68 q) hRF
      (quarticDepressionR410 hRF a3) hh hgTop hg_high_src]
    simp [depressedR410, quarticDepressionR410, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6]
  have hg5 :
      g.coeff 5 =
        depressedS410 hRF (quarticDepressionR410 hRF a3) b9 b8 b7 b6
          b5 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff5_410 (sourceToRatFunc68 q) hRF
      (quarticDepressionR410 hRF a3) hh hgTop hg_high_src]
    simp [depressedS410, quarticDepressionR410, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5]
  have hg4 :
      g.coeff 4 =
        depressedT410 hRF (quarticDepressionR410 hRF a3) b9 b8 b7 b6
          b5 b4 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff4_410 (sourceToRatFunc68 q) hRF
      (quarticDepressionR410 hRF a3) hh hgTop hg_high_src]
    simp [depressedT410, quarticDepressionR410, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4]
  have hg3 :
      g.coeff 3 =
        depressedU410 hRF (quarticDepressionR410 hRF a3) b9 b8 b7 b6
          b5 b4 b3 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff3_410 (sourceToRatFunc68 q) hRF
      (quarticDepressionR410 hRF a3) hh hgTop hg_high_src]
    simp [depressedU410, quarticDepressionR410, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3]
  have hg1 :
      g.coeff 1 =
        depressedW410 hRF (quarticDepressionR410 hRF a3) b9 b8 b7 b6
          b5 b4 b3 b2 b1 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff1_410 (sourceToRatFunc68 q) hRF
      (quarticDepressionR410 hRF a3) hh hgTop hg_high_src]
    simp [depressedW410, quarticDepressionR410, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2, b1]
  have hg8' :
      g.coeff 8 =
        depressedP410 hRF (quarticDepressionR410 hRF a3) b9 b8 := by
    dsimp only [g]
    rw [hg8]
    simp [depressedP410, depressedP810, quarticDepressionR410,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8]
  have hg9L :
      g.coeff 9 =
        depressedL410 hRF (quarticDepressionR410 hRF a3) b9 := by
    dsimp only [g]
    rw [hg9]
    simp [depressedL410, depressedL810, quarticDepressionR410,
      sourceToRatFunc68, sourceToRatFunc46, b9]
  have hLval :
      depressedL410 hRF (quarticDepressionR410 hRF a3) b9 =
        RatFunc.C (-lambda / 2) := by
    have hL := depressedL410_eq_of_ninthPower hRF a3 b9
      (RatFunc.C lambda) hh (by simpa using hNrat)
    simpa [map_neg, map_div₀, map_ofNat] using hL
  have hg9' : g.coeff 9 = RatFunc.C (-lambda / 2) := by
    rw [hg9L, hLval]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hg9']
    have hx := ratFuncDerivation46_polynomial (C (-lambda / 2) : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hrow11 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 2) -
        (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 8) = 0 := by
    have hrow :=
      differentialJacobian_coeff_11_monicQuarticDecic
        ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 11) hbracket
    simpa [f, g, Polynomial.coeff_C, show (11 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow10 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 1) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 2) -
        (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 7) = 0 := by
    have hrow :=
      differentialJacobian_coeff_10_monicQuarticDecic
        ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 10) hbracket
    simpa [f, g, Polynomial.coeff_C, show (10 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow9 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 0) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 1) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 2) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 8) -
          (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 6) = 0 := by
    have hrow :=
      differentialJacobian_coeff_9_monicQuarticDecic
        ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 9) hbracket
    simpa [f, g, Polynomial.coeff_C, show (9 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow8 :
      (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 0) +
          (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 1) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 2) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 8) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 7) -
          (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 5) = 0 := by
    have hrow :=
      differentialJacobian_coeff_8_monicQuarticDecic
        ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 8) hbracket
    simpa [f, g, Polynomial.coeff_C, show (8 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow7 :
      (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 0) +
          (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 1) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 2) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 7) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 6) -
          (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 4) = 0 := by
    have hrow :=
      differentialJacobian_coeff_7_monicQuarticDecic
        ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 7) hbracket
    simpa [f, g, Polynomial.coeff_C, show (7 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow6 :
      (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 0) +
          (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 1) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 2) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 6) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 5) -
          (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 3) = 0 := by
    have hrow :=
      differentialJacobian_coeff_6_monicQuarticDecic
        ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 6) hbracket
    simpa [f, g, Polynomial.coeff_C, show (6 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow4 :
      (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 0) +
          (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 1) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 2) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 4) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 3) -
          (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 1) = 0 := by
    have hrow :=
      differentialJacobian_coeff_4_monicQuarticDecic
        ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 4) hbracket
    simpa [f, g, Polynomial.coeff_C, show (4 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hf2 : f.coeff 2 =
      depressedA410 hRF (quarticDepressionR410 hRF a3) a3 a2 := by
    dsimp only [f, depressedA410, a3, a2]
    rw [hpDep, coeff_depressedQuartic46_two]
  have hf1 : f.coeff 1 =
      depressedB410 hRF (quarticDepressionR410 hRF a3) a3 a2 a1 := by
    dsimp only [f, depressedB410, a3, a2, a1]
    rw [hpDep, coeff_depressedQuartic46_one]
  have hf0 : f.coeff 0 =
      depressedC410 hRF (quarticDepressionR410 hRF a3) a3 a2 a1 a0 := by
    dsimp only [f, depressedC410, a3, a2, a1, a0]
    rw [hpDep, coeff_depressedQuartic46_zero]
  have halpha0 :
      ratFuncDerivation68 (alphaResidual410 (f.coeff 2) (g.coeff 8)) =
        0 :=
    alphaResidual410_deriv_zero ratFuncDerivation68 (f.coeff 2)
      (g.coeff 8) hrow11
  have hbeta0 :
      ratFuncDerivation68
        (betaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
          (g.coeff 7)) = 0 :=
    betaResidual410_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 2) (f.coeff 1) (g.coeff 7) hLconst (by simpa using hrow10)
  have hgamma0 :
      ratFuncDerivation68
        (gammaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
          (f.coeff 0) (g.coeff 8) (g.coeff 6)) = 0 :=
    gammaResidual410_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 6)
      hLconst halpha0 (by simpa using hrow9)
  have hdelta0 :
      ratFuncDerivation68
        (deltaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
          (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 5)) = 0 :=
    deltaResidual410_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
      (g.coeff 5) hLconst halpha0 hbeta0 (by simpa using hrow8)
  have hepsilon0 :
      ratFuncDerivation68
        (epsilonResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
          (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
          (g.coeff 4)) = 0 :=
    epsilonResidual410_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
      (g.coeff 6) (g.coeff 4) hLconst halpha0 hbeta0 hgamma0
      (by simpa using hrow7)
  have hzeta0 :
      ratFuncDerivation68
        (zetaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
          (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
          (g.coeff 5) (g.coeff 3)) = 0 :=
    zetaResidual410_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
      (g.coeff 6) (g.coeff 5) (g.coeff 3) hLconst halpha0 hbeta0
      hgamma0 hdelta0 (by simpa using hrow6)
  have htheta0deriv :
      ratFuncDerivation68
        (thetaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
          (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
          (g.coeff 4) (g.coeff 3) (g.coeff 1)) = 0 :=
    thetaResidual410_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
      (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 1)
      hLconst halpha0 hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0
      (by simpa using hrow4)
  obtain ⟨c0, hc0⟩ :
      ∃ c0 : k,
        thetaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
            (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
            (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 1) =
          algebraMap k (RatFunc k) c0 := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      htheta0deriv
  have hp3R : a3 = hRF ^ 3 * t2R := by
    dsimp only [a3, hRF, t2R]
    rw [hp3, map_mul, map_pow]
  have hp2R : a2 = hRF ^ 2 * a22R := by
    dsimp only [a2, hRF, a22R]
    rw [hp2, map_mul, map_pow]
  have hq8R : b8 = hRF ^ 8 * s22R := by
    dsimp only [b8, hRF, s22R]
    rw [hq8, map_mul, map_pow]
  have hq7R : b7 = hRF ^ 6 * visR := by
    dsimp only [b7, hRF, visR]
    rw [hq7, map_mul, map_pow]
  have hq6R : b6 = hRF ^ 5 * w73R := by
    dsimp only [b6, hRF, w73R]
    rw [hq6, map_mul, map_pow]
  have hq5R : b5 = hRF ^ 4 * q54R := by
    dsimp only [b5, hRF, q54R]
    rw [hq5, map_mul, map_pow]
  have hq4R : b4 = hRF ^ 2 * b42R := by
    dsimp only [b4, hRF, b42R]
    rw [hq4, map_mul, map_pow]
  have hq3R : b3 = hRF * b31R := by
    dsimp only [b3, hRF, b31R]
    rw [hq3, map_mul]
  have hNratSub :
      5 * (hRF ^ 3 * t2R) * hRF ^ 6 - 2 * b9 =
        RatFunc.C lambda * hRF ^ 9 := by
    rw [← hp3R]
    exact hNrat
  have hF := thetaDefect_eq_cleared410 hRF t2R a22R s22R visR w73R q54R
    a1 a0 b42R b31R b2 b1 b9 (RatFunc.C lambda) hh hNratSub
  have hf2' : f.coeff 2 =
      depressedA410 hRF (quarticDepressionR410 hRF (hRF ^ 3 * t2R))
        (hRF ^ 3 * t2R) (hRF ^ 2 * a22R) := by
    rw [← hp3R, ← hp2R]
    exact hf2
  have hf1' : f.coeff 1 =
      depressedB410 hRF (quarticDepressionR410 hRF (hRF ^ 3 * t2R))
        (hRF ^ 3 * t2R) (hRF ^ 2 * a22R) a1 := by
    rw [← hp3R, ← hp2R]
    exact hf1
  have hf0' : f.coeff 0 =
      depressedC410 hRF (quarticDepressionR410 hRF (hRF ^ 3 * t2R))
        (hRF ^ 3 * t2R) (hRF ^ 2 * a22R) a1 a0 := by
    rw [← hp3R, ← hp2R]
    exact hf0
  have hg9L' : g.coeff 9 =
      depressedL410 hRF (quarticDepressionR410 hRF (hRF ^ 3 * t2R))
        b9 := by
    rw [← hp3R]
    exact hg9L
  have hg8'' : g.coeff 8 =
      depressedP410 hRF (quarticDepressionR410 hRF (hRF ^ 3 * t2R)) b9
        (hRF ^ 8 * s22R) := by
    rw [← hp3R, ← hq8R]
    exact hg8'
  have hg7' : g.coeff 7 =
      depressedQ410 hRF (quarticDepressionR410 hRF (hRF ^ 3 * t2R)) b9
        (hRF ^ 8 * s22R) (hRF ^ 6 * visR) := by
    rw [← hp3R, ← hq8R, ← hq7R]
    exact hg7
  have hg6' : g.coeff 6 =
      depressedR410 hRF (quarticDepressionR410 hRF (hRF ^ 3 * t2R)) b9
        (hRF ^ 8 * s22R) (hRF ^ 6 * visR) (hRF ^ 5 * w73R) := by
    rw [← hp3R, ← hq8R, ← hq7R, ← hq6R]
    exact hg6
  have hg5' : g.coeff 5 =
      depressedS410 hRF (quarticDepressionR410 hRF (hRF ^ 3 * t2R)) b9
        (hRF ^ 8 * s22R) (hRF ^ 6 * visR) (hRF ^ 5 * w73R)
        (hRF ^ 4 * q54R) := by
    rw [← hp3R, ← hq8R, ← hq7R, ← hq6R, ← hq5R]
    exact hg5
  have hg4' : g.coeff 4 =
      depressedT410 hRF (quarticDepressionR410 hRF (hRF ^ 3 * t2R)) b9
        (hRF ^ 8 * s22R) (hRF ^ 6 * visR) (hRF ^ 5 * w73R)
        (hRF ^ 4 * q54R) (hRF ^ 2 * b42R) := by
    rw [← hp3R, ← hq8R, ← hq7R, ← hq6R, ← hq5R, ← hq4R]
    exact hg4
  have hg3' : g.coeff 3 =
      depressedU410 hRF (quarticDepressionR410 hRF (hRF ^ 3 * t2R)) b9
        (hRF ^ 8 * s22R) (hRF ^ 6 * visR) (hRF ^ 5 * w73R)
        (hRF ^ 4 * q54R) (hRF ^ 2 * b42R) (hRF * b31R) := by
    rw [← hp3R, ← hq8R, ← hq7R, ← hq6R, ← hq5R, ← hq4R, ← hq3R]
    exact hg3
  have hg1' : g.coeff 1 =
      depressedW410 hRF (quarticDepressionR410 hRF (hRF ^ 3 * t2R)) b9
        (hRF ^ 8 * s22R) (hRF ^ 6 * visR) (hRF ^ 5 * w73R)
        (hRF ^ 4 * q54R) (hRF ^ 2 * b42R) (hRF * b31R) b2 b1 := by
    rw [← hp3R, ← hq8R, ← hq7R, ← hq6R, ← hq5R, ← hq4R, ← hq3R]
    exact hg1
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedThetaResidual410 h0 t2 a22 s22 vis w73 q54
            (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1)
            lambda) =
        (16777216 : RatFunc k) * hRF ^ 3 *
          thetaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
            (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
            (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 1) := by
    rw [hg9L', hf2', hf1', hf0', hg8'', hg7', hg6', hg5', hg4', hg3',
      hg1', hF]
    simp only [localClearedThetaResidual410,
      thetaPolarThreeNumerator410, thetaPolarTwoNumerator410,
      thetaPolarOneNumerator410, thetaRegularNumerator410, map_add,
      map_sub, map_mul, map_pow, map_neg, map_ofNat,
      RatFunc.algebraMap_C, hRF, t2R, a22R, s22R, visR, w73R, q54R,
      b42R, b31R, a1, a0, b2, b1]
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedThetaResidual410 h0 t2 a22 s22 vis w73 q54
            (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1)
            lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (16777216 * c0) * h0 ^ 3) := by
    rw [hclear, hc0]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat]
    ring
  refine ⟨16777216 * c0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

/-! ## Exact `h`-adic peel of the theta power relation -/

/-- Full `h`-adic peel of the cleared `θ` power relation: exact
cofactors for the order-`-3`, order-`-2`, and order-`-1` blocks, the
scalar tie of the regular block to the ground constant `c`, the
vanishing of the order-`-3` block at the root, and the three root
evaluations.  Nothing beyond `c` is left in the power relation. -/
theorem thetaBridge_fullPeel410 (h t2 a22 s22 vis w73 q54 a1 a0 b42
    b31 b2 b1 : k[X]) (lambda a c : k)
    (hroot : h.eval a = 0)
    (hpow : localClearedThetaResidual410 h t2 a22 s22 vis w73 q54 a1
        a0 b42 b31 b2 b1 lambda =
      Polynomial.C c * h ^ 3) :
    ∃ v1 v2 v3 : k[X],
      thetaPolarThreeNumerator410 vis a1 b42 = h * v1 ∧
        v1 + thetaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1 b42
            b31 b2 lambda =
          h * v2 ∧
        v2 + thetaPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b1
            lambda =
          h * v3 ∧
        v3 + thetaRegularNumerator410 t2 a22 s22 a0 lambda =
          Polynomial.C c ∧
        (thetaPolarThreeNumerator410 vis a1 b42).eval a = 0 ∧
        v1.eval a +
            (thetaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1 b42
                b31 b2 lambda).eval a =
          0 ∧
        v2.eval a +
            (thetaPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b1
                lambda).eval a =
          0 ∧
        v3.eval a +
            (thetaRegularNumerator410 t2 a22 s22 a0 lambda).eval a =
          c := by
  have hpow' := hpow
  simp only [localClearedThetaResidual410] at hpow'
  have htop : (thetaPolarThreeNumerator410 vis a1 b42).eval a = 0 := by
    have he := congrArg (fun r : k[X] => r.eval a) hpow
    simpa [localClearedThetaResidual410, hroot] using he
  refine ⟨Polynomial.C c * h ^ 2 -
      (thetaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1 b42 b31 b2
          lambda +
        h * (thetaPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b1
            lambda +
          h * thetaRegularNumerator410 t2 a22 s22 a0 lambda)),
    Polynomial.C c * h -
      (thetaPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b1
          lambda +
        h * thetaRegularNumerator410 t2 a22 s22 a0 lambda),
    Polynomial.C c - thetaRegularNumerator410 t2 a22 s22 a0 lambda,
    ?_, ?_, ?_, ?_, htop, ?_, ?_, ?_⟩
  · linear_combination hpow'
  · ring
  · ring
  · ring
  · simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, hroot]
    ring
  · simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, hroot]
    ring
  · simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, hroot]
    ring

/-! ## Collapse of the polar split -/

/-- On the thirteenth-face root data the order-`-3` block of the
cleared `θ` evaluates to `-5242880 p₁(a)³` with no branch factor, so
the power relation forces `p₁(a) = 0` unconditionally.  The iota-bridge
disjunction `p₁(a) = 0 ∨ λ + 4 t₂(a) = 0` resolves to its first
branch. -/
theorem thetaBridge_pOneVanishes410 (h t2 a22 s22 vis w73 q54 a1 a0
    b42 b31 b2 b1 : k[X]) (lambda a c : k)
    (hroot : h.eval a = 0)
    (hpow : localClearedThetaResidual410 h t2 a22 s22 vis w73 q54 a1
        a0 b42 b31 b2 b1 lambda =
      Polynomial.C c * h ^ 3)
    (hT : (64 : k) * vis.eval a - (160 : k) * a1.eval a = 0)
    (hW : (8 : k) * b42.eval a = (15 : k) * (a1.eval a) ^ 2) :
    a1.eval a = 0 := by
  have htop : (thetaPolarThreeNumerator410 vis a1 b42).eval a = 0 := by
    have he := congrArg (fun r : k[X] => r.eval a) hpow
    simpa [localClearedThetaResidual410, hroot] using he
  have htop' := htop
  simp only [thetaPolarThreeNumerator410, eval_add, eval_sub, eval_mul,
    eval_pow, eval_neg, eval_ofNat] at htop'
  have hcube : (a1.eval a) ^ 3 = 0 := by
    linear_combination (-1 / 5242880 : k) * htop' +
      (7 / 128 : k) * (a1.eval a) ^ 2 * hT -
      (2 / 5 : k) * (a1.eval a) * hW
  have h3 : (3 : ℕ) ≠ 0 := by norm_num
  exact (pow_eq_zero_iff h3).mp hcube

/-! ## Source-facing theta bridge packet -/

set_option maxHeartbeats 4000000 in
/-- Sharpest exact successor packet of the `θ` source clearing on the
nonzero `(4,10)` face: both power relations (`θ` and `ι`) with their
full `h`-adic peels, the unconditional collapse `p₁(a) = 0` of the
polar split, the vanishing of every thirteenth-face jet letter at the
root, the double pinning of the next unused source coefficient `q₁` by
the two towers (`v₂(a) + 16777216 q₁(a) = 0` and
`w₂(a) = 2 q₁(a) t₂(a)`), the degree-`0` Keller row without its `q₀'`
term (`p₀'(a) q₁(a) = j`), the elimination of `q₁(a)` linking the
literal Keller constant to the `θ` cofactor
(`p₀'(a) v₂(a) + 16777216 j = 0`), and — on the branch
`λ + 4 t₂(a) = 0` of the former split — the exact combinations of the
two towers with the Keller constant.  Nothing here closes the face:
`t₂(a), a₂₂, s₂₂, q₁(a), q₀(a), c, c_θ, j, p₀'(a), q₀'(a)` are free or
tied, not determined. -/
theorem nonzeroFace410_thetaSourceBridgePacket
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (t2 a22 s22 vis w73 q54 b42 b31 : k[X]) (a : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hp3 : p.coeff 3 = h0 ^ 3 * t2) (hp2 : p.coeff 2 = h0 ^ 2 * a22)
    (hq8 : q.coeff 8 = h0 ^ 8 * s22) (hq7 : q.coeff 7 = h0 ^ 6 * vis)
    (hq6 : q.coeff 6 = h0 ^ 5 * w73) (hq5 : q.coeff 5 = h0 ^ 4 * q54)
    (hq4 : q.coeff 4 = h0 ^ 2 * b42) (hq3 : q.coeff 3 = h0 * b31)
    (hroot : h0.eval a = 0)
    (hT : (64 : k) * vis.eval a - (160 : k) * (p.coeff 1).eval a = 0)
    (hU : (8 : k) * w73.eval a =
      (p.coeff 1).eval a * ((30 : k) * t2.eval a - (9 : k) * lambda))
    (hW : (8 : k) * b42.eval a = (15 : k) * ((p.coeff 1).eval a) ^ 2)
    (hV : (32 : k) * q54.eval a +
        (40 : k) * (p.coeff 1).eval a * a22.eval a -
        (64 : k) * (p.coeff 1).eval a * s22.eval a -
        (27 : k) * (p.coeff 1).eval a * lambda * t2.eval a +
        (90 : k) * (p.coeff 1).eval a * (t2.eval a) ^ 2 =
      0)
    (hX : (64 : k) * b31.eval a =
      (15 : k) * ((p.coeff 1).eval a) ^ 2 *
        ((4 : k) * t2.eval a - (3 : k) * lambda))
    (hY : (256 : k) * (q.coeff 2).eval a =
      ((p.coeff 1).eval a) ^ 2 *
        ((256 : k) * s22.eval a - (400 : k) * a22.eval a +
          (243 : k) * lambda * t2.eval a -
          (540 : k) * (t2.eval a) ^ 2)) :
    ∃ (ctheta c : k) (v1 v2 v3 w1 w2 w3 : k[X]),
      localClearedThetaResidual410 h0 t2 a22 s22 vis w73 q54
          (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1)
          lambda =
        Polynomial.C ctheta * h0 ^ 3 ∧
      thetaPolarThreeNumerator410 vis (p.coeff 1) b42 = h0 * v1 ∧
      v1 + thetaPolarTwoNumerator410 t2 a22 s22 vis w73 q54
          (p.coeff 1) b42 b31 (q.coeff 2) lambda =
        h0 * v2 ∧
      v2 + thetaPolarOneNumerator410 t2 a22 s22 vis w73 q54
          (p.coeff 1) (p.coeff 0) (q.coeff 1) lambda =
        h0 * v3 ∧
      v3 + thetaRegularNumerator410 t2 a22 s22 (p.coeff 0) lambda =
        Polynomial.C ctheta ∧
      localClearedIotaResidual410 h0 t2 a22 s22 vis w73 q54
          (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1)
          (q.coeff 0) lambda =
        Polynomial.C c * h0 ^ 3 ∧
      iotaPolarThreeNumerator410 t2 vis w73 (p.coeff 1) b42 b31
          lambda =
        h0 * w1 ∧
      w1 + iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 (p.coeff 1)
          (p.coeff 0) b42 b31 (q.coeff 2) lambda =
        h0 * w2 ∧
      w2 + iotaPolarOneNumerator410 t2 a22 s22 vis w73 q54 (p.coeff 1)
          (p.coeff 0) (q.coeff 1) lambda =
        h0 * w3 ∧
      w3 + iotaRegularNumerator410 t2 a22 s22 (p.coeff 0) (q.coeff 0)
          lambda =
        Polynomial.C c ∧
      (p.coeff 1).eval a = 0 ∧
      vis.eval a = 0 ∧
      w73.eval a = 0 ∧
      q54.eval a = 0 ∧
      b42.eval a = 0 ∧
      b31.eval a = 0 ∧
      (q.coeff 2).eval a = 0 ∧
      v1.eval a = 0 ∧
      w1.eval a = 0 ∧
      v2.eval a + (16777216 : k) * (q.coeff 1).eval a = 0 ∧
      w2.eval a = (2 : k) * (q.coeff 1).eval a * t2.eval a ∧
      v3.eval a +
          (thetaRegularNumerator410 t2 a22 s22 (p.coeff 0)
              lambda).eval a =
        ctheta ∧
      w3.eval a +
          (iotaRegularNumerator410 t2 a22 s22 (p.coeff 0) (q.coeff 0)
              lambda).eval a =
        c ∧
      ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a = j ∧
      ((p.coeff 0).derivative).eval a * v2.eval a +
          (16777216 : k) * j =
        0 ∧
      (lambda + (4 : k) * t2.eval a = 0 →
        (2 : k) * w2.eval a + lambda * (q.coeff 1).eval a = 0 ∧
          (33554432 : k) * w2.eval a = lambda * v2.eval a ∧
          (2 : k) * ((p.coeff 0).derivative).eval a * w2.eval a +
              lambda * j =
            0) := by
  obtain ⟨ctheta, hpowT⟩ := nonzeroFace410_thetaResidualPowerRelation
    p q H h0 j lambda t2 a22 s22 vis w73 q54 b42 b31 hp hq hh0 hH hp4
    hq10 hN hD hp3 hp2 hq8 hq7 hq6 hq5 hq4 hq3
  obtain ⟨v1, v2, v3, htw1, htw2, htw3, htwc, _, hte1, hte2, hte3⟩ :=
    thetaBridge_fullPeel410 h0 t2 a22 s22 vis w73 q54 (p.coeff 1)
      (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1) lambda a ctheta
      hroot hpowT
  have ha1 : (p.coeff 1).eval a = 0 :=
    thetaBridge_pOneVanishes410 h0 t2 a22 s22 vis w73 q54 (p.coeff 1)
      (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1) lambda a ctheta
      hroot hpowT hT hW
  have hvis0 : vis.eval a = 0 := by
    linear_combination (1 / 64 : k) * hT + (5 / 2 : k) * ha1
  have hw730 : w73.eval a = 0 := by
    linear_combination (1 / 8 : k) * hU +
      (((30 : k) * t2.eval a - (9 : k) * lambda) / 8) * ha1
  have hb420 : b42.eval a = 0 := by
    linear_combination (1 / 8 : k) * hW +
      (15 / 8 : k) * (p.coeff 1).eval a * ha1
  have hq540 : q54.eval a = 0 := by
    linear_combination (1 / 32 : k) * hV -
      (1 / 32 : k) *
        ((40 : k) * a22.eval a - (64 : k) * s22.eval a -
          (27 : k) * lambda * t2.eval a +
          (90 : k) * (t2.eval a) ^ 2) * ha1
  have hb310 : b31.eval a = 0 := by
    linear_combination (1 / 64 : k) * hX +
      (15 / 64 : k) * (p.coeff 1).eval a *
        ((4 : k) * t2.eval a - (3 : k) * lambda) * ha1
  have hb20 : (q.coeff 2).eval a = 0 := by
    linear_combination (1 / 256 : k) * hY +
      (1 / 256 : k) * (p.coeff 1).eval a *
        ((256 : k) * s22.eval a - (400 : k) * a22.eval a +
          (243 : k) * lambda * t2.eval a -
          (540 : k) * (t2.eval a) ^ 2) * ha1
  obtain ⟨c, hpowI⟩ := nonzeroFace410_iotaResidualPowerRelation p q H
    h0 j lambda t2 a22 s22 vis w73 q54 b42 b31 hp hq hh0 hH hp4 hq10
    hN hD hp3 hp2 hq8 hq7 hq6 hq5 hq4 hq3
  obtain ⟨w1, w2, w3, hiw1, hiw2, hiw3, hiwc, hie1, hie2, hie3⟩ :=
    iotaBridge_orderOnePeel410 h0 t2 a22 s22 vis w73 q54 (p.coeff 1)
      (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1) (q.coeff 0) lambda a
      c hroot hpowI
  have hkel := kellerRowConstant_eval410 hp hq hD a
  have hTH2ev :
      (thetaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 (p.coeff 1)
          b42 b31 (q.coeff 2) lambda).eval a = 0 := by
    simp only [thetaPolarTwoNumerator410, eval_add, eval_sub, eval_mul,
      eval_pow, eval_neg, eval_ofNat, eval_C, ha1, hvis0, hw730, hq540,
      hb420, hb310, hb20]
    ring
  have hTH1ev :
      (thetaPolarOneNumerator410 t2 a22 s22 vis w73 q54 (p.coeff 1)
          (p.coeff 0) (q.coeff 1) lambda).eval a =
        (16777216 : k) * (q.coeff 1).eval a := by
    simp only [thetaPolarOneNumerator410, eval_add, eval_sub, eval_mul,
      eval_pow, eval_neg, eval_ofNat, eval_C, ha1, hvis0, hw730,
      hq540]
    ring
  have hIO2ev :
      (iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 (p.coeff 1)
          (p.coeff 0) b42 b31 (q.coeff 2) lambda).eval a = 0 := by
    simp only [iotaPolarTwoNumerator410, eval_add, eval_sub, eval_mul,
      eval_pow, eval_neg, eval_ofNat, eval_C, ha1, hvis0, hw730, hq540,
      hb420, hb310, hb20]
    ring
  have hIO1ev :
      (iotaPolarOneNumerator410 t2 a22 s22 vis w73 q54 (p.coeff 1)
          (p.coeff 0) (q.coeff 1) lambda).eval a =
        -(2 : k) * (q.coeff 1).eval a * t2.eval a := by
    simp only [iotaPolarOneNumerator410, eval_add, eval_sub, eval_mul,
      eval_pow, eval_neg, eval_ofNat, eval_C, ha1, hvis0, hw730,
      hq540]
    ring
  have hv10 : v1.eval a = 0 := by
    linear_combination hte1 - hTH2ev
  have hw10 : w1.eval a = 0 := by
    linear_combination hie1 - hIO2ev
  have hv2tie : v2.eval a + (16777216 : k) * (q.coeff 1).eval a = 0 := by
    linear_combination hte2 - hTH1ev
  have hw2tie : w2.eval a = (2 : k) * (q.coeff 1).eval a * t2.eval a := by
    linear_combination hie2 - hIO1ev
  have hkelP :
      ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a = j := by
    linear_combination hkel + ((q.coeff 0).derivative).eval a * ha1
  have hcombo :
      ((p.coeff 0).derivative).eval a * v2.eval a +
          (16777216 : k) * j = 0 := by
    linear_combination ((p.coeff 0).derivative).eval a * hv2tie -
      (16777216 : k) * hkelP
  refine ⟨ctheta, c, v1, v2, v3, w1, w2, w3, hpowT, htw1, htw2, htw3,
    htwc, hpowI, hiw1, hiw2, hiw3, hiwc, ha1, hvis0, hw730, hq540,
    hb420, hb310, hb20, hv10, hw10, hv2tie, hw2tie, hte3, hie3, hkelP,
    hcombo, ?_⟩
  intro hbranch
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (2 : k) * hw2tie +
      (q.coeff 1).eval a * hbranch
  · linear_combination (33554432 : k) * hw2tie - lambda * hv2tie +
      (16777216 : k) * (q.coeff 1).eval a * hbranch
  · linear_combination
      (2 : k) * ((p.coeff 0).derivative).eval a * hw2tie -
      lambda * hkelP +
      ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a * hbranch

end NonzeroThetaBridge410

#print axioms affineDepress_degreeTen_coeff1_410
#print axioms depressedW410_eq_cleared
#print axioms thetaDefect_eq_cleared410
#print axioms nonzeroFace410_thetaResidualPowerRelation
#print axioms thetaBridge_fullPeel410
#print axioms thetaBridge_pOneVanishes410
#print axioms nonzeroFace410_thetaSourceBridgePacket

end Max11DegreeRoutes
