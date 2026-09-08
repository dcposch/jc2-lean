import Grok410ScaleTwoTerminalIotaScratch

/-! # Alternate iota derivative/source bridge for the normalized `(4,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₃ H³ - 2 q₉ = λ h⁹` with
`h.natDegree = 1`, the terminal file computed the order-`-3` polar
coefficient of the tenth-face residual `ι` on the twelfth/thirteenth jet
as `15 p₁³ (λ + 4 t₂) / 256`, but did not prove that it vanishes: the
degree-`3` first-integral identity `d ι = 0` was never descended to the
literal source.  This file closes that gap independently.

First, `iotaResidualAlternate410_deriv_zero` proves the exact
first-integral identity: on the literal depressed degree-`3` row
`4 T C' + 3 U B' + 2 V A' - B U' - 2 A V' - 4 Z' = 0` and the second-
through eighth-face integrals `α, …, η`, the residual `ι` is a
differential constant.  No first integral is constructed for the
degree-`0` row, which is not exact.

Second, on the thirteenth-face jet `p₃ = h³ t₂`, `p₂ = h² a₂₂`,
`q₈ = h⁸ s₂₂`, `q₇ = h⁶ v`, `q₆ = h⁵ w`, `q₅ = h⁴ u`, `q₄ = h² b₄₂`,
`q₃ = h b₃₁`, the residual clears against `h³` exactly:
`8 h³ ι = Δ₃ + h (Δ₂ + h (Δ₁ + h Δ₀))` with explicit integer polynomial
blocks satisfying `Δ₃ = 8 ι₋₃` and `Δ₂ = 8 ι₋₂` for the polar
numerators of the terminal file.  Descending `ι` to the ground field
through the affine depression of the literal source
(`nonzeroFace410_iotaAlternatePowerRelation`) shows the cleared defect
is a scalar multiple of `h³`, with the scalar `8 ι₀` left arbitrary.

Consequently the order-`-3` polar coefficient genuinely vanishes at the
root of the degree-one scale: `p₁(a)³ (λ + 4 t₂(a)) = 0`, so the
nonzero face splits into the two branches `p₁(a) = 0` and
`λ + 4 t₂(a) = 0`; neither branch is eliminated and no unique vanishing
is claimed.  At order `-2` the power relation does not force `ι₋₂(a)`
to vanish: it ties the `h`-cofactor `w₁` of the order-`-3` block to
`128 w₁(a) + 3 p₁(a)² (-160 a₂₂² + 18 λ a₂₂ t₂ + 440 a₂₂ t₂²
- 27 λ t₂³ + 256 s₂₂ t₂² - 180 t₂⁴)(a) = 0`, and that exact residual
is retained.  The ground constants `α, β, γ, δ` are not touched, `ι₀`
is not claimed to vanish, and the degree-`0` row `W C' - B Z' = j` is
not used.

No total-degree or twice-prime theorem is used.  The aligned face
`N = 0` is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## The degree-`3` row first integral: `d ι = 0` -/

section IotaDerivativeAlternate410

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

set_option maxHeartbeats 64000000 in
/-- The tenth-face residual `ι` is an exact first integral of the literal
degree-`3` depressed Jacobian row on the second- through eighth-face
integrals. -/
theorem iotaResidualAlternate410_deriv_zero
    (d : Derivation k F F) (L A B C0 P Q R S0 T0 U0 V0 Z0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual410 A P) = 0)
    (hbeta : d (betaResidual410 L A B Q) = 0)
    (hgamma : d (gammaResidual410 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual410 L A B C0 P Q S0) = 0)
    (hepsilon : d (epsilonResidual410 L A B C0 P Q R T0) = 0)
    (hzeta : d (zetaResidual410 L A B C0 P Q R S0 U0) = 0)
    (heta : d (etaResidual410 L A B C0 P Q R S0 T0 V0) = 0)
    (hrow : (4 : F) * T0 * d C0 + (3 : F) * U0 * d B +
        (2 : F) * V0 * d A - B * d U0 - (2 : F) * A * d V0 -
        (4 : F) * d Z0 = 0) :
    d (iotaResidual410 L A B C0 P Q R S0 T0 U0 V0 Z0) = 0 := by
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h3 : d (3 : F) = 0 := d.map_natCast 3
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h7 : d (7 : F) = 0 := d.map_natCast 7
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h15 : d (15 : F) = 0 := d.map_natCast 15
  have h16 : d (16 : F) = 0 := d.map_natCast 16
  have h21 : d (21 : F) = 0 := d.map_natCast 21
  have h25 : d (25 : F) = 0 := d.map_natCast 25
  have h27 : d (27 : F) = 0 := d.map_natCast 27
  have h32 : d (32 : F) = 0 := d.map_natCast 32
  have h35 : d (35 : F) = 0 := d.map_natCast 35
  have h45 : d (45 : F) = 0 := d.map_natCast 45
  have h49 : d (49 : F) = 0 := d.map_natCast 49
  have h63 : d (63 : F) = 0 := d.map_natCast 63
  have h75 : d (75 : F) = 0 := d.map_natCast 75
  have h81 : d (81 : F) = 0 := d.map_natCast 81
  have h128 : d (128 : F) = 0 := d.map_natCast 128
  have h135 : d (135 : F) = 0 := d.map_natCast 135
  have h175 : d (175 : F) = 0 := d.map_natCast 175
  have h231 : d (231 : F) = 0 := d.map_natCast 231
  have h385 : d (385 : F) = 0 := d.map_natCast 385
  have h693 : d (693 : F) = 0 := d.map_natCast 693
  have h64 : d (64 : F) = 0 := d.map_natCast 64
  have h2inv : d ((2 : F)⁻¹) = 0 := by
    have hne : (2 : F) ≠ 0 := two_ne_zero
    have hd : (2 : F) • d ((2 : F)⁻¹) + ((2 : F)⁻¹) • d (2 : F) = 0 := by
      rw [← Derivation.leibniz, mul_inv_cancel₀ hne]
      exact d.map_one_eq_zero
    have hd2 : (2 : F) * d ((2 : F)⁻¹) = 0 := by
      simpa [smul_eq_mul, h2] using hd
    exact (mul_eq_zero.mp hd2).resolve_left hne
  have h52 : d (5 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h5]
  have h94 : d (9 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h9]
  have h54 : d (5 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h5]
  have h32div : d (3 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h3]
  have h74 : d (7 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h7]
  have h34 : d (3 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h3]
  have h72 : d (7 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h7]
  have h92 : d (9 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h9]
  have h98 : d (9 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h9]
  have h154 : d (15 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h15]
  have h158 : d (15 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h15]
  have h218 : d (21 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h21]
  have h258 : d (25 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h25]
  have h278 : d (27 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h27]
  have h358 : d (35 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h35]
  have h458 : d (45 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h45]
  have h758 : d (75 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h75]
  have h7516 : d (75 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h75]
  have h4932 : d (49 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h49]
  have h6316 : d (63 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h63]
  have h6332 : d (63 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h63]
  have h8132 : d (81 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h81]
  have h13532 : d (135 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h135]
  have h13516 : d (135 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h135]
  have h175128 : d (175 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h175]
  have h17532 : d (175 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h175]
  have h231128 : d (231 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h231]
  have h38564 : d (385 / 64 : F) = 0 := by
    simp [Derivation.leibniz_div, h64, h385]
  have h693128 : d (693 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h693]
  have hP0 : d P - (5 / 2 : F) * d A = 0 := by
    simpa [alphaResidual410, map_sub, Derivation.leibniz, h52, zero_mul,
      add_zero] using halpha
  have hQ0 : d Q - (5 / 2 : F) * d B - (9 / 4 : F) * L * d A = 0 := by
    simpa [betaResidual410, map_sub, Derivation.leibniz, h52, h94, hL,
      zero_mul, add_zero, mul_zero] using hbeta
  have hsqA : d (A * A) = (2 : F) * A * d A := by
    simp [Derivation.leibniz]; ring
  have hsqB : d (B * B) = (2 : F) * B * d B := by
    simp [Derivation.leibniz]; ring
  have hsqC : d (C0 * C0) = (2 : F) * C0 * d C0 := by
    simp [Derivation.leibniz]; ring
  have hcube : d (A * A * A) = (3 : F) * (A * A) * d A := by
    simp [Derivation.leibniz]; ring
  have hfourth : d (A * A * A * A) = (4 : F) * (A * A * A) * d A := by
    simp [Derivation.leibniz]; ring
  have hfifth : d (A * A * A * A * A) =
      (5 : F) * (A * A * A * A) * d A := by
    simp [Derivation.leibniz]; ring
  have hcubeB : d (B * B * B) = (3 : F) * (B * B) * d B := by
    simp [Derivation.leibniz]; ring
  have hR0 :
      d R - (5 / 2 : F) * d C0 - (9 / 4 : F) * L * d B -
          (2 : F) * A * d P - (2 : F) * P * d A +
          (25 / 4 : F) * A * d A = 0 := by
    have hexp :
        gammaResidual410 L A B C0 P R =
          R - (5 / 2 : F) * C0 - (9 / 4 : F) * L * B -
            (2 : F) * P * A + (25 / 8 : F) * (A * A) := by
      simp only [gammaResidual410, pow_two]
    have hdg :
        d (R - (5 / 2 : F) * C0 - (9 / 4 : F) * L * B -
            (2 : F) * P * A + (25 / 8 : F) * (A * A)) = 0 := by
      simpa [hexp] using hgamma
    simp [map_sub, map_add, Derivation.leibniz, h2, h52, h94, h258, hL,
      hsqA, zero_mul, add_zero, mul_zero] at hdg
    linear_combination hdg
  have hS0 :
      d S0 - (9 / 4 : F) * L * d C0 - (2 : F) * B * d P -
          (2 : F) * P * d B - (7 / 4 : F) * A * d Q -
          (7 / 4 : F) * Q * d A + (45 / 8 : F) * B * d A +
          (45 / 8 : F) * A * d B + (81 / 16 : F) * L * A * d A = 0 := by
    have hexp :
        deltaResidual410 L A B C0 P Q S0 =
          S0 - (9 / 4 : F) * L * C0 - (2 : F) * P * B -
            (7 / 4 : F) * Q * A + (45 / 8 : F) * A * B +
            (81 / 32 : F) * L * (A * A) := by
      simp only [deltaResidual410, alphaResidual410, betaResidual410,
        pow_two]
      ring
    have hdg :
        d (S0 - (9 / 4 : F) * L * C0 - (2 : F) * P * B -
            (7 / 4 : F) * Q * A + (45 / 8 : F) * A * B +
            (81 / 32 : F) * L * (A * A)) = 0 := by
      simpa [hexp] using hdelta
    simp [map_sub, map_add, Derivation.leibniz, h2, h94, h74, h458, h8132,
      hL, hsqA, zero_mul, add_zero, mul_zero] at hdg
    linear_combination hdg
  have hT0 :
      d T0 - (2 : F) * C0 * d P - (2 : F) * P * d C0 -
          (7 / 4 : F) * B * d Q - (7 / 4 : F) * Q * d B -
          (3 / 2 : F) * A * d R - (3 / 2 : F) * R * d A +
          (2 : F) * (A * A) * d P + (4 : F) * P * A * d A +
          (9 / 2 : F) * L * B * d A + (9 / 2 : F) * L * A * d B +
          (5 : F) * C0 * d A + (5 : F) * A * d C0 +
          (5 : F) * B * d B - (15 / 2 : F) * (A * A) * d A = 0 := by
    have hexp :
        epsilonResidual410 L A B C0 P Q R T0 =
          T0 - (2 : F) * P * C0 - (7 / 4 : F) * Q * B -
            (3 / 2 : F) * R * A + (2 : F) * P * (A * A) +
            (9 / 2 : F) * L * A * B + (5 : F) * A * C0 +
            (5 / 2 : F) * (B * B) - (5 / 2 : F) * (A * A * A) := by
      simp only [epsilonResidual410, alphaResidual410, betaResidual410,
        gammaResidual410, pow_two, pow_three]
      ring
    have hdg :
        d (T0 - (2 : F) * P * C0 - (7 / 4 : F) * Q * B -
            (3 / 2 : F) * R * A + (2 : F) * P * (A * A) +
            (9 / 2 : F) * L * A * B + (5 : F) * A * C0 +
            (5 / 2 : F) * (B * B) - (5 / 2 : F) * (A * A * A)) = 0 := by
      simpa [hexp] using hepsilon
    simp [map_sub, map_add, Derivation.leibniz, h2, h3, h5, h52, h74,
      h32div, h92, hL, hsqA, hsqB, hcube, zero_mul, add_zero,
      mul_zero] at hdg
    linear_combination hdg
  have hU0 :
      d U0 - (5 / 4 : F) * S0 * d A - (5 / 4 : F) * A * d S0 -
          (3 / 2 : F) * R * d B - (3 / 2 : F) * B * d R -
          (7 / 4 : F) * Q * d C0 - (7 / 4 : F) * C0 * d Q +
          (7 / 2 : F) * B * P * d A + (7 / 2 : F) * A * P * d B +
          (7 / 2 : F) * A * B * d P + (49 / 16 : F) * A * Q * d A +
          (49 / 32 : F) * (A * A) * d Q +
          (63 / 16 : F) * L * C0 * d A + (63 / 16 : F) * L * A * d C0 +
          (63 / 16 : F) * L * B * d B +
          (35 / 8 : F) * C0 * d B + (35 / 8 : F) * B * d C0 -
          (693 / 128 : F) * L * (A * A) * d A -
          (385 / 32 : F) * A * B * d A -
          (385 / 64 : F) * (A * A) * d B = 0 := by
    have hexp :
        zetaResidual410 L A B C0 P Q R S0 U0 =
          U0 - (5 / 4 : F) * A * S0 - (3 / 2 : F) * B * R -
            (7 / 4 : F) * C0 * Q + (7 / 2 : F) * A * B * P +
            (49 / 32 : F) * (A * A) * Q + (63 / 16 : F) * L * A * C0 +
            (63 / 32 : F) * L * (B * B) + (35 / 8 : F) * B * C0 -
            (231 / 128 : F) * L * (A * A * A) -
            (385 / 64 : F) * (A * A) * B := by
      simp only [zetaResidual410, alphaResidual410, betaResidual410,
        gammaResidual410, deltaResidual410, pow_two, pow_three]
      ring
    have hdg :
        d (U0 - (5 / 4 : F) * A * S0 - (3 / 2 : F) * B * R -
            (7 / 4 : F) * C0 * Q + (7 / 2 : F) * A * B * P +
            (49 / 32 : F) * (A * A) * Q + (63 / 16 : F) * L * A * C0 +
            (63 / 32 : F) * L * (B * B) + (35 / 8 : F) * B * C0 -
            (231 / 128 : F) * L * (A * A * A) -
            (385 / 64 : F) * (A * A) * B) = 0 := by
      simpa [hexp] using hzeta
    simp [map_sub, map_add, Derivation.leibniz, h2, h3, h4, h5, h7, h8,
      h16, h32, h54, h32div, h74, h72, h4932, h6316, h6332, h358,
      h231128, h38564, h693128, hL, hsqA, hsqB, hcube, zero_mul,
      add_zero, mul_zero] at hdg
    linear_combination hdg
  have hV0 :
      d V0 - A * d T0 - (75 / 16 : F) * (A * A) * d C0 +
          (9 / 8 : F) * (A * A) * d R +
          (175 / 32 : F) * (A * A * A) * d A -
          (5 / 4 : F) * (A * A * A) * d P - (5 / 4 : F) * B * d S0 -
          (75 / 16 : F) * (B * B) * d A + (3 / 2 : F) * (B * B) * d P +
          (15 / 4 : F) * C0 * d C0 - (3 / 2 : F) * C0 * d R -
          (3 / 2 : F) * R * d C0 - (5 / 4 : F) * S0 * d B - T0 * d A -
          (75 / 8 : F) * A * B * d B + (21 / 8 : F) * A * B * d Q -
          (75 / 8 : F) * A * C0 * d A + (3 : F) * A * C0 * d P +
          (3 : F) * A * P * d C0 + (21 / 8 : F) * A * Q * d B +
          (9 / 4 : F) * A * R * d A -
          (135 / 32 : F) * (A * A) * L * d B -
          (15 / 4 : F) * (A * A) * P * d A +
          (27 / 8 : F) * B * L * d C0 + (3 : F) * B * P * d B +
          (21 / 8 : F) * B * Q * d A + (27 / 8 : F) * C0 * L * d B +
          (3 : F) * C0 * P * d A -
          (135 / 16 : F) * A * B * L * d A = 0 := by
    have hexp :
        etaResidual410 L A B C0 P Q R S0 T0 V0 =
          V0 - A * T0 - (5 / 4 : F) * B * S0 - (3 / 2 : F) * C0 * R +
            (15 / 8 : F) * (C0 * C0) + (9 / 8 : F) * (A * A) * R +
            (21 / 8 : F) * A * B * Q + (3 : F) * A * C0 * P +
            (3 / 2 : F) * (B * B) * P - (5 / 4 : F) * (A * A * A) * P -
            (135 / 32 : F) * (A * A) * B * L +
            (27 / 8 : F) * B * C0 * L - (75 / 16 : F) * (A * A) * C0 -
            (75 / 16 : F) * A * (B * B) +
            (175 / 128 : F) * (A * A * A * A) := by
      simp only [etaResidual410, alphaResidual410, betaResidual410,
        gammaResidual410, deltaResidual410, epsilonResidual410, pow_two,
        pow_three]
      ring
    have hdg :
        d (V0 - A * T0 - (5 / 4 : F) * B * S0 - (3 / 2 : F) * C0 * R +
            (15 / 8 : F) * (C0 * C0) + (9 / 8 : F) * (A * A) * R +
            (21 / 8 : F) * A * B * Q + (3 : F) * A * C0 * P +
            (3 / 2 : F) * (B * B) * P - (5 / 4 : F) * (A * A * A) * P -
            (135 / 32 : F) * (A * A) * B * L +
            (27 / 8 : F) * B * C0 * L - (75 / 16 : F) * (A * A) * C0 -
            (75 / 16 : F) * A * (B * B) +
            (175 / 128 : F) * (A * A * A * A)) = 0 := by
      simpa [hexp] using heta
    simp [map_sub, map_add, Derivation.leibniz, h2, h3, h4, h8, h16,
      h32, h128, h54, h32div, h158, h98, h218, h13532, h278, h7516,
      h175128, h17532, h13516, h758, h154, hL, hsqA, hsqB, hsqC, hcube,
      hfourth, zero_mul, add_zero, mul_zero] at hdg
    linear_combination hdg
  have hPderiv : d P = (5 / 2 : F) * d A := by linear_combination hP0
  have hQderiv : d Q = (5 / 2 : F) * d B + (9 / 4 : F) * L * d A := by
    linear_combination hQ0
  have hRderiv :
      d R = (5 / 2 : F) * d C0 + (9 / 4 : F) * L * d B +
        (2 : F) * A * d P + (2 : F) * P * d A -
        (25 / 4 : F) * A * d A := by
    linear_combination hR0
  have hSderiv :
      d S0 = (9 / 4 : F) * L * d C0 + (2 : F) * B * d P +
        (2 : F) * P * d B + (7 / 4 : F) * A * d Q +
        (7 / 4 : F) * Q * d A - (45 / 8 : F) * B * d A -
        (45 / 8 : F) * A * d B - (81 / 16 : F) * L * A * d A := by
    linear_combination hS0
  have hTderiv :
      d T0 = (2 : F) * C0 * d P + (2 : F) * P * d C0 +
        (7 / 4 : F) * B * d Q + (7 / 4 : F) * Q * d B +
        (3 / 2 : F) * A * d R + (3 / 2 : F) * R * d A -
        (2 : F) * (A * A) * d P - (4 : F) * P * A * d A -
        (9 / 2 : F) * L * B * d A - (9 / 2 : F) * L * A * d B -
        (5 : F) * C0 * d A - (5 : F) * A * d C0 -
        (5 : F) * B * d B + (15 / 2 : F) * (A * A) * d A := by
    linear_combination hT0
  have hUderiv :
      d U0 = (5 / 4 : F) * S0 * d A + (5 / 4 : F) * A * d S0 +
        (3 / 2 : F) * R * d B + (3 / 2 : F) * B * d R +
        (7 / 4 : F) * Q * d C0 + (7 / 4 : F) * C0 * d Q -
        (7 / 2 : F) * B * P * d A - (7 / 2 : F) * A * P * d B -
        (7 / 2 : F) * A * B * d P - (49 / 16 : F) * A * Q * d A -
        (49 / 32 : F) * (A * A) * d Q -
        (63 / 16 : F) * L * C0 * d A - (63 / 16 : F) * L * A * d C0 -
        (63 / 16 : F) * L * B * d B -
        (35 / 8 : F) * C0 * d B - (35 / 8 : F) * B * d C0 +
        (693 / 128 : F) * L * (A * A) * d A +
        (385 / 32 : F) * A * B * d A +
        (385 / 64 : F) * (A * A) * d B := by
    linear_combination hU0
  have hVderiv :
      d V0 = A * d T0 + (75 / 16 : F) * (A * A) * d C0 -
        (9 / 8 : F) * (A * A) * d R -
        (175 / 32 : F) * (A * A * A) * d A +
        (5 / 4 : F) * (A * A * A) * d P + (5 / 4 : F) * B * d S0 +
        (75 / 16 : F) * (B * B) * d A - (3 / 2 : F) * (B * B) * d P -
        (15 / 4 : F) * C0 * d C0 + (3 / 2 : F) * C0 * d R +
        (3 / 2 : F) * R * d C0 + (5 / 4 : F) * S0 * d B + T0 * d A +
        (75 / 8 : F) * A * B * d B - (21 / 8 : F) * A * B * d Q +
        (75 / 8 : F) * A * C0 * d A - (3 : F) * A * C0 * d P -
        (3 : F) * A * P * d C0 - (21 / 8 : F) * A * Q * d B -
        (9 / 4 : F) * A * R * d A +
        (135 / 32 : F) * (A * A) * L * d B +
        (15 / 4 : F) * (A * A) * P * d A -
        (27 / 8 : F) * B * L * d C0 - (3 : F) * B * P * d B -
        (21 / 8 : F) * B * Q * d A - (27 / 8 : F) * C0 * L * d B -
        (3 : F) * C0 * P * d A +
        (135 / 16 : F) * A * B * L * d A := by
    linear_combination hV0
  have hZderiv :
      d Z0 = T0 * d C0 + (3 / 4 : F) * U0 * d B +
        (1 / 2 : F) * V0 * d A - (1 / 4 : F) * B * d U0 -
        (1 / 2 : F) * A * d V0 := by
    linear_combination (-1 / 4 : F) * hrow
  have htarget :
      d Z0 - (1 / 2 : F) * A * d V0 + (1 / 2 : F) * (A * A) * d T0 +
          (5 / 2 : F) * (A * A * A) * d C0 -
          (1 / 2 : F) * (A * A * A) * d R -
          (5 / 2 : F) * (A * A * A * A) * d A +
          (1 / 2 : F) * (A * A * A * A) * d P -
          (3 / 4 : F) * B * d U0 - (5 / 2 : F) * (B * B) * d C0 +
          (3 / 4 : F) * (B * B) * d R - C0 * d T0 -
          (5 / 2 : F) * (C0 * C0) * d A + (C0 * C0) * d P -
          T0 * d C0 - (3 / 4 : F) * U0 * d B - (1 / 2 : F) * V0 * d A +
          (5 / 4 : F) * A * B * d S0 +
          (15 / 2 : F) * A * (B * B) * d A -
          (2 : F) * A * (B * B) * d P - (5 : F) * A * C0 * d C0 +
          (3 / 2 : F) * A * C0 * d R + (3 / 2 : F) * A * R * d C0 +
          (5 / 4 : F) * A * S0 * d B + A * T0 * d A +
          (15 / 2 : F) * (A * A) * B * d B -
          (7 / 4 : F) * (A * A) * B * d Q +
          (15 / 2 : F) * (A * A) * C0 * d A -
          (2 : F) * (A * A) * C0 * d P -
          (2 : F) * (A * A) * P * d C0 -
          (7 / 4 : F) * (A * A) * Q * d B -
          (3 / 2 : F) * (A * A) * R * d A +
          (9 / 4 : F) * (A * A * A) * L * d B +
          (2 : F) * (A * A * A) * P * d A - (5 : F) * B * C0 * d B +
          (7 / 4 : F) * B * C0 * d Q + (7 / 4 : F) * B * Q * d C0 +
          (3 / 2 : F) * B * R * d B + (5 / 4 : F) * B * S0 * d A -
          (9 / 4 : F) * (B * B) * L * d B -
          (2 : F) * (B * B) * P * d A + (2 : F) * C0 * P * d C0 +
          (7 / 4 : F) * C0 * Q * d B + (3 / 2 : F) * C0 * R * d A -
          (9 / 2 : F) * A * B * L * d C0 - (4 : F) * A * B * P * d B -
          (7 / 2 : F) * A * B * Q * d A -
          (9 / 2 : F) * A * C0 * L * d B - (4 : F) * A * C0 * P * d A +
          (27 / 4 : F) * (A * A) * B * L * d A -
          (9 / 2 : F) * B * C0 * L * d A = 0 := by
    rw [hZderiv, hVderiv, hUderiv, hTderiv, hSderiv, hRderiv, hQderiv,
      hPderiv]
    ring
  rw [iotaResidual410_eq_expanded]
  simp [map_sub, map_add, Derivation.leibniz, h2, h3, h4, h5, h7, h9,
    h15, h2inv, h34, h54, h32div, h74, h94, h92, h52, h154, hL, hsqA,
    hsqB, hsqC, hcube, hfourth, hfifth, hcubeB, zero_mul, add_zero,
    mul_zero]
  linear_combination htarget

end IotaDerivativeAlternate410

/-! ## Constant coefficient of the depressed decic -/

section IotaAltCoeffZero410

variable {F : Type*} [Field F] [CharZero F]

/-- The constant coefficient of a monic-after-scaling degree-ten source
under the affine depression `y = (z - r)/h`, by direct evaluation at
zero. -/
theorem affineDepressAlternate_degreeTen_coeff0_410
    (p : F[X]) (h r : F) (hh : h ≠ 0)
    (hp10 : p.coeff 10 = h ^ 10)
    (hp_high : ∀ n, 10 < n → p.coeff n = 0) :
    (affineDepress68 h r p).coeff 0 =
      r ^ 10 - (p.coeff 9 / h ^ 9) * r ^ 9 +
        (p.coeff 8 / h ^ 8) * r ^ 8 - (p.coeff 7 / h ^ 7) * r ^ 7 +
        (p.coeff 6 / h ^ 6) * r ^ 6 - (p.coeff 5 / h ^ 5) * r ^ 5 +
        (p.coeff 4 / h ^ 4) * r ^ 4 - (p.coeff 3 / h ^ 3) * r ^ 3 +
        (p.coeff 2 / h ^ 2) * r ^ 2 - (p.coeff 1 / h) * r +
        p.coeff 0 := by
  have hdeg : p.natDegree ≤ 10 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hp_high
  have hlt : p.natDegree < 11 := Nat.lt_succ_of_le hdeg
  have harg :
      ((X - Polynomial.C r) * Polynomial.C h⁻¹).eval (0 : F) =
        -r * h⁻¹ := by
    simp only [eval_mul, eval_sub, eval_X, eval_C, zero_sub, neg_mul]
  have hcoeff0 :
      (affineDepress68 h r p).coeff 0 = p.eval (-r * h⁻¹) := by
    rw [show affineDepress68 h r p =
        p.comp ((X - Polynomial.C r) * Polynomial.C h⁻¹) from rfl,
      Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp, harg]
  rw [hcoeff0, Polynomial.eval_eq_sum_range' hlt]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hp10]
  field_simp
  ring

end IotaAltCoeffZero410

/-! ## The cleared iota defect on the thirteenth-face jet -/

section IotaAltCleared410

variable {F : Type*} [Field F] [CharZero F]

/-- Order-`-3` block of the cleared iota defect: `8 ι₋₃` as an exact
polynomial. -/
def iotaAltPolarThree410 (t2 vis w73 a1 b42 b31 : F[X])
    (lambda : F) : F[X] :=
  -(6 : F[X]) * a1 * b31
      + (6 : F[X]) * a1 ^ 2 * w73
      + (3 : F[X]) * a1 ^ 3 * Polynomial.C lambda
      + (5 : F[X]) * a1 ^ 3 * t2
      + (8 : F[X]) * a1 * b42 * t2
      - (14 : F[X]) * a1 ^ 2 * t2 * vis

/-- Order-`-2` block of the cleared iota defect: `8 ι₋₂` as an exact
polynomial. -/
def iotaAltPolarTwo410 (t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 : F[X])
    (lambda : F) : F[X] :=
  -(20 : F[X]) * a0 * a1 ^ 2
      - (8 : F[X]) * a0 * b42
      + (30 : F[X]) * a1 ^ 2 * a22 ^ 2
      - (40 : F[X]) * a1 ^ 2 * t2 ^ 4
      - (4 : F[X]) * a22 * b2
      + (4 : F[X]) * a22 ^ 2 * b42
      + (2 : F[X]) * b2 * t2 ^ 2
      - (2 : F[X]) * b31 * t2 ^ 3
      + (2 : F[X]) * b42 * t2 ^ 4
      + (14 : F[X]) * a0 * a1 * vis
      + (10 : F[X]) * a1 * a22 * q54
      - (14 : F[X]) * a1 * a22 ^ 2 * vis
      - (10 : F[X]) * a1 * q54 * t2 ^ 2
      + (12 : F[X]) * a1 * t2 ^ 3 * w73
      - (14 : F[X]) * a1 * t2 ^ 4 * vis
      - (16 : F[X]) * a1 ^ 2 * a22 * s22
      + (15 : F[X]) * a1 ^ 2 * a22 * t2 ^ 2
      + (18 : F[X]) * a1 ^ 2 * Polynomial.C lambda * t2 ^ 3
      + (24 : F[X]) * a1 ^ 2 * s22 * t2 ^ 2
      + (6 : F[X]) * a22 * b31 * t2
      - (8 : F[X]) * a22 * b42 * t2 ^ 2
      - (24 : F[X]) * a1 * a22 * t2 * w73
      + (42 : F[X]) * a1 * a22 * t2 ^ 2 * vis
      - (27 : F[X]) * a1 ^ 2 * a22 * Polynomial.C lambda * t2

/-- Order-`-1` block of the cleared iota defect. -/
def iotaAltPolarOne410 (t2 a22 s22 vis w73 q54 a1 a0 b1 : F[X])
    (lambda : F) : F[X] :=
  -(25 : F[X]) * a1 * t2 ^ 7
      - (4 : F[X]) * a22 ^ 3 * w73
      - (2 : F[X]) * b1 * t2
      - (2 : F[X]) * q54 * t2 ^ 5
      + (2 : F[X]) * t2 ^ 6 * w73
      - (2 : F[X]) * t2 ^ 7 * vis
      + (55 : F[X]) * a0 * a1 * t2 ^ 3
      + (12 : F[X]) * a0 * a22 * w73
      + (10 : F[X]) * a0 * q54 * t2
      - (12 : F[X]) * a0 * t2 ^ 2 * w73
      + (14 : F[X]) * a0 * t2 ^ 3 * vis
      + (105 : F[X]) * a1 * a22 * t2 ^ 5
      - (70 : F[X]) * a1 * a22 ^ 2 * t2 ^ 3
      - (9 : F[X]) * a1 * a22 ^ 3 * Polynomial.C lambda
      - (35 : F[X]) * a1 * a22 ^ 3 * t2
      + (9 : F[X]) * a1 * Polynomial.C lambda * t2 ^ 6
      + (16 : F[X]) * a1 * s22 * t2 ^ 5
      + (10 : F[X]) * a22 * q54 * t2 ^ 3
      - (12 : F[X]) * a22 * t2 ^ 4 * w73
      + (14 : F[X]) * a22 * t2 ^ 5 * vis
      - (10 : F[X]) * a22 ^ 2 * q54 * t2
      + (18 : F[X]) * a22 ^ 2 * t2 ^ 2 * w73
      - (28 : F[X]) * a22 ^ 2 * t2 ^ 3 * vis
      + (14 : F[X]) * a22 ^ 3 * t2 * vis
      + (18 : F[X]) * a0 * a1 * a22 * Polynomial.C lambda
      + (30 : F[X]) * a0 * a1 * a22 * t2
      - (27 : F[X]) * a0 * a1 * Polynomial.C lambda * t2 ^ 2
      - (32 : F[X]) * a0 * a1 * s22 * t2
      - (28 : F[X]) * a0 * a22 * t2 * vis
      - (45 : F[X]) * a1 * a22 * Polynomial.C lambda * t2 ^ 4
      - (64 : F[X]) * a1 * a22 * s22 * t2 ^ 3
      + (54 : F[X]) * a1 * a22 ^ 2 * Polynomial.C lambda * t2 ^ 2
      + (48 : F[X]) * a1 * a22 ^ 2 * s22 * t2

/-- Order-`0` block of the cleared iota defect. -/
def iotaAltPolarZero410 (t2 a22 s22 a0 b0 : F[X]) (lambda : F) : F[X] :=
  -(4 : F[X]) * a22 ^ 5
      + (8 : F[X]) * b0
      - (3 : F[X]) * t2 ^ 10
      + (20 : F[X]) * a0 * a22 ^ 3
      + (25 : F[X]) * a0 * t2 ^ 6
      - (20 : F[X]) * a0 ^ 2 * a22
      + (8 : F[X]) * a0 ^ 2 * s22
      - (15 : F[X]) * a0 ^ 2 * t2 ^ 2
      + (25 : F[X]) * a22 * t2 ^ 8
      - (65 : F[X]) * a22 ^ 2 * t2 ^ 6
      + (50 : F[X]) * a22 ^ 3 * t2 ^ 4
      + (4 : F[X]) * a22 ^ 4 * s22
      + (5 : F[X]) * a22 ^ 4 * t2 ^ 2
      + Polynomial.C lambda * t2 ^ 9
      + (2 : F[X]) * s22 * t2 ^ 8
      - (80 : F[X]) * a0 * a22 * t2 ^ 4
      - (16 : F[X]) * a0 * a22 ^ 2 * s22
      + (15 : F[X]) * a0 * a22 ^ 2 * t2 ^ 2
      - (9 : F[X]) * a0 * Polynomial.C lambda * t2 ^ 5
      - (16 : F[X]) * a0 * s22 * t2 ^ 4
      + (9 : F[X]) * a0 ^ 2 * Polynomial.C lambda * t2
      - (9 : F[X]) * a22 * Polynomial.C lambda * t2 ^ 7
      - (16 : F[X]) * a22 * s22 * t2 ^ 6
      + (27 : F[X]) * a22 ^ 2 * Polynomial.C lambda * t2 ^ 5
      + (40 : F[X]) * a22 ^ 2 * s22 * t2 ^ 4
      - (30 : F[X]) * a22 ^ 3 * Polynomial.C lambda * t2 ^ 3
      - (32 : F[X]) * a22 ^ 3 * s22 * t2 ^ 2
      + (9 : F[X]) * a22 ^ 4 * Polynomial.C lambda * t2
      + (36 : F[X]) * a0 * a22 * Polynomial.C lambda * t2 ^ 3
      + (48 : F[X]) * a0 * a22 * s22 * t2 ^ 2
      - (27 : F[X]) * a0 * a22 ^ 2 * Polynomial.C lambda * t2

/-- Polynomial numerator of `8 h³ ι` on the thirteenth-face jet. -/
def localClearedIotaAlternate410
    (h t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 b1 b0 : F[X])
    (lambda : F) : F[X] :=
  iotaAltPolarThree410 t2 vis w73 a1 b42 b31 lambda +
    h * (iotaAltPolarTwo410 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2
        lambda +
      h * (iotaAltPolarOne410 t2 a22 s22 vis w73 q54 a1 a0 b1 lambda +
        h * iotaAltPolarZero410 t2 a22 s22 a0 b0 lambda))

set_option maxHeartbeats 400000000 in
/-- Clearing the tenth-face residual `ι` against `h³` on the
thirteenth-face jet.  All divisibilities are consumed as literal
substitutions, and the four displayed blocks are exact. -/
theorem iotaDefectAlternate_eq_cleared410
    (h t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 b1 b0 a3 a2 b9 b8 b7 b6
      b5 b4 b3 lambda : F)
    (hh : h ≠ 0)
    (ha3 : a3 = h ^ 3 * t2) (ha2 : a2 = h ^ 2 * a22)
    (hN : 5 * a3 * h ^ 6 - 2 * b9 = lambda * h ^ 9)
    (hb8 : b8 = h ^ 8 * s22) (hb7 : b7 = h ^ 6 * vis)
    (hb6 : b6 = h ^ 5 * w73) (hb5 : b5 = h ^ 4 * q54)
    (hb4 : b4 = h ^ 2 * b42) (hb3 : b3 = h * b31) :
    (8 : F) * h ^ 3 *
        iotaResidual410
          (depressedL410 h (quarticDepressionR410 h a3) b9)
          (depressedA410 h (quarticDepressionR410 h a3) a3 a2)
          (depressedB410 h (quarticDepressionR410 h a3) a3 a2 a1)
          (depressedC410 h (quarticDepressionR410 h a3) a3 a2 a1 a0)
          (depressedP410 h (quarticDepressionR410 h a3) b9 b8)
          (depressedQ410 h (quarticDepressionR410 h a3) b9 b8 b7)
          (depressedR410 h (quarticDepressionR410 h a3) b9 b8 b7 b6)
          (depressedS410 h (quarticDepressionR410 h a3) b9 b8 b7 b6 b5)
          (depressedT410 h (quarticDepressionR410 h a3) b9 b8 b7 b6 b5
            b4)
          (depressedU410 h (quarticDepressionR410 h a3) b9 b8 b7 b6 b5
            b4 b3)
          (depressedV410 h (quarticDepressionR410 h a3) b9 b8 b7 b6 b5
            b4 b3 b2)
          (depressedZ410 h (quarticDepressionR410 h a3) b9 b8 b7 b6 b5
            b4 b3 b2 b1 b0) =
      (-(6 : F) * a1 * b31
          + (6 : F) * a1 ^ 2 * w73
          + (3 : F) * a1 ^ 3 * lambda
          + (5 : F) * a1 ^ 3 * t2
          + (8 : F) * a1 * b42 * t2
          - (14 : F) * a1 ^ 2 * t2 * vis) +
        h * ((-(20 : F) * a0 * a1 ^ 2
              - (8 : F) * a0 * b42
              + (30 : F) * a1 ^ 2 * a22 ^ 2
              - (40 : F) * a1 ^ 2 * t2 ^ 4
              - (4 : F) * a22 * b2
              + (4 : F) * a22 ^ 2 * b42
              + (2 : F) * b2 * t2 ^ 2
              - (2 : F) * b31 * t2 ^ 3
              + (2 : F) * b42 * t2 ^ 4
              + (14 : F) * a0 * a1 * vis
              + (10 : F) * a1 * a22 * q54
              - (14 : F) * a1 * a22 ^ 2 * vis
              - (10 : F) * a1 * q54 * t2 ^ 2
              + (12 : F) * a1 * t2 ^ 3 * w73
              - (14 : F) * a1 * t2 ^ 4 * vis
              - (16 : F) * a1 ^ 2 * a22 * s22
              + (15 : F) * a1 ^ 2 * a22 * t2 ^ 2
              + (18 : F) * a1 ^ 2 * lambda * t2 ^ 3
              + (24 : F) * a1 ^ 2 * s22 * t2 ^ 2
              + (6 : F) * a22 * b31 * t2
              - (8 : F) * a22 * b42 * t2 ^ 2
              - (24 : F) * a1 * a22 * t2 * w73
              + (42 : F) * a1 * a22 * t2 ^ 2 * vis
              - (27 : F) * a1 ^ 2 * a22 * lambda * t2) +
          h * ((-(25 : F) * a1 * t2 ^ 7
                - (4 : F) * a22 ^ 3 * w73
                - (2 : F) * b1 * t2
                - (2 : F) * q54 * t2 ^ 5
                + (2 : F) * t2 ^ 6 * w73
                - (2 : F) * t2 ^ 7 * vis
                + (55 : F) * a0 * a1 * t2 ^ 3
                + (12 : F) * a0 * a22 * w73
                + (10 : F) * a0 * q54 * t2
                - (12 : F) * a0 * t2 ^ 2 * w73
                + (14 : F) * a0 * t2 ^ 3 * vis
                + (105 : F) * a1 * a22 * t2 ^ 5
                - (70 : F) * a1 * a22 ^ 2 * t2 ^ 3
                - (9 : F) * a1 * a22 ^ 3 * lambda
                - (35 : F) * a1 * a22 ^ 3 * t2
                + (9 : F) * a1 * lambda * t2 ^ 6
                + (16 : F) * a1 * s22 * t2 ^ 5
                + (10 : F) * a22 * q54 * t2 ^ 3
                - (12 : F) * a22 * t2 ^ 4 * w73
                + (14 : F) * a22 * t2 ^ 5 * vis
                - (10 : F) * a22 ^ 2 * q54 * t2
                + (18 : F) * a22 ^ 2 * t2 ^ 2 * w73
                - (28 : F) * a22 ^ 2 * t2 ^ 3 * vis
                + (14 : F) * a22 ^ 3 * t2 * vis
                + (18 : F) * a0 * a1 * a22 * lambda
                + (30 : F) * a0 * a1 * a22 * t2
                - (27 : F) * a0 * a1 * lambda * t2 ^ 2
                - (32 : F) * a0 * a1 * s22 * t2
                - (28 : F) * a0 * a22 * t2 * vis
                - (45 : F) * a1 * a22 * lambda * t2 ^ 4
                - (64 : F) * a1 * a22 * s22 * t2 ^ 3
                + (54 : F) * a1 * a22 ^ 2 * lambda * t2 ^ 2
                + (48 : F) * a1 * a22 ^ 2 * s22 * t2) +
            h * (-(4 : F) * a22 ^ 5
                + (8 : F) * b0
                - (3 : F) * t2 ^ 10
                + (20 : F) * a0 * a22 ^ 3
                + (25 : F) * a0 * t2 ^ 6
                - (20 : F) * a0 ^ 2 * a22
                + (8 : F) * a0 ^ 2 * s22
                - (15 : F) * a0 ^ 2 * t2 ^ 2
                + (25 : F) * a22 * t2 ^ 8
                - (65 : F) * a22 ^ 2 * t2 ^ 6
                + (50 : F) * a22 ^ 3 * t2 ^ 4
                + (4 : F) * a22 ^ 4 * s22
                + (5 : F) * a22 ^ 4 * t2 ^ 2
                + lambda * t2 ^ 9
                + (2 : F) * s22 * t2 ^ 8
                - (80 : F) * a0 * a22 * t2 ^ 4
                - (16 : F) * a0 * a22 ^ 2 * s22
                + (15 : F) * a0 * a22 ^ 2 * t2 ^ 2
                - (9 : F) * a0 * lambda * t2 ^ 5
                - (16 : F) * a0 * s22 * t2 ^ 4
                + (9 : F) * a0 ^ 2 * lambda * t2
                - (9 : F) * a22 * lambda * t2 ^ 7
                - (16 : F) * a22 * s22 * t2 ^ 6
                + (27 : F) * a22 ^ 2 * lambda * t2 ^ 5
                + (40 : F) * a22 ^ 2 * s22 * t2 ^ 4
                - (30 : F) * a22 ^ 3 * lambda * t2 ^ 3
                - (32 : F) * a22 ^ 3 * s22 * t2 ^ 2
                + (9 : F) * a22 ^ 4 * lambda * t2
                + (36 : F) * a0 * a22 * lambda * t2 ^ 3
                + (48 : F) * a0 * a22 * s22 * t2 ^ 2
                - (27 : F) * a0 * a22 ^ 2 * lambda * t2))) := by
  subst ha3 ha2 hb8 hb7 hb6 hb5 hb4 hb3
  have h2 : (2 : F) ≠ 0 := by norm_num
  have hb9div : b9 = (5 * (h ^ 3 * t2) * h ^ 6 - lambda * h ^ 9) / 2 := by
    field_simp
    linear_combination -hN
  subst hb9div
  simp only [iotaResidual410, alphaResidual410, betaResidual410,
    gammaResidual410, deltaResidual410, epsilonResidual410,
    zetaResidual410, etaResidual410, depressedL410, depressedL810,
    depressedA410, depressedA46, depressedB410, depressedB46,
    depressedC410, depressedC46, depressedP410, depressedP810,
    depressedQ410, depressedQ810, depressedR410, depressedS410,
    depressedT410, depressedU410, depressedV410, depressedZ410,
    quarticDepressionR410, quarticDepressionR46]
  field_simp
  ring

end IotaAltCleared410

/-! ## Source-facing power relation: the cleared defect is `C (8 ι₀) h³` -/

section NonzeroIotaAlternate410

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 120000000 in
/-- The tenth-face residual `ι` descends to the ground field on the
thirteenth-face jet: the cleared defect is a scalar multiple of `h³`.
The scalar is `8 ι₀` and stays arbitrary. -/
theorem nonzeroFace410_iotaAlternatePowerRelation
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
      localClearedIotaAlternate410 h0 t2 a22 s22 vis w73 q54
          (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1)
          (q.coeff 0) lambda =
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
  let b0 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 0)
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
  have hNrat : 5 * a3 * hRF ^ 6 - 2 * b9 =
      RatFunc.C lambda * hRF ^ 9 := by
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
  have hLval :
      depressedL410 hRF (quarticDepressionR410 hRF a3) b9 =
        RatFunc.C (-lambda / 2) := by
    have hL := depressedL410_eq_of_ninthPower hRF a3 b9
      (RatFunc.C lambda) hh (by simpa using hNrat)
    simpa [map_neg, map_div₀, map_ofNat] using hL
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
  have hg_high_src : ∀ n, 10 < n →
      (sourceToRatFunc68 q).coeff n = 0 := by
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
  have hg2 :
      g.coeff 2 =
        depressedV410 hRF (quarticDepressionR410 hRF a3) b9 b8 b7 b6
          b5 b4 b3 b2 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff2_410 (sourceToRatFunc68 q) hRF
      (quarticDepressionR410 hRF a3) hh hgTop hg_high_src]
    simp [depressedV410, quarticDepressionR410, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2]
  have hg0 :
      g.coeff 0 =
        depressedZ410 hRF (quarticDepressionR410 hRF a3) b9 b8 b7 b6
          b5 b4 b3 b2 b1 b0 := by
    dsimp only [g]
    rw [affineDepressAlternate_degreeTen_coeff0_410
      (sourceToRatFunc68 q) hRF (quarticDepressionR410 hRF a3) hh hgTop
      hg_high_src]
    simp [depressedZ410, quarticDepressionR410, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0]
  have hg8' :
      g.coeff 8 =
        depressedP410 hRF (quarticDepressionR410 hRF a3) b9 b8 := by
    dsimp only [g]
    rw [hg8]
    simp [depressedP410, depressedP810, quarticDepressionR410,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8]
  have hg9' : g.coeff 9 = RatFunc.C (-lambda / 2) := by
    dsimp only [g]
    rw [hg9]
    have : -10 * quarticDepressionR410 hRF a3 +
        (sourceToRatFunc68 q).coeff 9 / hRF ^ 9 =
          depressedL410 hRF (quarticDepressionR410 hRF a3) b9 := by
      simp [depressedL410, depressedL810, quarticDepressionR410,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    rw [this, hLval]
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
    simpa [f, g, Polynomial.coeff_C, show (11 : ℕ) ≠ 0 by norm_num]
      using hrow.symm.trans hbr
  have hrow10 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 1) +
          (9 : RatFunc k) * g.coeff 9 *
            ratFuncDerivation68 (f.coeff 2) -
        (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 7) = 0 := by
    have hrow :=
      differentialJacobian_coeff_10_monicQuarticDecic
        ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 10) hbracket
    simpa [f, g, Polynomial.coeff_C, show (10 : ℕ) ≠ 0 by norm_num]
      using hrow.symm.trans hbr
  have hrow9 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 0) +
          (9 : RatFunc k) * g.coeff 9 *
            ratFuncDerivation68 (f.coeff 1) +
        (8 : RatFunc k) * g.coeff 8 *
            ratFuncDerivation68 (f.coeff 2) -
          (2 : RatFunc k) * f.coeff 2 *
            ratFuncDerivation68 (g.coeff 8) -
          (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 6) = 0 := by
    have hrow :=
      differentialJacobian_coeff_9_monicQuarticDecic
        ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 9) hbracket
    simpa [f, g, Polynomial.coeff_C, show (9 : ℕ) ≠ 0 by norm_num]
      using hrow.symm.trans hbr
  have hrow8 :
      (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 0) +
          (8 : RatFunc k) * g.coeff 8 *
            ratFuncDerivation68 (f.coeff 1) +
        (7 : RatFunc k) * g.coeff 7 *
            ratFuncDerivation68 (f.coeff 2) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 8) -
          (2 : RatFunc k) * f.coeff 2 *
            ratFuncDerivation68 (g.coeff 7) -
          (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 5) = 0 := by
    have hrow :=
      differentialJacobian_coeff_8_monicQuarticDecic
        ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 8) hbracket
    simpa [f, g, Polynomial.coeff_C, show (8 : ℕ) ≠ 0 by norm_num]
      using hrow.symm.trans hbr
  have hrow7 :
      (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 0) +
          (7 : RatFunc k) * g.coeff 7 *
            ratFuncDerivation68 (f.coeff 1) +
        (6 : RatFunc k) * g.coeff 6 *
            ratFuncDerivation68 (f.coeff 2) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 7) -
          (2 : RatFunc k) * f.coeff 2 *
            ratFuncDerivation68 (g.coeff 6) -
          (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 4) = 0 := by
    have hrow :=
      differentialJacobian_coeff_7_monicQuarticDecic
        ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 7) hbracket
    simpa [f, g, Polynomial.coeff_C, show (7 : ℕ) ≠ 0 by norm_num]
      using hrow.symm.trans hbr
  have hrow6 :
      (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 0) +
          (6 : RatFunc k) * g.coeff 6 *
            ratFuncDerivation68 (f.coeff 1) +
        (5 : RatFunc k) * g.coeff 5 *
            ratFuncDerivation68 (f.coeff 2) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 6) -
          (2 : RatFunc k) * f.coeff 2 *
            ratFuncDerivation68 (g.coeff 5) -
          (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 3) = 0 := by
    have hrow :=
      differentialJacobian_coeff_6_monicQuarticDecic
        ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 6) hbracket
    simpa [f, g, Polynomial.coeff_C, show (6 : ℕ) ≠ 0 by norm_num]
      using hrow.symm.trans hbr
  have hrow5 :
      (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 0) +
          (5 : RatFunc k) * g.coeff 5 *
            ratFuncDerivation68 (f.coeff 1) +
        (4 : RatFunc k) * g.coeff 4 *
            ratFuncDerivation68 (f.coeff 2) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 5) -
          (2 : RatFunc k) * f.coeff 2 *
            ratFuncDerivation68 (g.coeff 4) -
          (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 2) = 0 := by
    have hrow :=
      differentialJacobian_coeff_5_monicQuarticDecic
        ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 5) hbracket
    simpa [f, g, Polynomial.coeff_C, show (5 : ℕ) ≠ 0 by norm_num]
      using hrow.symm.trans hbr
  have hrow3 :
      (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 0) +
          (3 : RatFunc k) * g.coeff 3 *
            ratFuncDerivation68 (f.coeff 1) +
        (2 : RatFunc k) * g.coeff 2 *
            ratFuncDerivation68 (f.coeff 2) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 3) -
          (2 : RatFunc k) * f.coeff 2 *
            ratFuncDerivation68 (g.coeff 2) -
          (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 0) = 0 := by
    have hrow :=
      differentialJacobian_coeff_3_monicQuarticDecic
        ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 3) hbracket
    simpa [f, g, Polynomial.coeff_C, show (3 : ℕ) ≠ 0 by norm_num]
      using hrow.symm.trans hbr
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
      (f.coeff 2) (f.coeff 1) (g.coeff 7) hLconst
      (by simpa using hrow10)
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
          (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
          (g.coeff 3)) = 0 :=
    zetaResidual410_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
      (g.coeff 6) (g.coeff 5) (g.coeff 3) hLconst halpha0 hbeta0
      hgamma0 hdelta0 (by simpa using hrow6)
  have heta0deriv :
      ratFuncDerivation68
        (etaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
          (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
          (g.coeff 4) (g.coeff 2)) = 0 :=
    etaResidual410_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
      (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 2) hLconst halpha0
      hbeta0 hgamma0 hdelta0 hepsilon0 (by simpa using hrow5)
  have hiotaDeriv :
      ratFuncDerivation68
        (iotaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
          (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
          (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 0)) = 0 :=
    iotaResidualAlternate410_deriv_zero ratFuncDerivation68
      (g.coeff 9) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
      (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
      (g.coeff 2) (g.coeff 0) hLconst halpha0 hbeta0 hgamma0 hdelta0
      hepsilon0 hzeta0 heta0deriv (by simpa using hrow3)
  obtain ⟨iota0, hiota0⟩ :
      ∃ a : k,
        iotaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
            (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
            (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
            (g.coeff 0) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      hiotaDeriv
  have hja3 : a3 = hRF ^ 3 * algebraMap k[X] (RatFunc k) t2 := by
    simp only [a3, hRF, hp3, map_mul, map_pow]
  have hja2 : a2 = hRF ^ 2 * algebraMap k[X] (RatFunc k) a22 := by
    simp only [a2, hRF, hp2, map_mul, map_pow]
  have hjb8 : b8 = hRF ^ 8 * algebraMap k[X] (RatFunc k) s22 := by
    simp only [b8, hRF, hq8, map_mul, map_pow]
  have hjb7 : b7 = hRF ^ 6 * algebraMap k[X] (RatFunc k) vis := by
    simp only [b7, hRF, hq7, map_mul, map_pow]
  have hjb6 : b6 = hRF ^ 5 * algebraMap k[X] (RatFunc k) w73 := by
    simp only [b6, hRF, hq6, map_mul, map_pow]
  have hjb5 : b5 = hRF ^ 4 * algebraMap k[X] (RatFunc k) q54 := by
    simp only [b5, hRF, hq5, map_mul, map_pow]
  have hjb4 : b4 = hRF ^ 2 * algebraMap k[X] (RatFunc k) b42 := by
    simp only [b4, hRF, hq4, map_mul, map_pow]
  have hjb3 : b3 = hRF * algebraMap k[X] (RatFunc k) b31 := by
    simp only [b3, hRF, hq3, map_mul]
  have hbig := iotaDefectAlternate_eq_cleared410 hRF
    (algebraMap k[X] (RatFunc k) t2) (algebraMap k[X] (RatFunc k) a22)
    (algebraMap k[X] (RatFunc k) s22) (algebraMap k[X] (RatFunc k) vis)
    (algebraMap k[X] (RatFunc k) w73) (algebraMap k[X] (RatFunc k) q54)
    a1 a0 (algebraMap k[X] (RatFunc k) b42)
    (algebraMap k[X] (RatFunc k) b31) b2 b1 b0 a3 a2 b9 b8 b7 b6 b5 b4
    b3 (RatFunc.C lambda) hh hja3 hja2 hNrat hjb8 hjb7 hjb6 hjb5 hjb4
    hjb3
  have hf2 : f.coeff 2 =
      depressedA410 hRF (quarticDepressionR410 hRF a3) a3 a2 := by
    dsimp only [f, depressedA410, a3, a2]
    rw [hpDep, coeff_depressedQuartic46_two]
  have hf1 : f.coeff 1 =
      depressedB410 hRF (quarticDepressionR410 hRF a3) a3 a2 a1 := by
    dsimp only [f, depressedB410, a3, a2, a1]
    rw [hpDep, coeff_depressedQuartic46_one]
  have hf0 : f.coeff 0 =
      depressedC410 hRF (quarticDepressionR410 hRF a3) a3 a2 a1
        a0 := by
    dsimp only [f, depressedC410, a3, a2, a1, a0]
    rw [hpDep, coeff_depressedQuartic46_zero]
  have hg9L : g.coeff 9 =
      depressedL410 hRF (quarticDepressionR410 hRF a3) b9 := by
    dsimp only [g]
    rw [hg9]
    simp [depressedL410, depressedL810, quarticDepressionR410,
      sourceToRatFunc68, sourceToRatFunc46, b9]
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedIotaAlternate410 h0 t2 a22 s22 vis w73 q54
            (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1)
            (q.coeff 0) lambda) =
        (8 : RatFunc k) * hRF ^ 3 *
          iotaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
            (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
            (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
            (g.coeff 0) := by
    simpa [localClearedIotaAlternate410, iotaAltPolarThree410,
      iotaAltPolarTwo410, iotaAltPolarOne410, iotaAltPolarZero410,
      map_sub, map_add, map_mul, map_pow, map_ofNat, map_neg,
      RatFunc.algebraMap_C, hRF, a3, a2, a1, a0, b9, b8, b7, b6, b5,
      b4, b3, b2, b1, b0, iotaResidual410, alphaResidual410,
      betaResidual410, gammaResidual410, deltaResidual410,
      epsilonResidual410, zetaResidual410, etaResidual410, hf2, hf1,
      hf0, hg2, hg3, hg4, hg5, hg6, hg7, hg8', hg9L, hg0] using
      hbig.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedIotaAlternate410 h0 t2 a22 s22 vis w73 q54
            (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1)
            (q.coeff 0) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (8 * iota0) * h0 ^ 3) := by
    rw [hclear, hiota0]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat,
      map_add]
    ring
  refine ⟨8 * iota0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

end NonzeroIotaAlternate410

/-! ## Peeling the power relation at the root: the polar audit -/

section IotaAlternatePolarAudit410

variable {k : Type*} [Field k] [CharZero k]

/-- The order-`-3` polar coefficient of `ι` genuinely vanishes at the
root: the power relation kills the block `Δ₃ = 8 ι₋₃`, and on the
twelfth/thirteenth jet that block is `8 · (15/256) p₁³ (λ + 4 t₂)`. -/
theorem iotaAlternate_orderThreeVanishes410
    (h t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 b1 b0 : k[X])
    (lambda a c : k) (hroot : h.eval a = 0)
    (hpow : localClearedIotaAlternate410 h t2 a22 s22 vis w73 q54 a1 a0
        b42 b31 b2 b1 b0 lambda =
      Polynomial.C c * h ^ 3)
    (hT : (64 : k) * vis.eval a - (160 : k) * a1.eval a = 0)
    (hU : (8 : k) * w73.eval a =
      a1.eval a * ((30 : k) * t2.eval a - (9 : k) * lambda))
    (hW : (8 : k) * b42.eval a = (15 : k) * a1.eval a ^ 2)
    (hX : (64 : k) * b31.eval a =
      (15 : k) * a1.eval a ^ 2 *
        ((4 : k) * t2.eval a - (3 : k) * lambda)) :
    a1.eval a ^ 3 * (lambda + (4 : k) * t2.eval a) = 0 := by
  have heval := congrArg (fun r : k[X] => r.eval a) hpow
  have hD3 :
      (iotaAltPolarThree410 t2 vis w73 a1 b42 b31 lambda).eval a =
        0 := by
    simpa [localClearedIotaAlternate410, hroot] using heval
  have h8iota :
      (8 : k) * iotaOrderThree410 (a1.eval a) (t2.eval a) (vis.eval a)
          (w73.eval a) (b31.eval a) (b42.eval a) lambda =
        (iotaAltPolarThree410 t2 vis w73 a1 b42 b31 lambda).eval a := by
    simp only [iotaOrderThree410, iotaAltPolarThree410, eval_add,
      eval_sub, eval_mul, eval_pow, eval_ofNat, eval_C, eval_neg]
    ring
  have h8 : (8 : k) ≠ 0 := by norm_num
  have hval :
      iotaOrderThree410 (a1.eval a) (t2.eval a) (vis.eval a)
          (w73.eval a) (b31.eval a) (b42.eval a) lambda = 0 := by
    have hmul :
        (8 : k) * iotaOrderThree410 (a1.eval a) (t2.eval a)
            (vis.eval a) (w73.eval a) (b31.eval a) (b42.eval a)
            lambda = 0 := by
      rw [h8iota, hD3]
    exact (mul_eq_zero.mp hmul).resolve_left h8
  have hfact := terminalIota_orderThree_onJet410 (a1.eval a)
    (t2.eval a) (vis.eval a) (w73.eval a) (b31.eval a) (b42.eval a)
    lambda hT hU hW hX
  have hz :
      (15 / 256 : k) * a1.eval a ^ 3 *
          (lambda + (4 : k) * t2.eval a) = 0 := by
    rw [← hfact]
    exact hval
  have h15256 : (15 / 256 : k) ≠ 0 := by norm_num
  have hsplit :
      (15 / 256 : k) *
          (a1.eval a ^ 3 * (lambda + (4 : k) * t2.eval a)) = 0 := by
    linear_combination hz
  exact (mul_eq_zero.mp hsplit).resolve_left h15256

/-- The audited split: at the root of the scale, either `p₁(a) = 0` or
`λ + 4 t₂(a) = 0`.  Neither branch is eliminated. -/
theorem iotaAlternate_polarSplit410
    (h t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 b1 b0 : k[X])
    (lambda a c : k) (hroot : h.eval a = 0)
    (hpow : localClearedIotaAlternate410 h t2 a22 s22 vis w73 q54 a1 a0
        b42 b31 b2 b1 b0 lambda =
      Polynomial.C c * h ^ 3)
    (hT : (64 : k) * vis.eval a - (160 : k) * a1.eval a = 0)
    (hU : (8 : k) * w73.eval a =
      a1.eval a * ((30 : k) * t2.eval a - (9 : k) * lambda))
    (hW : (8 : k) * b42.eval a = (15 : k) * a1.eval a ^ 2)
    (hX : (64 : k) * b31.eval a =
      (15 : k) * a1.eval a ^ 2 *
        ((4 : k) * t2.eval a - (3 : k) * lambda)) :
    a1.eval a = 0 ∨ lambda + (4 : k) * t2.eval a = 0 := by
  have hz := iotaAlternate_orderThreeVanishes410 h t2 a22 s22 vis w73
    q54 a1 a0 b42 b31 b2 b1 b0 lambda a c hroot hpow hT hU hW hX
  rcases mul_eq_zero.mp hz with h3 | hlin
  · exact Or.inl ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp h3)
  · exact Or.inr hlin

/-- At order `-2` the power relation does not force `ι₋₂(a)` to vanish:
it ties the `h`-cofactor of the order-`-3` block to the order-`-2`
polar coefficient.  The exact residual is retained. -/
theorem iotaAlternate_orderTwoResidual410
    (h t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 b1 b0 : k[X])
    (lambda a c : k) (hh : h ≠ 0) (hdeg : h.natDegree = 1)
    (hroot : h.eval a = 0)
    (hpow : localClearedIotaAlternate410 h t2 a22 s22 vis w73 q54 a1 a0
        b42 b31 b2 b1 b0 lambda =
      Polynomial.C c * h ^ 3)
    (hT : (64 : k) * vis.eval a - (160 : k) * a1.eval a = 0)
    (hU : (8 : k) * w73.eval a =
      a1.eval a * ((30 : k) * t2.eval a - (9 : k) * lambda))
    (hW : (8 : k) * b42.eval a = (15 : k) * a1.eval a ^ 2)
    (hV : (32 : k) * q54.eval a +
        (40 : k) * a1.eval a * a22.eval a -
        (64 : k) * a1.eval a * s22.eval a -
        (27 : k) * a1.eval a * lambda * t2.eval a +
        (90 : k) * a1.eval a * t2.eval a ^ 2 =
      0)
    (hX : (64 : k) * b31.eval a =
      (15 : k) * a1.eval a ^ 2 *
        ((4 : k) * t2.eval a - (3 : k) * lambda))
    (hY : (256 : k) * b2.eval a =
      a1.eval a ^ 2 *
        ((256 : k) * s22.eval a - (400 : k) * a22.eval a +
          (243 : k) * lambda * t2.eval a -
          (540 : k) * t2.eval a ^ 2)) :
    ∃ w1 : k[X],
      iotaAltPolarThree410 t2 vis w73 a1 b42 b31 lambda = h * w1 ∧
        (128 : k) * w1.eval a +
            (3 : k) * a1.eval a ^ 2 *
              (-(160 : k) * a22.eval a ^ 2 +
                (18 : k) * a22.eval a * lambda * t2.eval a +
                (440 : k) * a22.eval a * t2.eval a ^ 2 -
                (27 : k) * lambda * t2.eval a ^ 3 +
                (256 : k) * s22.eval a * t2.eval a ^ 2 -
                (180 : k) * t2.eval a ^ 4) =
          0 := by
  have heval := congrArg (fun r : k[X] => r.eval a) hpow
  have hD3 :
      (iotaAltPolarThree410 t2 vis w73 a1 b42 b31 lambda).eval a =
        0 := by
    simpa [localClearedIotaAlternate410, hroot] using heval
  obtain ⟨w1, hw1⟩ :
      h ∣ iotaAltPolarThree410 t2 vis w73 a1 b42 b31 lambda :=
    linearPolynomial_dvd_of_eval_eq_zero_410 h _ a hdeg hroot hD3
  refine ⟨w1, hw1, ?_⟩
  have hface :
      localClearedIotaAlternate410 h t2 a22 s22 vis w73 q54 a1 a0 b42
          b31 b2 b1 b0 lambda =
        h * (w1 +
          (iotaAltPolarTwo410 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2
            lambda +
          h * (iotaAltPolarOne410 t2 a22 s22 vis w73 q54 a1 a0 b1
              lambda +
            h * iotaAltPolarZero410 t2 a22 s22 a0 b0 lambda))) := by
    simp only [localClearedIotaAlternate410]
    rw [hw1]
    ring
  have hcanc :
      w1 +
          (iotaAltPolarTwo410 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2
            lambda +
          h * (iotaAltPolarOne410 t2 a22 s22 vis w73 q54 a1 a0 b1
              lambda +
            h * iotaAltPolarZero410 t2 a22 s22 a0 b0 lambda)) =
        Polynomial.C c * h ^ 2 := by
    apply mul_left_cancel₀ hh
    rw [← hface, hpow]
    ring
  have heval2 := congrArg (fun r : k[X] => r.eval a) hcanc
  have htie :
      w1.eval a +
          (iotaAltPolarTwo410 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2
            lambda).eval a =
        0 := by
    simpa [hroot] using heval2
  have h8two :
      (8 : k) * iotaOrderTwo410 (a0.eval a) (a1.eval a) (t2.eval a)
          (a22.eval a) (s22.eval a) (vis.eval a) (w73.eval a)
          (q54.eval a) (b42.eval a) (b31.eval a) (b2.eval a) lambda =
        (iotaAltPolarTwo410 t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2
          lambda).eval a := by
    simp only [iotaOrderTwo410, iotaAltPolarTwo410, eval_add, eval_sub,
      eval_mul, eval_pow, eval_ofNat, eval_C, eval_neg]
    ring
  have hfact2 := terminalIota_orderTwo_onJet410 (a0.eval a)
    (a1.eval a) (t2.eval a) (a22.eval a) (s22.eval a) (vis.eval a)
    (w73.eval a) (q54.eval a) (b42.eval a) (b31.eval a) (b2.eval a)
    lambda hT hU hW hV hX hY
  linear_combination (128 : k) * htie + (128 : k) * h8two -
    (1024 : k) * hfact2

end IotaAlternatePolarAudit410

#print axioms iotaResidualAlternate410_deriv_zero
#print axioms affineDepressAlternate_degreeTen_coeff0_410
#print axioms iotaDefectAlternate_eq_cleared410
#print axioms nonzeroFace410_iotaAlternatePowerRelation
#print axioms iotaAlternate_orderThreeVanishes410
#print axioms iotaAlternate_polarSplit410
#print axioms iotaAlternate_orderTwoResidual410

end Max11DegreeRoutes
