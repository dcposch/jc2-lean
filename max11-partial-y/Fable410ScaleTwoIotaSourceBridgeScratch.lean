import Grok410ScaleTwoTerminalIotaScratch

/-! # Iota source bridge for the normalized `(4,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₃ H³ - 2 q₉ = λ h⁹` with
`h.natDegree = 1`, the terminal file computed the order-`-3` polar
coefficient of the tenth-face residual `ι` as `15 p₁³ (λ + 4 t₂) / 256`
on the twelfth/thirteenth jet, but did not prove that it vanishes: the
degree-`3` first-integral identity `d ι = 0` was never established, and
`ι` was never traced back to the literal depressed source.  This file
closes that gap.

First, `iotaResidual410_deriv_zero` proves the exact first-integral
identity: on the depressed row
`4 T C' + 3 U B' + 2 V A' - B U' - 2 A V' - 4 Z' = 0` and the second-
through eighth-face integrals `α, …, η`, the residual `ι` is a
differential constant.  No first integral is constructed for the
degree-`0` row `W C' - B Z' = j`, which is not exact.

Second, on the thirteenth-face jet `p₃ = h³ t₂`, `p₂ = h² a₂₂`,
`q₈ = h⁸ s₂₂`, `q₇ = h⁶ v`, `q₆ = h⁵ w`, `q₅ = h⁴ u`, `q₄ = h² b₄₂`,
`q₃ = h b₃₁` the residual `ι` clears against `h³` exactly:
`8 h³ ι = D₃ + h (D₂ + h (D₁ + h D₀))` with explicit polynomial blocks,
where `D₃ = 8 ι₋₃` and `D₂ = 8 ι₋₂` are the polar numerators of the
terminal file.  Tracing `ι` through the affine depression of the literal
source (`nonzeroFace410_iotaResidualPowerRelation`) shows the cleared
defect is a scalar multiple of `h³`.

Consequently the order-`-3` polar coefficient genuinely vanishes at the
root of the degree-one scale: `p₁(a)³ (λ + 4 t₂(a)) = 0`, so the
nonzero face splits into the two branches `p₁(a) = 0` and
`λ + 4 t₂(a) = 0`; neither branch is eliminated.  At order `-2` the
power relation does not force `ι₋₂(a)` to vanish: it ties the
`h`-cofactor `w₁` of the order-`-3` block to
`128 w₁(a) + 3 p₁(a)² (-160 a₂₂² + 18 λ a₂₂ t₂ + 440 a₂₂ t₂² - 27 λ t₂³
+ 256 s₂₂ t₂² - 180 t₂⁴)(a) = 0`, and that exact residual is retained.
The ground constants `α, β, γ, δ` are not touched.

No total-degree or twice-prime theorem is used.  The aligned face
`N = 0` is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## The degree-`3` row first integral: `d ι = 0` -/

section IotaDerivZero410

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

set_option maxHeartbeats 16000000 in
/-- The tenth-face residual `ι` is an exact first integral of the
degree-`3` depressed Jacobian row on the second- through eighth-face
integrals. -/
theorem iotaResidual410_deriv_zero
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
  have h128 : d (128 : F) = 0 := d.map_natCast 128
  have h135 : d (135 : F) = 0 := d.map_natCast 135
  have h175 : d (175 : F) = 0 := d.map_natCast 175
  have h231 : d (231 : F) = 0 := d.map_natCast 231
  have h385 : d (385 : F) = 0 := d.map_natCast 385
  have h2inv : d (2⁻¹ : F) = 0 := by
    simp [Derivation.leibniz_inv, h2]
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
  have h154 : d (15 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h15]
  have h158 : d (15 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h15]
  have h258 : d (25 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h25]
  have h4932 : d (49 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h49]
  have h6316 : d (63 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h63]
  have h6332 : d (63 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h63]
  have h358 : d (35 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h35]
  have h231128 : d (231 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h231]
  have h38564 : d (385 / 64 : F) = 0 := by
    have h64 : d (64 : F) = 0 := d.map_natCast 64
    simp [Derivation.leibniz_div, h64, h385]
  have h98 : d (9 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h9]
  have h218 : d (21 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h21]
  have h278 : d (27 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h27]
  have h7516 : d (75 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h75]
  have h13532 : d (135 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32, h135]
  have h175128 : d (175 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h175]
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
    have h458 : d (45 / 8 : F) = 0 := by
      simp [Derivation.leibniz_div, h8, h45]
    have h8132 : d (81 / 32 : F) = 0 := by
      have h81 : d (81 : F) = 0 := d.map_natCast 81
      simp [Derivation.leibniz_div, h32, h81]
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
    have h693128 : d (693 / 128 : F) = 0 := by
      have h693 : d (693 : F) = 0 := d.map_natCast 693
      simp [Derivation.leibniz_div, h128, h693]
    simp [map_sub, map_add, Derivation.leibniz, h2, h3, h4, h5, h7, h8,
      h16, h32, h54, h32div, h74, h72, h4932, h6316, h6332, h358,
      h231128, h38564, hL, hsqA, hsqB, hcube, zero_mul, add_zero,
      mul_zero] at hdg
    linear_combination hdg
  have hV0 :
      d V0 + (175 / 128 : F) * ((4 : F) * (A * A * A) * d A) -
          (5 / 4 : F) *
            (P * ((3 : F) * (A * A) * d A) + (A * A * A) * d P) -
          (135 / 32 : F) * L *
            (((2 : F) * A * d A) * B + (A * A) * d B) -
          (75 / 16 : F) * (((2 : F) * A * d A) * C0 + (A * A) * d C0) +
          (9 / 8 : F) * (((2 : F) * A * d A) * R + (A * A) * d R) -
          (75 / 16 : F) * ((B * B) * d A + A * ((2 : F) * B * d B)) +
          (21 / 8 : F) * (B * Q * d A + A * Q * d B + A * B * d Q) +
          (3 : F) * (C0 * P * d A + A * P * d C0 + A * C0 * d P) -
          (T0 * d A + A * d T0) +
          (3 / 2 : F) * (((2 : F) * B * d B) * P + (B * B) * d P) +
          (27 / 8 : F) * L * (C0 * d B + B * d C0) -
          (5 / 4 : F) * (S0 * d B + B * d S0) +
          (15 / 8 : F) * ((2 : F) * C0 * d C0) -
          (3 / 2 : F) * (R * d C0 + C0 * d R) = 0 := by
    have hexp :
        etaResidual410 L A B C0 P Q R S0 T0 V0 =
          V0 + (175 / 128 : F) * (A * A * A * A) -
            (5 / 4 : F) * (A * A * A) * P -
            (135 / 32 : F) * L * (A * A) * B -
            (75 / 16 : F) * (A * A) * C0 +
            (9 / 8 : F) * (A * A) * R -
            (75 / 16 : F) * A * (B * B) +
            (21 / 8 : F) * A * B * Q +
            (3 : F) * A * C0 * P - A * T0 +
            (3 / 2 : F) * (B * B) * P +
            (27 / 8 : F) * L * B * C0 -
            (5 / 4 : F) * B * S0 +
            (15 / 8 : F) * (C0 * C0) -
            (3 / 2 : F) * C0 * R := by
      simp only [etaResidual410, alphaResidual410, betaResidual410,
        gammaResidual410, deltaResidual410, epsilonResidual410, pow_two,
        pow_three]
      ring
    have hdg :
        d (V0 + (175 / 128 : F) * (A * A * A * A) -
            (5 / 4 : F) * (A * A * A) * P -
            (135 / 32 : F) * L * (A * A) * B -
            (75 / 16 : F) * (A * A) * C0 +
            (9 / 8 : F) * (A * A) * R -
            (75 / 16 : F) * A * (B * B) +
            (21 / 8 : F) * A * B * Q +
            (3 : F) * A * C0 * P - A * T0 +
            (3 / 2 : F) * (B * B) * P +
            (27 / 8 : F) * L * B * C0 -
            (5 / 4 : F) * B * S0 +
            (15 / 8 : F) * (C0 * C0) -
            (3 / 2 : F) * C0 * R) = 0 := by
      simpa [hexp] using heta
    simp [map_sub, map_add, Derivation.leibniz, h2, h3, h54, h98, h158,
      h218, h278, h7516, h13532, h175128, h32div, hL, hsqA, hsqB, hsqC,
      hcube, hfourth, zero_mul, add_zero, mul_zero] at hdg
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
      d V0 =
        -(175 / 128 : F) * ((4 : F) * (A * A * A) * d A) +
          (5 / 4 : F) *
            (P * ((3 : F) * (A * A) * d A) + (A * A * A) * d P) +
          (135 / 32 : F) * L *
            (((2 : F) * A * d A) * B + (A * A) * d B) +
          (75 / 16 : F) * (((2 : F) * A * d A) * C0 + (A * A) * d C0) -
          (9 / 8 : F) * (((2 : F) * A * d A) * R + (A * A) * d R) +
          (75 / 16 : F) * ((B * B) * d A + A * ((2 : F) * B * d B)) -
          (21 / 8 : F) * (B * Q * d A + A * Q * d B + A * B * d Q) -
          (3 : F) * (C0 * P * d A + A * P * d C0 + A * C0 * d P) +
          (T0 * d A + A * d T0) -
          (3 / 2 : F) * (((2 : F) * B * d B) * P + (B * B) * d P) -
          (27 / 8 : F) * L * (C0 * d B + B * d C0) +
          (5 / 4 : F) * (S0 * d B + B * d S0) -
          (15 / 8 : F) * ((2 : F) * C0 * d C0) +
          (3 / 2 : F) * (R * d C0 + C0 * d R) := by
    linear_combination hV0
  have hZderiv :
      d Z0 = T0 * d C0 + (3 / 4 : F) * U0 * d B +
        (1 / 2 : F) * V0 * d A - (1 / 4 : F) * B * d U0 -
        (1 / 2 : F) * A * d V0 := by
    linear_combination (-1 / 4 : F) * hrow
  have htarget :
      d Z0 - (1 / 2 : F) * (V0 * d A + A * d V0) -
          (3 / 4 : F) * (U0 * d B + B * d U0) -
          (T0 * d C0 + C0 * d T0) +
          (1 / 2 : F) * (((2 : F) * A * d A) * T0 + (A * A) * d T0) +
          (5 / 4 : F) * (B * S0 * d A + A * S0 * d B + A * B * d S0) +
          (3 / 2 : F) * (C0 * R * d A + A * R * d C0 + A * C0 * d R) +
          (3 / 4 : F) * (((2 : F) * B * d B) * R + (B * B) * d R) +
          (7 / 4 : F) * (C0 * Q * d B + B * Q * d C0 + B * C0 * d Q) +
          ((C0 * C0) * d P + P * ((2 : F) * C0 * d C0)) +
          (1 / 2 : F) *
            (((4 : F) * (A * A * A) * d A) * P + (A * A * A * A) * d P) -
          (1 / 2 : F) *
            (((3 : F) * (A * A) * d A) * R + (A * A * A) * d R) -
          (7 / 4 : F) *
            (((2 : F) * A * d A) * B * Q + (A * A) * Q * d B +
              (A * A) * B * d Q) -
          (2 : F) *
            (((2 : F) * A * d A) * C0 * P + (A * A) * P * d C0 +
              (A * A) * C0 * d P) -
          (2 : F) *
            ((B * B) * P * d A + A * P * ((2 : F) * B * d B) +
              A * (B * B) * d P) +
          (9 / 4 : F) * L *
            (((3 : F) * (A * A) * d A) * B + (A * A * A) * d B) -
          (9 / 2 : F) * L * (B * C0 * d A + A * C0 * d B + A * B * d C0) -
          (3 / 4 : F) * L * ((3 : F) * (B * B) * d B) -
          (1 / 2 : F) * ((5 : F) * (A * A * A * A) * d A) +
          (5 / 2 : F) *
            (((3 : F) * (A * A) * d A) * C0 + (A * A * A) * d C0) +
          (15 / 4 : F) *
            (((2 : F) * A * d A) * (B * B) + (A * A) * ((2 : F) * B * d B)) -
          (5 / 2 : F) * ((C0 * C0) * d A + A * ((2 : F) * C0 * d C0)) -
          (5 / 2 : F) * (((2 : F) * B * d B) * C0 + (B * B) * d C0) =
        0 := by
    rw [hZderiv, hVderiv, hUderiv, hTderiv, hSderiv, hRderiv, hQderiv,
      hPderiv]
    ring
  have hexp :
      iotaResidual410 L A B C0 P Q R S0 T0 U0 V0 Z0 =
        Z0 - (1 / 2 : F) * A * V0 - (3 / 4 : F) * B * U0 - C0 * T0 +
          (1 / 2 : F) * (A * A) * T0 + (5 / 4 : F) * A * B * S0 +
          (3 / 2 : F) * A * C0 * R + (3 / 4 : F) * (B * B) * R +
          (7 / 4 : F) * B * C0 * Q + P * (C0 * C0) +
          (1 / 2 : F) * (A * A * A * A) * P -
          (1 / 2 : F) * (A * A * A) * R -
          (7 / 4 : F) * (A * A) * B * Q -
          (2 : F) * (A * A) * C0 * P -
          (2 : F) * A * (B * B) * P +
          (9 / 4 : F) * L * (A * A * A) * B -
          (9 / 2 : F) * L * A * B * C0 -
          (3 / 4 : F) * L * (B * B * B) -
          (1 / 2 : F) * (A * A * A * A * A) +
          (5 / 2 : F) * (A * A * A) * C0 +
          (15 / 4 : F) * (A * A) * (B * B) -
          (5 / 2 : F) * A * (C0 * C0) -
          (5 / 2 : F) * (B * B) * C0 := by
    simp only [iotaResidual410, alphaResidual410, betaResidual410,
      gammaResidual410, deltaResidual410, epsilonResidual410,
      zetaResidual410, etaResidual410, pow_two, pow_three]
    ring
  rw [hexp]
  simp [map_sub, map_add, Derivation.leibniz, h2, h3, h4, h5, h2inv,
    h34, h54, h32div, h74, h94, h92, h154, h52, hL, hsqA, hsqB, hsqC,
    hcube, hfourth, hfifth, hcubeB, zero_mul, add_zero, mul_zero]
  linear_combination htarget

end IotaDerivZero410

/-! ## Decic `z⁰` coefficient of the affine depression -/

section AffineDecic410Bridge

variable {k : Type*} [Field k] [CharZero k]

/-- The `z⁰` coefficient of the affine depression of a degree-ten
source. -/
theorem affineDepress_degreeTen_coeff0_410
    (p : (RatFunc k)[X]) (h r : RatFunc k) (hh : h ≠ 0)
    (hp10 : p.coeff 10 = h ^ 10)
    (hp_high : ∀ n, 10 < n → p.coeff n = 0) :
    (affineDepress68 h r p).coeff 0 =
      r ^ 10 - (p.coeff 9 / h ^ 9) * r ^ 9 +
        (p.coeff 8 / h ^ 8) * r ^ 8 -
        (p.coeff 7 / h ^ 7) * r ^ 7 +
        (p.coeff 6 / h ^ 6) * r ^ 6 -
        (p.coeff 5 / h ^ 5) * r ^ 5 +
        (p.coeff 4 / h ^ 4) * r ^ 4 -
        (p.coeff 3 / h ^ 3) * r ^ 3 +
        (p.coeff 2 / h ^ 2) * r ^ 2 -
        (p.coeff 1 / h) * r + p.coeff 0 := by
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
  have hlow0 :
      (plow.comp ((X - C r) * C h⁻¹)).coeff 0 = p.coeff 0 := by
    have hC : plow = C (plow.coeff 0) :=
      Polynomial.eq_C_of_natDegree_le_zero hplowDeg
    have hcoeff0 : plow.coeff 0 = p.coeff 0 := by
      simp [plow]
    rw [hC, Polynomial.C_comp, Polynomial.coeff_C, if_pos rfl, hcoeff0]
  have h10_0 :
      ((C (p.coeff 10) * X ^ 10).comp ((X - C r) * C h⁻¹)).coeff 0 =
        r ^ 10 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 10) h r 10 0 hh]
    have hle : (0 : ℕ) ≤ 10 := by omega
    have hbin : (10 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hp10, hbin, pow_zero]
    field_simp [hh]; ring
  have h9_0 :
      ((C (p.coeff 9) * X ^ 9).comp ((X - C r) * C h⁻¹)).coeff 0 =
        -(p.coeff 9 / h ^ 9) * r ^ 9 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 9) h r 9 0 hh]
    have hle : (0 : ℕ) ≤ 9 := by omega
    have hbin : (9 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero]
    field_simp [hh]; ring
  have h8_0 :
      ((C (p.coeff 8) * X ^ 8).comp ((X - C r) * C h⁻¹)).coeff 0 =
        (p.coeff 8 / h ^ 8) * r ^ 8 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 8) h r 8 0 hh]
    have hle : (0 : ℕ) ≤ 8 := by omega
    have hbin : (8 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero]
    field_simp [hh]; ring
  have h7_0 :
      ((C (p.coeff 7) * X ^ 7).comp ((X - C r) * C h⁻¹)).coeff 0 =
        -(p.coeff 7 / h ^ 7) * r ^ 7 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 7) h r 7 0 hh]
    have hle : (0 : ℕ) ≤ 7 := by omega
    have hbin : (7 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero]
    field_simp [hh]; ring
  have h6_0 :
      ((C (p.coeff 6) * X ^ 6).comp ((X - C r) * C h⁻¹)).coeff 0 =
        (p.coeff 6 / h ^ 6) * r ^ 6 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 6) h r 6 0 hh]
    have hle : (0 : ℕ) ≤ 6 := by omega
    have hbin : (6 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero]
    field_simp [hh]; ring
  have h5_0 :
      ((C (p.coeff 5) * X ^ 5).comp ((X - C r) * C h⁻¹)).coeff 0 =
        -(p.coeff 5 / h ^ 5) * r ^ 5 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 5) h r 5 0 hh]
    have hle : (0 : ℕ) ≤ 5 := by omega
    have hbin : (5 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero]
    field_simp [hh]; ring
  have h4_0 :
      ((C (p.coeff 4) * X ^ 4).comp ((X - C r) * C h⁻¹)).coeff 0 =
        (p.coeff 4 / h ^ 4) * r ^ 4 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 4) h r 4 0 hh]
    have hle : (0 : ℕ) ≤ 4 := by omega
    have hbin : (4 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero]
    field_simp [hh]; ring
  have h3_0 :
      ((C (p.coeff 3) * X ^ 3).comp ((X - C r) * C h⁻¹)).coeff 0 =
        -(p.coeff 3 / h ^ 3) * r ^ 3 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 3) h r 3 0 hh]
    have hle : (0 : ℕ) ≤ 3 := by omega
    have hbin : (3 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero, pow_three]
    field_simp [hh]; ring
  have h2_0 :
      ((C (p.coeff 2) * X ^ 2).comp ((X - C r) * C h⁻¹)).coeff 0 =
        (p.coeff 2 / h ^ 2) * r ^ 2 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 2) h r 2 0 hh]
    have hle : (0 : ℕ) ≤ 2 := by omega
    have hbin : (2 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero, pow_two]
    field_simp [hh]; ring
  have h1_0 :
      ((C (p.coeff 1) * X ^ 1).comp ((X - C r) * C h⁻¹)).coeff 0 =
        -(p.coeff 1 / h) * r := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 1) h r 1 0 hh]
    have hle : (0 : ℕ) ≤ 1 := by omega
    have hbin : (1 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero, pow_one]
    field_simp [hh]; ring
  rw [hq, coeff_add, coeff_add, coeff_add, coeff_add, coeff_add,
    coeff_add, coeff_add, coeff_add, coeff_add, coeff_add, h10_0, h9_0,
    h8_0, h7_0, h6_0, h5_0, h4_0, h3_0, h2_0, h1_0, hlow0]
  ring

end AffineDecic410Bridge

/-! ## Exact `h³` clearing of `ι` on the thirteenth-face jet -/

section IotaClearing410

variable {F : Type*} [Field F] [CharZero F]

/-- Exact denominator clearing for the depressed decic `z⁰` coordinate
on the ninth-power face. -/
theorem depressedZ410_eq_cleared
    (h a3 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a3 * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    depressedZ410 h (quarticDepressionR410 h a3) b9 b8 b7 b6 b5 b4 b3
        b2 b1 b0 =
      (-(9 : F) * a3 ^ 10 * h ^ 2 + (2 : F) * lambda * a3 ^ 9 * h ^ 5 +
          (16 : F) * a3 ^ 8 * b8 - (64 : F) * a3 ^ 7 * b7 * h ^ 4 +
          (256 : F) * a3 ^ 6 * b6 * h ^ 8 -
          (1024 : F) * a3 ^ 5 * b5 * h ^ 12 +
          (4096 : F) * a3 ^ 4 * b4 * h ^ 16 -
          (16384 : F) * a3 ^ 3 * b3 * h ^ 20 +
          (65536 : F) * a3 ^ 2 * b2 * h ^ 24 -
          (262144 : F) * a3 * b1 * h ^ 28 +
          (1048576 : F) * b0 * h ^ 32) /
        ((1048576 : F) * h ^ 32) := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h1048576 : (1048576 : F) ≠ 0 := by norm_num
  have hh3 : h ^ 3 ≠ 0 := pow_ne_zero 3 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh32 : h ^ 32 ≠ 0 := pow_ne_zero 32 hh
  have hb9 : 2 * b9 = 5 * a3 * h ^ 6 - lambda * h ^ 9 := by
    linear_combination -hN
  have hb9div : b9 = (5 * a3 * h ^ 6 - lambda * h ^ 9) / 2 :=
    eq_div_of_mul_eq h2 (by rw [mul_comm]; exact hb9)
  rw [hb9div]
  simp only [depressedZ410, quarticDepressionR410, quarticDepressionR46]
  field_simp [hh]
  ring

/-- Order-`-3` numerator block of the cleared `ι`: eight times the
terminal order-`-3` polar coefficient. -/
def iotaPolarThreeNumerator410 (t2 vis w73 a1 b42 b31 : F[X])
    (lambda : F) : F[X] :=
  (3 : F[X]) * a1 ^ 3 * Polynomial.C lambda +
    (5 : F[X]) * a1 ^ 3 * t2 -
    (14 : F[X]) * a1 ^ 2 * vis * t2 +
    (6 : F[X]) * a1 ^ 2 * w73 +
    (8 : F[X]) * a1 * b42 * t2 -
    (6 : F[X]) * a1 * b31

/-- Order-`-2` numerator block of the cleared `ι`: eight times the
terminal order-`-2` polar coefficient. -/
def iotaPolarTwoNumerator410 (t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 :
    F[X]) (lambda : F) : F[X] :=
  -(20 : F[X]) * a0 * a1 ^ 2 +
    (14 : F[X]) * a0 * a1 * vis -
    (8 : F[X]) * a0 * b42 +
    (30 : F[X]) * a1 ^ 2 * a22 ^ 2 -
    (16 : F[X]) * a1 ^ 2 * a22 * s22 -
    (27 : F[X]) * a1 ^ 2 * a22 * Polynomial.C lambda * t2 +
    (15 : F[X]) * a1 ^ 2 * a22 * t2 ^ 2 +
    (24 : F[X]) * a1 ^ 2 * s22 * t2 ^ 2 +
    (18 : F[X]) * a1 ^ 2 * Polynomial.C lambda * t2 ^ 3 -
    (40 : F[X]) * a1 ^ 2 * t2 ^ 4 -
    (14 : F[X]) * a1 * a22 ^ 2 * vis +
    (42 : F[X]) * a1 * a22 * vis * t2 ^ 2 -
    (24 : F[X]) * a1 * a22 * w73 * t2 +
    (10 : F[X]) * a1 * a22 * q54 -
    (14 : F[X]) * a1 * vis * t2 ^ 4 +
    (12 : F[X]) * a1 * w73 * t2 ^ 3 -
    (10 : F[X]) * a1 * q54 * t2 ^ 2 +
    (4 : F[X]) * a22 ^ 2 * b42 -
    (8 : F[X]) * a22 * b42 * t2 ^ 2 +
    (6 : F[X]) * a22 * b31 * t2 -
    (4 : F[X]) * a22 * b2 +
    (2 : F[X]) * b42 * t2 ^ 4 -
    (2 : F[X]) * b31 * t2 ^ 3 +
    (2 : F[X]) * b2 * t2 ^ 2

/-- Order-`-1` numerator block of the cleared `ι`. -/
def iotaPolarOneNumerator410 (t2 a22 s22 vis w73 q54 a1 a0 b1 : F[X])
    (lambda : F) : F[X] :=
  (18 : F[X]) * a0 * a1 * a22 * Polynomial.C lambda +
    (30 : F[X]) * a0 * a1 * a22 * t2 -
    (32 : F[X]) * a0 * a1 * s22 * t2 -
    (27 : F[X]) * a0 * a1 * Polynomial.C lambda * t2 ^ 2 +
    (55 : F[X]) * a0 * a1 * t2 ^ 3 -
    (28 : F[X]) * a0 * a22 * vis * t2 +
    (12 : F[X]) * a0 * a22 * w73 +
    (14 : F[X]) * a0 * vis * t2 ^ 3 -
    (12 : F[X]) * a0 * w73 * t2 ^ 2 +
    (10 : F[X]) * a0 * q54 * t2 -
    (9 : F[X]) * a1 * a22 ^ 3 * Polynomial.C lambda -
    (35 : F[X]) * a1 * a22 ^ 3 * t2 +
    (48 : F[X]) * a1 * a22 ^ 2 * s22 * t2 +
    (54 : F[X]) * a1 * a22 ^ 2 * Polynomial.C lambda * t2 ^ 2 -
    (70 : F[X]) * a1 * a22 ^ 2 * t2 ^ 3 -
    (64 : F[X]) * a1 * a22 * s22 * t2 ^ 3 -
    (45 : F[X]) * a1 * a22 * Polynomial.C lambda * t2 ^ 4 +
    (105 : F[X]) * a1 * a22 * t2 ^ 5 +
    (16 : F[X]) * a1 * s22 * t2 ^ 5 +
    (9 : F[X]) * a1 * Polynomial.C lambda * t2 ^ 6 -
    (25 : F[X]) * a1 * t2 ^ 7 +
    (14 : F[X]) * a22 ^ 3 * vis * t2 -
    (4 : F[X]) * a22 ^ 3 * w73 -
    (28 : F[X]) * a22 ^ 2 * vis * t2 ^ 3 +
    (18 : F[X]) * a22 ^ 2 * w73 * t2 ^ 2 -
    (10 : F[X]) * a22 ^ 2 * q54 * t2 +
    (14 : F[X]) * a22 * vis * t2 ^ 5 -
    (12 : F[X]) * a22 * w73 * t2 ^ 4 +
    (10 : F[X]) * a22 * q54 * t2 ^ 3 -
    (2 : F[X]) * vis * t2 ^ 7 +
    (2 : F[X]) * w73 * t2 ^ 6 -
    (2 : F[X]) * q54 * t2 ^ 5 -
    (2 : F[X]) * b1 * t2

/-- Regular (order-`0`) numerator block of the cleared `ι`. -/
def iotaRegularNumerator410 (t2 a22 s22 a0 b0 : F[X]) (lambda : F) :
    F[X] :=
  -(20 : F[X]) * a0 ^ 2 * a22 +
    (8 : F[X]) * a0 ^ 2 * s22 +
    (9 : F[X]) * a0 ^ 2 * Polynomial.C lambda * t2 -
    (15 : F[X]) * a0 ^ 2 * t2 ^ 2 +
    (20 : F[X]) * a0 * a22 ^ 3 -
    (16 : F[X]) * a0 * a22 ^ 2 * s22 -
    (27 : F[X]) * a0 * a22 ^ 2 * Polynomial.C lambda * t2 +
    (15 : F[X]) * a0 * a22 ^ 2 * t2 ^ 2 +
    (48 : F[X]) * a0 * a22 * s22 * t2 ^ 2 +
    (36 : F[X]) * a0 * a22 * Polynomial.C lambda * t2 ^ 3 -
    (80 : F[X]) * a0 * a22 * t2 ^ 4 -
    (16 : F[X]) * a0 * s22 * t2 ^ 4 -
    (9 : F[X]) * a0 * Polynomial.C lambda * t2 ^ 5 +
    (25 : F[X]) * a0 * t2 ^ 6 -
    (4 : F[X]) * a22 ^ 5 +
    (4 : F[X]) * a22 ^ 4 * s22 +
    (9 : F[X]) * a22 ^ 4 * Polynomial.C lambda * t2 +
    (5 : F[X]) * a22 ^ 4 * t2 ^ 2 -
    (32 : F[X]) * a22 ^ 3 * s22 * t2 ^ 2 -
    (30 : F[X]) * a22 ^ 3 * Polynomial.C lambda * t2 ^ 3 +
    (50 : F[X]) * a22 ^ 3 * t2 ^ 4 +
    (40 : F[X]) * a22 ^ 2 * s22 * t2 ^ 4 +
    (27 : F[X]) * a22 ^ 2 * Polynomial.C lambda * t2 ^ 5 -
    (65 : F[X]) * a22 ^ 2 * t2 ^ 6 -
    (16 : F[X]) * a22 * s22 * t2 ^ 6 -
    (9 : F[X]) * a22 * Polynomial.C lambda * t2 ^ 7 +
    (25 : F[X]) * a22 * t2 ^ 8 +
    (2 : F[X]) * s22 * t2 ^ 8 +
    (8 : F[X]) * b0 +
    Polynomial.C lambda * t2 ^ 9 -
    (3 : F[X]) * t2 ^ 10

/-- Polynomial numerator of `8 h³ ι` on the thirteenth-face jet, in
`h`-nested form. -/
def localClearedIotaResidual410 (h t2 a22 s22 vis w73 q54 a1 a0 b42 b31
    b2 b1 b0 : F[X]) (lambda : F) : F[X] :=
  iotaPolarThreeNumerator410 t2 vis w73 a1 b42 b31 lambda +
    h * (iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b42 b31
        b2 lambda +
      h * (iotaPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b1
          lambda +
        h * iotaRegularNumerator410 t2 a22 s22 a0 b0 lambda))

set_option maxHeartbeats 80000000 in
/-- Exact `h³` clearing of the tenth-face residual `ι` on the
thirteenth-face jet substitutions. -/
theorem iotaDefect_eq_cleared410
    (h t2 a22 s22 vis w73 q54 a1 a0 b42 b31 b2 b1 b0 b9 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * (h ^ 3 * t2) * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    (8 : F) * h ^ 3 *
        iotaResidual410
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
          (depressedV410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
            (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
            (h ^ 2 * b42) (h * b31) b2)
          (depressedZ410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
            (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
            (h ^ 2 * b42) (h * b31) b2 b1 b0) =
      ((3 : F) * a1 ^ 3 * lambda +
          (5 : F) * a1 ^ 3 * t2 -
          (14 : F) * a1 ^ 2 * vis * t2 +
          (6 : F) * a1 ^ 2 * w73 +
          (8 : F) * a1 * b42 * t2 -
          (6 : F) * a1 * b31) +
        h * ((-(20 : F) * a0 * a1 ^ 2 +
            (14 : F) * a0 * a1 * vis -
            (8 : F) * a0 * b42 +
            (30 : F) * a1 ^ 2 * a22 ^ 2 -
            (16 : F) * a1 ^ 2 * a22 * s22 -
            (27 : F) * a1 ^ 2 * a22 * lambda * t2 +
            (15 : F) * a1 ^ 2 * a22 * t2 ^ 2 +
            (24 : F) * a1 ^ 2 * s22 * t2 ^ 2 +
            (18 : F) * a1 ^ 2 * lambda * t2 ^ 3 -
            (40 : F) * a1 ^ 2 * t2 ^ 4 -
            (14 : F) * a1 * a22 ^ 2 * vis +
            (42 : F) * a1 * a22 * vis * t2 ^ 2 -
            (24 : F) * a1 * a22 * w73 * t2 +
            (10 : F) * a1 * a22 * q54 -
            (14 : F) * a1 * vis * t2 ^ 4 +
            (12 : F) * a1 * w73 * t2 ^ 3 -
            (10 : F) * a1 * q54 * t2 ^ 2 +
            (4 : F) * a22 ^ 2 * b42 -
            (8 : F) * a22 * b42 * t2 ^ 2 +
            (6 : F) * a22 * b31 * t2 -
            (4 : F) * a22 * b2 +
            (2 : F) * b42 * t2 ^ 4 -
            (2 : F) * b31 * t2 ^ 3 +
            (2 : F) * b2 * t2 ^ 2) +
          h * (((18 : F) * a0 * a1 * a22 * lambda +
              (30 : F) * a0 * a1 * a22 * t2 -
              (32 : F) * a0 * a1 * s22 * t2 -
              (27 : F) * a0 * a1 * lambda * t2 ^ 2 +
              (55 : F) * a0 * a1 * t2 ^ 3 -
              (28 : F) * a0 * a22 * vis * t2 +
              (12 : F) * a0 * a22 * w73 +
              (14 : F) * a0 * vis * t2 ^ 3 -
              (12 : F) * a0 * w73 * t2 ^ 2 +
              (10 : F) * a0 * q54 * t2 -
              (9 : F) * a1 * a22 ^ 3 * lambda -
              (35 : F) * a1 * a22 ^ 3 * t2 +
              (48 : F) * a1 * a22 ^ 2 * s22 * t2 +
              (54 : F) * a1 * a22 ^ 2 * lambda * t2 ^ 2 -
              (70 : F) * a1 * a22 ^ 2 * t2 ^ 3 -
              (64 : F) * a1 * a22 * s22 * t2 ^ 3 -
              (45 : F) * a1 * a22 * lambda * t2 ^ 4 +
              (105 : F) * a1 * a22 * t2 ^ 5 +
              (16 : F) * a1 * s22 * t2 ^ 5 +
              (9 : F) * a1 * lambda * t2 ^ 6 -
              (25 : F) * a1 * t2 ^ 7 +
              (14 : F) * a22 ^ 3 * vis * t2 -
              (4 : F) * a22 ^ 3 * w73 -
              (28 : F) * a22 ^ 2 * vis * t2 ^ 3 +
              (18 : F) * a22 ^ 2 * w73 * t2 ^ 2 -
              (10 : F) * a22 ^ 2 * q54 * t2 +
              (14 : F) * a22 * vis * t2 ^ 5 -
              (12 : F) * a22 * w73 * t2 ^ 4 +
              (10 : F) * a22 * q54 * t2 ^ 3 -
              (2 : F) * vis * t2 ^ 7 +
              (2 : F) * w73 * t2 ^ 6 -
              (2 : F) * q54 * t2 ^ 5 -
              (2 : F) * b1 * t2) +
            h * (-(20 : F) * a0 ^ 2 * a22 +
              (8 : F) * a0 ^ 2 * s22 +
              (9 : F) * a0 ^ 2 * lambda * t2 -
              (15 : F) * a0 ^ 2 * t2 ^ 2 +
              (20 : F) * a0 * a22 ^ 3 -
              (16 : F) * a0 * a22 ^ 2 * s22 -
              (27 : F) * a0 * a22 ^ 2 * lambda * t2 +
              (15 : F) * a0 * a22 ^ 2 * t2 ^ 2 +
              (48 : F) * a0 * a22 * s22 * t2 ^ 2 +
              (36 : F) * a0 * a22 * lambda * t2 ^ 3 -
              (80 : F) * a0 * a22 * t2 ^ 4 -
              (16 : F) * a0 * s22 * t2 ^ 4 -
              (9 : F) * a0 * lambda * t2 ^ 5 +
              (25 : F) * a0 * t2 ^ 6 -
              (4 : F) * a22 ^ 5 +
              (4 : F) * a22 ^ 4 * s22 +
              (9 : F) * a22 ^ 4 * lambda * t2 +
              (5 : F) * a22 ^ 4 * t2 ^ 2 -
              (32 : F) * a22 ^ 3 * s22 * t2 ^ 2 -
              (30 : F) * a22 ^ 3 * lambda * t2 ^ 3 +
              (50 : F) * a22 ^ 3 * t2 ^ 4 +
              (40 : F) * a22 ^ 2 * s22 * t2 ^ 4 +
              (27 : F) * a22 ^ 2 * lambda * t2 ^ 5 -
              (65 : F) * a22 ^ 2 * t2 ^ 6 -
              (16 : F) * a22 * s22 * t2 ^ 6 -
              (9 : F) * a22 * lambda * t2 ^ 7 +
              (25 : F) * a22 * t2 ^ 8 +
              (2 : F) * s22 * t2 ^ 8 +
              (8 : F) * b0 +
              lambda * t2 ^ 9 -
              (3 : F) * t2 ^ 10))) := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h128 : (128 : F) ≠ 0 := by norm_num
  have h256 : (256 : F) ≠ 0 := by norm_num
  have h2048 : (2048 : F) ≠ 0 := by norm_num
  have h65536 : (65536 : F) ≠ 0 := by norm_num
  have h1048576 : (1048576 : F) ≠ 0 := by norm_num
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
  have hV :
      depressedV410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
          (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
          (h ^ 2 * b42) (h * b31) b2 =
        (65536 * b2 - 49152 * b31 * t2 + 24576 * b42 * t2 ^ 2 +
            72 * h ^ 2 * lambda * t2 ^ 7 + 448 * h ^ 2 * s22 * t2 ^ 6 -
            315 * h ^ 2 * t2 ^ 8 - 10240 * h * q54 * t2 ^ 3 -
            1344 * h * t2 ^ 5 * vis + 3840 * h * t2 ^ 4 * w73) /
          (65536 * h ^ 2) := by
    rw [depressedV410_eq_cleared h (h ^ 3 * t2) b9 (h ^ 8 * s22)
      (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54) (h ^ 2 * b42)
      (h * b31) b2 lambda hh hN]
    field_simp [hh]
    ring
  have hZ :
      depressedZ410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
          (h ^ 8 * s22) (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54)
          (h ^ 2 * b42) (h * b31) b2 b1 b0 =
        (1048576 * b0 * h ^ 2 - 262144 * b1 * h * t2 +
            65536 * b2 * t2 ^ 2 - 16384 * b31 * t2 ^ 3 +
            4096 * b42 * t2 ^ 4 + 2 * h ^ 2 * lambda * t2 ^ 9 +
            16 * h ^ 2 * s22 * t2 ^ 8 - 9 * h ^ 2 * t2 ^ 10 -
            1024 * h * q54 * t2 ^ 5 - 64 * h * t2 ^ 7 * vis +
            256 * h * t2 ^ 6 * w73) / (1048576 * h ^ 2) := by
    rw [depressedZ410_eq_cleared h (h ^ 3 * t2) b9 (h ^ 8 * s22)
      (h ^ 6 * vis) (h ^ 5 * w73) (h ^ 4 * q54) (h ^ 2 * b42)
      (h * b31) b2 b1 b0 lambda hh hN]
    field_simp [hh]
    ring
  simp only [iotaResidual410, alphaResidual410, betaResidual410,
    gammaResidual410, deltaResidual410, epsilonResidual410,
    zetaResidual410, etaResidual410, hL, hA, hB, hC, hP, hQ, hR, hS,
    hT, hU, hV, hZ]
  field_simp [hh]
  ring

end IotaClearing410

/-! ## Source-facing power relation -/

section NonzeroIotaBridge410

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

set_option maxHeartbeats 80000000 in
/-- The tenth-face residual `ι` on a square-core ninth-power source is a
differential constant, and on the thirteenth-face jet its cleared
defect is a scalar times `h³`. -/
theorem nonzeroFace410_iotaResidualPowerRelation
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
      localClearedIotaResidual410 h0 t2 a22 s22 vis w73 q54 (p.coeff 1)
          (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1) (q.coeff 0)
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
  let b0 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 0)
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
    rw [affineDepress_degreeTen_coeff0_410 (sourceToRatFunc68 q) hRF
      (quarticDepressionR410 hRF a3) hh hgTop hg_high_src]
    simp [depressedZ410, quarticDepressionR410, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0]
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
  have hrow5 :
      (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 0) +
          (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 1) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 2) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 5) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 4) -
          (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 2) = 0 := by
    have hrow :=
      differentialJacobian_coeff_5_monicQuarticDecic
        ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 5) hbracket
    simpa [f, g, Polynomial.coeff_C, show (5 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow3 :
      (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 0) +
          (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 1) +
        (2 : RatFunc k) * g.coeff 2 * ratFuncDerivation68 (f.coeff 2) -
          f.coeff 1 * ratFuncDerivation68 (g.coeff 3) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 2) -
          (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 0) = 0 := by
    have hrow :=
      differentialJacobian_coeff_3_monicQuarticDecic
        ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 3) hbracket
    simpa [f, g, Polynomial.coeff_C, show (3 : ℕ) ≠ 0 by norm_num] using
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
  have heta0deriv :
      ratFuncDerivation68
        (etaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
          (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
          (g.coeff 5) (g.coeff 4) (g.coeff 2)) = 0 :=
    etaResidual410_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
      (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 2) hLconst halpha0
      hbeta0 hgamma0 hdelta0 hepsilon0 (by simpa using hrow5)
  have hiota0deriv :
      ratFuncDerivation68
        (iotaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
          (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
          (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 0)) = 0 :=
    iotaResidual410_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
      (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
      (g.coeff 0) hLconst halpha0 hbeta0 hgamma0 hdelta0 hepsilon0
      hzeta0 heta0deriv (by simpa using hrow3)
  obtain ⟨c0, hc0⟩ :
      ∃ c0 : k,
        iotaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
            (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
            (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
            (g.coeff 0) =
          algebraMap k (RatFunc k) c0 := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      hiota0deriv
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
  have hF := iotaDefect_eq_cleared410 hRF t2R a22R s22R visR w73R q54R
    a1 a0 b42R b31R b2 b1 b0 b9 (RatFunc.C lambda) hh hNratSub
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
  have hg2' : g.coeff 2 =
      depressedV410 hRF (quarticDepressionR410 hRF (hRF ^ 3 * t2R)) b9
        (hRF ^ 8 * s22R) (hRF ^ 6 * visR) (hRF ^ 5 * w73R)
        (hRF ^ 4 * q54R) (hRF ^ 2 * b42R) (hRF * b31R) b2 := by
    rw [← hp3R, ← hq8R, ← hq7R, ← hq6R, ← hq5R, ← hq4R, ← hq3R]
    exact hg2
  have hg0' : g.coeff 0 =
      depressedZ410 hRF (quarticDepressionR410 hRF (hRF ^ 3 * t2R)) b9
        (hRF ^ 8 * s22R) (hRF ^ 6 * visR) (hRF ^ 5 * w73R)
        (hRF ^ 4 * q54R) (hRF ^ 2 * b42R) (hRF * b31R) b2 b1 b0 := by
    rw [← hp3R, ← hq8R, ← hq7R, ← hq6R, ← hq5R, ← hq4R, ← hq3R]
    exact hg0
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedIotaResidual410 h0 t2 a22 s22 vis w73 q54
            (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1)
            (q.coeff 0) lambda) =
        (8 : RatFunc k) * hRF ^ 3 *
          iotaResidual410 (g.coeff 9) (f.coeff 2) (f.coeff 1)
            (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
            (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
            (g.coeff 0) := by
    rw [hg9L', hf2', hf1', hf0', hg8'', hg7', hg6', hg5', hg4', hg3',
      hg2', hg0', hF]
    simp only [localClearedIotaResidual410, iotaPolarThreeNumerator410,
      iotaPolarTwoNumerator410, iotaPolarOneNumerator410,
      iotaRegularNumerator410, map_add, map_sub, map_mul, map_pow,
      map_neg, map_ofNat, RatFunc.algebraMap_C, hRF, t2R, a22R, s22R,
      visR, w73R, q54R, b42R, b31R, a1, a0, b2, b1, b0]
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedIotaResidual410 h0 t2 a22 s22 vis w73 q54
            (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1)
            (q.coeff 0) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (8 * c0) * h0 ^ 3) := by
    rw [hclear, hc0]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat]
    ring
  refine ⟨8 * c0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

/-- The cleared `ι` defect is `h`-adically divisible by `h³`. -/
theorem iotaBridge_hCubeDvd410 (h t2 a22 s22 vis w73 q54 a1 a0 b42 b31
    b2 b1 b0 : k[X]) (lambda c : k)
    (hpow : localClearedIotaResidual410 h t2 a22 s22 vis w73 q54 a1 a0
        b42 b31 b2 b1 b0 lambda =
      Polynomial.C c * h ^ 3) :
    h ^ 3 ∣
      localClearedIotaResidual410 h t2 a22 s22 vis w73 q54 a1 a0 b42
        b31 b2 b1 b0 lambda :=
  ⟨Polynomial.C c, by rw [hpow]; ring⟩

/-- At a root of the degree-one scale the order-`-3` numerator block of
the cleared `ι` vanishes. -/
theorem iotaBridge_orderThreeVanishes410 (h t2 a22 s22 vis w73 q54 a1
    a0 b42 b31 b2 b1 b0 : k[X]) (lambda a c : k)
    (hroot : h.eval a = 0)
    (hpow : localClearedIotaResidual410 h t2 a22 s22 vis w73 q54 a1 a0
        b42 b31 b2 b1 b0 lambda =
      Polynomial.C c * h ^ 3) :
    (iotaPolarThreeNumerator410 t2 vis w73 a1 b42 b31 lambda).eval a =
      0 := by
  have heval := congrArg (fun r : k[X] => r.eval a) hpow
  simpa [localClearedIotaResidual410, hroot, eval_add, eval_mul,
    eval_pow] using heval

/-- On the thirteenth-face jet the vanishing of the order-`-3` block
forces the polar coefficient `15 p₁³ (λ + 4 t₂) / 256` to vanish at the
root: the nonzero face splits into `p₁(a) = 0` or `λ + 4 t₂(a) = 0`.
Neither branch is eliminated. -/
theorem iotaBridge_polarSplit410 (h t2 a22 s22 vis w73 q54 a1 a0 b42
    b31 b2 b1 b0 : k[X]) (lambda a c : k)
    (hroot : h.eval a = 0)
    (hpow : localClearedIotaResidual410 h t2 a22 s22 vis w73 q54 a1 a0
        b42 b31 b2 b1 b0 lambda =
      Polynomial.C c * h ^ 3)
    (hT : (64 : k) * vis.eval a - (160 : k) * a1.eval a = 0)
    (hU : (8 : k) * w73.eval a =
      a1.eval a * ((30 : k) * t2.eval a - (9 : k) * lambda))
    (hW : (8 : k) * b42.eval a = (15 : k) * (a1.eval a) ^ 2)
    (hX : (64 : k) * b31.eval a =
      (15 : k) * (a1.eval a) ^ 2 *
        ((4 : k) * t2.eval a - (3 : k) * lambda)) :
    a1.eval a = 0 ∨ lambda + (4 : k) * t2.eval a = 0 := by
  have hzero := iotaBridge_orderThreeVanishes410 h t2 a22 s22 vis w73
    q54 a1 a0 b42 b31 b2 b1 b0 lambda a c hroot hpow
  have hlink :
      (iotaPolarThreeNumerator410 t2 vis w73 a1 b42 b31 lambda).eval a =
        (8 : k) * iotaOrderThree410 (a1.eval a) (t2.eval a)
          (vis.eval a) (w73.eval a) (b31.eval a) (b42.eval a)
          lambda := by
    simp only [iotaPolarThreeNumerator410, iotaOrderThree410, eval_add,
      eval_sub, eval_mul, eval_pow, eval_ofNat, eval_C]
    ring
  have hfact := terminalIota_orderThree_onJet410 (a1.eval a)
    (t2.eval a) (vis.eval a) (w73.eval a) (b31.eval a) (b42.eval a)
    lambda hT hU hW hX
  have hprod :
      (15 / 32 : k) *
          ((a1.eval a) ^ 3 * (lambda + (4 : k) * t2.eval a)) = 0 := by
    linear_combination hzero - hlink - (8 : k) * hfact
  have h1532 : (15 / 32 : k) ≠ 0 := by norm_num
  have hX3 : (a1.eval a) ^ 3 * (lambda + (4 : k) * t2.eval a) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left h1532
  have hX3' :
      a1.eval a *
          (a1.eval a *
            (a1.eval a * (lambda + (4 : k) * t2.eval a))) = 0 := by
    linear_combination hX3
  rcases mul_eq_zero.mp hX3' with h1 | hrest
  · exact Or.inl h1
  rcases mul_eq_zero.mp hrest with h1 | hrest'
  · exact Or.inl h1
  rcases mul_eq_zero.mp hrest' with h1 | hlin
  · exact Or.inl h1
  · exact Or.inr hlin

/-- Exact order-`-2` residual: the power relation peels one `h` off the
order-`-3` block and ties the cofactor to the order-`-2` block at the
root.  The order-`-2` polar coefficient is not claimed to vanish. -/
theorem iotaBridge_orderTwoCofactor410 (h t2 a22 s22 vis w73 q54 a1 a0
    b42 b31 b2 b1 b0 : k[X]) (lambda a c : k)
    (hroot : h.eval a = 0)
    (hpow : localClearedIotaResidual410 h t2 a22 s22 vis w73 q54 a1 a0
        b42 b31 b2 b1 b0 lambda =
      Polynomial.C c * h ^ 3) :
    ∃ w1 : k[X],
      iotaPolarThreeNumerator410 t2 vis w73 a1 b42 b31 lambda =
          h * w1 ∧
        w1.eval a +
            (iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b42
                b31 b2 lambda).eval a =
          0 := by
  refine ⟨Polynomial.C c * h ^ 2 -
      (iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b42 b31
          b2 lambda +
        h * (iotaPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b1
            lambda +
          h * iotaRegularNumerator410 t2 a22 s22 a0 b0 lambda)),
    ?_, ?_⟩
  · have hpow' := hpow
    simp only [localClearedIotaResidual410] at hpow'
    linear_combination hpow'
  · have hw :
        (Polynomial.C c * h ^ 2 -
            (iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b42
                b31 b2 lambda +
              h * (iotaPolarOneNumerator410 t2 a22 s22 vis w73 q54 a1
                  a0 b1 lambda +
                h * iotaRegularNumerator410 t2 a22 s22 a0 b0
                  lambda))).eval a =
          -(iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b42
              b31 b2 lambda).eval a := by
      simp [hroot, eval_add, eval_mul, eval_sub, eval_pow]
    rw [hw]
    ring

/-- Jet form of the order-`-2` residual: the `h`-cofactor `w₁` of the
order-`-3` block satisfies `128 w₁(a) + 3 p₁(a)² (-160 a₂₂² +
18 λ a₂₂ t₂ + 440 a₂₂ t₂² - 27 λ t₂³ + 256 s₂₂ t₂² - 180 t₂⁴)(a) = 0`.
This retains the exact residual; `ι₋₂(a)` itself is not forced to
vanish. -/
theorem iotaBridge_orderTwoResidual410 (h t2 a22 s22 vis w73 q54 a1 a0
    b42 b31 b2 b1 b0 : k[X]) (lambda a c : k)
    (hroot : h.eval a = 0)
    (hpow : localClearedIotaResidual410 h t2 a22 s22 vis w73 q54 a1 a0
        b42 b31 b2 b1 b0 lambda =
      Polynomial.C c * h ^ 3)
    (hT : (64 : k) * vis.eval a - (160 : k) * a1.eval a = 0)
    (hU : (8 : k) * w73.eval a =
      a1.eval a * ((30 : k) * t2.eval a - (9 : k) * lambda))
    (hW : (8 : k) * b42.eval a = (15 : k) * (a1.eval a) ^ 2)
    (hV : (32 : k) * q54.eval a + (40 : k) * a1.eval a * a22.eval a -
        (64 : k) * a1.eval a * s22.eval a -
        (27 : k) * a1.eval a * lambda * t2.eval a +
        (90 : k) * a1.eval a * (t2.eval a) ^ 2 =
      0)
    (hX : (64 : k) * b31.eval a =
      (15 : k) * (a1.eval a) ^ 2 *
        ((4 : k) * t2.eval a - (3 : k) * lambda))
    (hY : (256 : k) * b2.eval a =
      (a1.eval a) ^ 2 *
        ((256 : k) * s22.eval a - (400 : k) * a22.eval a +
          (243 : k) * lambda * t2.eval a -
          (540 : k) * (t2.eval a) ^ 2)) :
    ∃ w1 : k[X],
      iotaPolarThreeNumerator410 t2 vis w73 a1 b42 b31 lambda =
          h * w1 ∧
        (128 : k) * w1.eval a +
            (3 : k) * (a1.eval a) ^ 2 *
              (-(160 : k) * (a22.eval a) ^ 2 +
                (18 : k) * a22.eval a * lambda * t2.eval a +
                (440 : k) * a22.eval a * (t2.eval a) ^ 2 -
                (27 : k) * lambda * (t2.eval a) ^ 3 +
                (256 : k) * s22.eval a * (t2.eval a) ^ 2 -
                (180 : k) * (t2.eval a) ^ 4) =
          0 := by
  obtain ⟨w1, hw1, hsum⟩ := iotaBridge_orderTwoCofactor410 h t2 a22 s22
    vis w73 q54 a1 a0 b42 b31 b2 b1 b0 lambda a c hroot hpow
  have hlink2 :
      (iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 a1 a0 b42 b31
          b2 lambda).eval a =
        (8 : k) * iotaOrderTwo410 (a0.eval a) (a1.eval a) (t2.eval a)
          (a22.eval a) (s22.eval a) (vis.eval a) (w73.eval a)
          (q54.eval a) (b42.eval a) (b31.eval a) (b2.eval a)
          lambda := by
    simp only [iotaPolarTwoNumerator410, iotaOrderTwo410, eval_add,
      eval_sub, eval_mul, eval_pow, eval_ofNat, eval_C, eval_neg]
    ring
  have hfact2 := terminalIota_orderTwo_onJet410 (a0.eval a)
    (a1.eval a) (t2.eval a) (a22.eval a) (s22.eval a) (vis.eval a)
    (w73.eval a) (q54.eval a) (b42.eval a) (b31.eval a) (b2.eval a)
    lambda hT hU hW hV hX hY
  refine ⟨w1, hw1, ?_⟩
  linear_combination (128 : k) * hsum - (128 : k) * hlink2 -
    (1024 : k) * hfact2

end NonzeroIotaBridge410

#print axioms iotaResidual410_deriv_zero
#print axioms affineDepress_degreeTen_coeff0_410
#print axioms depressedZ410_eq_cleared
#print axioms iotaDefect_eq_cleared410
#print axioms nonzeroFace410_iotaResidualPowerRelation
#print axioms iotaBridge_hCubeDvd410
#print axioms iotaBridge_orderThreeVanishes410
#print axioms iotaBridge_polarSplit410
#print axioms iotaBridge_orderTwoCofactor410
#print axioms iotaBridge_orderTwoResidual410

end Max11DegreeRoutes
