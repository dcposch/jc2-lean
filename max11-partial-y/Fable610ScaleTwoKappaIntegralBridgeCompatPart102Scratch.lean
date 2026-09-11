import Fable610ScaleTwoKappaIntegralBridgeCompatPart101Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatPart05Scratch
import Fable610ScaleTwoKappaIntegralBridgeCompatKappaSpeedPart03Scratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaDepressedRows610

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

set_option maxHeartbeats 16000000 in
theorem bridgeThetaResidual610_deriv_zero
    (d : Derivation k F F) (L A B C0 D0 E0 P Q R S0 T0 U0 W0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual610 A P) = 0)
    (hbeta : d (betaResidual610 L A B Q) = 0)
    (hgamma : d (gammaResidual610 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual610 L A B C0 D0 P Q S0) = 0)
    (hepsilon : d (epsilonResidual610 L A B C0 D0 E0 P Q R T0) = 0)
    (hzeta : d (zetaResidual610 L A B C0 D0 E0 P Q R S0 U0) = 0)
    (hrow : (7 : F) * Q * d E0 + (6 : F) * R * d D0 +
        (5 : F) * S0 * d C0 + (4 : F) * T0 * d B +
        (3 : F) * U0 * d A - (1 : F) * D0 * d R -
        (2 : F) * C0 * d S0 - (3 : F) * B * d T0 -
        (4 : F) * A * d U0 - (6 : F) * d W0 = 0) :
    d (bridgeThetaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 W0) = 0 := by
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h3 : d (3 : F) = 0 := d.map_natCast 3
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h6 : d (6 : F) = 0 := d.map_natCast 6
  have h7 : d (7 : F) = 0 := d.map_natCast 7
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h16 : d (16 : F) = 0 := d.map_natCast 16
  have h27 : d (27 : F) = 0 := d.map_natCast 27
  have h36 : d (36 : F) = 0 := d.map_natCast 36
  have h72 : d (72 : F) = 0 := d.map_natCast 72
  have h81 : d (81 : F) = 0 := d.map_natCast 81
  have h128 : d (128 : F) = 0 := d.map_natCast 128
  have h243 : d (243 : F) = 0 := d.map_natCast 243
  have h1296 : d (1296 : F) = 0 := d.map_natCast 1296
  have h53 : d (5 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, h3, h5]
  have h32 : d (3 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h3]
  have h43 : d (4 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, h3, h4]
  have h76 : d (7 / 6 : F) = 0 := by
    simp [Derivation.leibniz_div, h6, h7]
  have h56c : d (5 / 6 : F) = 0 := by
    simp [Derivation.leibniz_div, h6, h5]
  have h23 : d (2 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, h3, h2]
  have h12 : d (1 / 2 : F) = 0 := by
    simp [Derivation.leibniz_inv, h2]
  have h109 : d (10 / 9 : F) = 0 := by
    have h10 : d (10 : F) = 0 := d.map_natCast 10
    simp [Derivation.leibniz_div, h9, h10]
  have h49 : d (4 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h4]
  have h772 : d (7 / 72 : F) = 0 := by
    simp [Derivation.leibniz_div, h72, h7]
  have h581 : d (5 / 81 : F) = 0 := by
    simp [Derivation.leibniz_div, h81, h5]
  have h736 : d (7 / 36 : F) = 0 := by
    simp [Derivation.leibniz_div, h36, h7]
  have h1027 : d (10 / 27 : F) = 0 := by
    have h10 : d (10 : F) = 0 := d.map_natCast 10
    simp [Derivation.leibniz_div, h27, h10]
  have h572 : d (5 / 72 : F) = 0 := by
    simp [Derivation.leibniz_div, h72, h5]
  have h527 : d (5 / 27 : F) = 0 := by
    simp [Derivation.leibniz_div, h27, h5]
  have h427 : d (4 / 27 : F) = 0 := by
    simp [Derivation.leibniz_div, h27, h4]
  have h351296 : d (35 / 1296 : F) = 0 := by
    have h35 : d (35 : F) = 0 := d.map_natCast 35
    simp [Derivation.leibniz_div, h1296, h35]
  have h20243 : d (20 / 243 : F) = 0 := by
    have h20 : d (20 : F) = 0 := d.map_natCast 20
    simp [Derivation.leibniz_div, h243, h20]
  have h38 : d (3 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h3]
  have h34 : d (3 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h3]
  have h316 : d (3 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h3]
  have h3128 : d (3 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h3]
  have hsq : d (A * A) = (2 : F) * A * d A := by
    simp [Derivation.leibniz]
    ring
  have hsqB : d (B * B) = (2 : F) * B * d B := by
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  have hsqC : d (C0 * C0) = (2 : F) * C0 * d C0 := by
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  have hcub : d (A ^ 3) = (3 : F) * A ^ 2 * d A := by
    have h2A : d (A ^ 2) = (2 : F) * A * d A := by
      simpa [pow_two] using hsq
    simp [pow_three, Derivation.leibniz, h2A]
    ring
  have hcubB : d (B ^ 3) = (3 : F) * B ^ 2 * d B := by
    have h2B : d (B ^ 2) = (2 : F) * B * d B := by
      simpa [pow_two] using hsqB
    simp [pow_three, Derivation.leibniz, h2B]
    ring
  have hquar : d (A ^ 4) = (4 : F) * A ^ 3 * d A := by
    have : A ^ 4 = A ^ 3 * A := by ring
    rw [this]
    simp [Derivation.leibniz, hcub]
    ring
  have hPderiv : d P = (5 / 3 : F) * d A := by
    have halpha' : d P - (5 / 3 : F) * d A = 0 := by
      simpa [alphaResidual610, map_sub, Derivation.leibniz, h53, zero_mul,
        add_zero] using halpha
    linear_combination halpha'
  have hQderiv : d Q = (5 / 3 : F) * d B + (3 / 2 : F) * L * d A := by
    have hbeta' :
        d Q - (5 / 3 : F) * d B - (3 / 2 : F) * L * d A = 0 := by
      simpa [betaResidual610, map_sub, Derivation.leibniz, h53, h32, hL,
        zero_mul, add_zero, mul_zero] using hbeta
    linear_combination hbeta'
  have hRderiv : d R = (5 / 3 : F) * d C0 + (3 / 2 : F) * L * d B +
      (4 / 3 : F) * P * d A - (10 / 9 : F) * A * d A := by
    have hgamma' :
        d R - (5 / 3 : F) * d C0 - (3 / 2 : F) * L * d B -
          ((4 / 3 : F) * P * d A + A * ((4 / 3 : F) * d P)) +
          (5 / 3 : F) * (A * d A + A * d A) = 0 := by
      simpa [gammaResidual610, map_sub, map_add, Derivation.leibniz, h53,
        h32, h43, hL, zero_mul, add_zero, mul_zero, pow_two] using hgamma
    linear_combination hgamma' + (-(4 / 3 : F) * A) * hPderiv.symm
  have hSderiv : d S0 = (5 / 3 : F) * d D0 + (3 / 2 : F) * L * d C0 +
      (4 / 3 : F) * P * d B - (10 / 9 : F) * A * d B +
      (7 / 6 : F) * Q * d A - (A * L + (5 / 6 : F) * B) * d A := by
    have hexp :
        deltaResidual610 L A B C0 D0 P Q S0 =
          S0 - (5 / 3 : F) * D0 - (3 / 2 : F) * L * C0 -
            (4 / 3 : F) * P * B - (7 / 6 : F) * Q * A +
            (55 / 18 : F) * A * B + (11 / 8 : F) * L * (A * A) := by
      simp only [deltaResidual610, alphaResidual610, betaResidual610,
        pow_two]
      ring
    have hdlt := hdelta
    rw [hexp] at hdlt
    have h18 : d (18 : F) = 0 := d.map_natCast 18
    have h55 : d (55 : F) = 0 := d.map_natCast 55
    have h11 : d (11 : F) = 0 := d.map_natCast 11
    have h5518 : d (55 / 18 : F) = 0 := by
      simp [Derivation.leibniz_div, h18, h55]
    have h118 : d (11 / 8 : F) = 0 := by
      simp [Derivation.leibniz_div, h8, h11]
    simp [map_sub, map_add, Derivation.leibniz, h53, h32, h43, h76, hL,
      h5518, h118, zero_mul, add_zero, mul_zero, hsq] at hdlt
    rw [hPderiv, hQderiv] at hdlt
    linear_combination hdlt
  have hTderiv : d T0 = (5 / 3 : F) * d E0 + (3 / 2 : F) * L * d D0 +
      (4 / 3 : F) * P * d C0 - (10 / 9 : F) * A * d C0 +
      (7 / 6 : F) * Q * d B - (A * L + (5 / 6 : F) * B) * d B +
      R * d A +
      ((20 / 27 : F) * A ^ 2 - (8 / 9 : F) * A * P - (3 / 4 : F) * L * B -
        (5 / 9 : F) * C0) * d A := by
    have hexp :
        epsilonResidual610 L A B C0 D0 E0 P Q R T0 =
          T0 - (5 / 3 : F) * E0 - (3 / 2 : F) * L * D0 -
            (4 / 3 : F) * P * C0 - (7 / 6 : F) * Q * B - R * A +
            (25 / 9 : F) * A * C0 + (25 / 18 : F) * (B * B) +
            (5 / 2 : F) * L * A * B + (10 / 9 : F) * P * (A * A) -
            (100 / 81 : F) * (A * A * A) := by
      simp only [epsilonResidual610, alphaResidual610, betaResidual610,
        gammaResidual610, pow_two, pow_three]
      ring
    have heps := hepsilon
    rw [hexp] at heps
    have h18 : d (18 : F) = 0 := d.map_natCast 18
    have h25 : d (25 : F) = 0 := d.map_natCast 25
    have h10 : d (10 : F) = 0 := d.map_natCast 10
    have h100 : d (100 : F) = 0 := d.map_natCast 100
    have h259 : d (25 / 9 : F) = 0 := by
      simp [Derivation.leibniz_div, h9, h25]
    have h2518 : d (25 / 18 : F) = 0 := by
      simp [Derivation.leibniz_div, h18, h25]
    have h52 : d (5 / 2 : F) = 0 := by
      simp [Derivation.leibniz_div, h2, h5]
    have h10081 : d (100 / 81 : F) = 0 := by
      simp [Derivation.leibniz_div, h81, h100]
    have hcub' : d (A * A * A) = (3 : F) * (A * A) * d A := by
      simp [Derivation.leibniz]
      ring
    simp [map_sub, map_add, Derivation.leibniz, h53, h32, h43, h76, hL,
      h259, h2518, h52, h109, h10081, zero_mul, add_zero, mul_zero, hsq,
      hcub', hsqB] at heps
    rw [hPderiv, hQderiv, hRderiv] at heps
    linear_combination heps
  have hUderiv : d U0 =
      (3 / 2 : F) * L * d E0 +
        (4 / 3 : F) * P * d D0 + (4 / 3 : F) * D0 * d P +
        (7 / 6 : F) * Q * d C0 + (7 / 6 : F) * C0 * d Q +
        R * d B + B * d R +
        (5 / 6 : F) * S0 * d A + (5 / 6 : F) * A * d S0 -
        (5 / 2 : F) * A * d D0 - (5 / 2 : F) * D0 * d A -
        (5 / 2 : F) * B * d C0 - (5 / 2 : F) * C0 * d B -
        (2 : F) * A * B * d P - (2 : F) * A * P * d B -
        (2 : F) * B * P * d A -
        (7 / 8 : F) * (A * A) * d Q - (7 / 4 : F) * Q * A * d A -
        (9 / 4 : F) * L * A * d C0 - (9 / 4 : F) * L * C0 * d A -
        (9 / 4 : F) * L * B * d B +
        (25 / 8 : F) * (A * A) * d B + (25 / 4 : F) * A * B * d A +
        (45 / 16 : F) * L * (A * A) * d A := by
    have hexp :
        zetaResidual610 L A B C0 D0 E0 P Q R S0 U0 =
          U0 - (3 / 2 : F) * L * E0 - (4 / 3 : F) * P * D0 -
            (7 / 6 : F) * Q * C0 - R * B - (5 / 6 : F) * S0 * A +
            (5 / 2 : F) * A * D0 + (5 / 2 : F) * B * C0 +
            (2 : F) * A * B * P + (7 / 8 : F) * Q * (A * A) +
            (9 / 4 : F) * L * A * C0 + (9 / 8 : F) * L * (B * B) -
            (25 / 8 : F) * (A * A) * B -
            (15 / 16 : F) * L * (A * A * A) := by
      simp only [zetaResidual610, alphaResidual610, betaResidual610,
        gammaResidual610, deltaResidual610, pow_two, pow_three]
      ring
    have hz := hzeta
    rw [hexp] at hz
    have h25 : d (25 : F) = 0 := d.map_natCast 25
    have h15 : d (15 : F) = 0 := d.map_natCast 15
    have h52 : d (5 / 2 : F) = 0 := by
      simp [Derivation.leibniz_div, h2, h5]
    have h78 : d (7 / 8 : F) = 0 := by
      simp [Derivation.leibniz_div, h8, h7]
    have h94 : d (9 / 4 : F) = 0 := by
      simp [Derivation.leibniz_div, h4, h9]
    have h98 : d (9 / 8 : F) = 0 := by
      simp [Derivation.leibniz_div, h8, h9]
    have h258 : d (25 / 8 : F) = 0 := by
      simp [Derivation.leibniz_div, h8, h25]
    have h16ne : (16 : F) ≠ 0 := by norm_num
    have h16inv : d (16 : F)⁻¹ = 0 := by
      have hone : (16 : F) * (16 : F)⁻¹ = 1 := mul_inv_cancel₀ h16ne
      have hd1 : d ((16 : F) * (16 : F)⁻¹) = 0 := by
        rw [hone]
        exact d.map_one_eq_zero
      have hleib :
          d ((16 : F) * (16 : F)⁻¹) =
            (16 : F) • d (16 : F)⁻¹ + (16 : F)⁻¹ • d (16 : F) :=
        Derivation.leibniz d (16 : F) (16 : F)⁻¹
      have hsum : (16 : F) * d (16 : F)⁻¹ + (16 : F)⁻¹ * d (16 : F) = 0 := by
        simpa [smul_eq_mul, hd1] using hleib.symm
      have honly : (16 : F) * d (16 : F)⁻¹ = 0 := by
        simpa [h16, mul_zero, add_zero] using hsum
      exact (mul_eq_zero.mp honly).resolve_left h16ne
    have h1516 : d (15 / 16 : F) = 0 := by
      simp [div_eq_mul_inv, Derivation.leibniz, h15, h16inv, zero_mul,
        add_zero, mul_zero]
    have hcub' : d (A * A * A) = (3 : F) * (A * A) * d A := by
      simp [Derivation.leibniz]
      ring
    simp [map_sub, map_add, Derivation.leibniz, h32, h43, h76, h56c, hL,
      h52, h78, h94, h98, h258, h1516, zero_mul, add_zero, mul_zero, hsq,
      hsqB, hcub', h2] at hz
    linear_combination hz
  have hWderiv : d W0 = (7 / 6 : F) * Q * d E0 + R * d D0 +
      (5 / 6 : F) * S0 * d C0 + (2 / 3 : F) * T0 * d B +
      (1 / 2 : F) * U0 * d A - (1 / 6 : F) * D0 * d R -
      (1 / 3 : F) * C0 * d S0 - (1 / 2 : F) * B * d T0 -
      (2 / 3 : F) * A * d U0 := by
    linear_combination (-1 / 6 : F) * hrow
  have h116 : d (1 / 16 : F) = 0 := by
    simp [Derivation.leibniz_inv, h16]
  have h29 : d (2 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h2]
  have h59 : d (5 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h5]
  have h89 : d (8 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h8]
  have h2027 : d (20 / 27 : F) = 0 := by
    have h20 : d (20 : F) = 0 := d.map_natCast 20
    simp [Derivation.leibniz_div, h27, h20]
  simp [bridgeThetaResidual610, alphaResidual610, betaResidual610,
    gammaResidual610, deltaResidual610, epsilonResidual610,
    zetaResidual610, map_sub, map_add, Derivation.leibniz, smul_eq_mul,
    h2, h3, h4, h5, h6, h7, h8, h9, h12, h23, h53, h32, h43, h76, h56c,
    h109, h49, h772, h581, h736, h1027, h572, h527, h427, h351296,
    h20243, h38, h34, h316, h3128, h116, h29, h59, h89, h2027, hL, hsq,
    hsqB, hsqC, hcub, hcubB, hquar, pow_two, pow_three]
  simp [hWderiv, hPderiv, hQderiv, hRderiv, hSderiv, hTderiv, hUderiv]
  simp [Derivation.leibniz_inv, Derivation.leibniz_div, h2, h16, h12,
    h116]
  ring

end BridgeKappaDepressedRows610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaJet610

variable {R : Type*} [CommRing R]

/-- Order-`48` head of the jet-substituted cleared `κ` defect: the
coefficient of `h⁴⁸` after the fifteenth-face jet `p₅ = h⁵ w₁`,
`p₄ = h³ a₄₁`, `p₃ = h p₃₁`, `q₈ = h⁷ s₁`, `q₇ = h⁵ u₁`, `q₆ = h⁴ b₆₂`,
`q₅ = h² q₅₂` is substituted into `bridgeClearedKappaDefect610`,
kept in its fully factored form. -/
def bridgeKappaJetHead610 (a41 p31 s1 u1 q52 q4 : R) : R :=
  (4837294080 : R) * p31 *
    ((264 : R) * p31 ^ 2 * s1 + (693 : R) * a41 * p31 * u1 -
      (935 : R) * a41 * p31 ^ 2 - (432 : R) * a41 * q4 -
      (270 : R) * p31 * q52)

end BridgeKappaJet610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaDepressedRows610

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

set_option maxHeartbeats 80000000 in
theorem bridgeKappaResidual610_deriv_zero
    (d : Derivation k F F) (L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual610 A P) = 0)
    (hbeta : d (betaResidual610 L A B Q) = 0)
    (hgamma : d (gammaResidual610 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual610 L A B C0 D0 P Q S0) = 0)
    (hepsilon : d (epsilonResidual610 L A B C0 D0 E0 P Q R T0) = 0)
    (hzeta : d (zetaResidual610 L A B C0 D0 E0 P Q R S0 U0) = 0)
    (heta : d (etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0) = 0)
    (htheta : d (bridgeThetaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 W0) = 0)
    (hrow6 : (7 : F) * Q * d E0 + (6 : F) * R * d D0 +
        (5 : F) * S0 * d C0 + (4 : F) * T0 * d B +
        (3 : F) * U0 * d A - (1 : F) * D0 * d R -
        (2 : F) * C0 * d S0 - (3 : F) * B * d T0 -
        (4 : F) * A * d U0 - (6 : F) * d W0 = 0)
    (hrow : (5 : F) * S0 * d E0 + (4 : F) * T0 * d D0 +
        (3 : F) * U0 * d C0 + (2 : F) * V0 * d B +
        (1 : F) * W0 * d A - (1 : F) * D0 * d T0 -
        (2 : F) * C0 * d U0 - (3 : F) * B * d V0 -
        (4 : F) * A * d W0 = 0) :
    d (bridgeKappaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0) = 0 := by
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h3 : d (3 : F) = 0 := d.map_natCast 3
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h6 : d (6 : F) = 0 := d.map_natCast 6
  have h7 : d (7 : F) = 0 := d.map_natCast 7
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h16 : d (16 : F) = 0 := d.map_natCast 16
  have h27 : d (27 : F) = 0 := d.map_natCast 27
  have h36 : d (36 : F) = 0 := d.map_natCast 36
  have h72 : d (72 : F) = 0 := d.map_natCast 72
  have h81 : d (81 : F) = 0 := d.map_natCast 81
  have h128 : d (128 : F) = 0 := d.map_natCast 128
  have h243 : d (243 : F) = 0 := d.map_natCast 243
  have h1296 : d (1296 : F) = 0 := d.map_natCast 1296
  have h53 : d (5 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, h3, h5]
  have h32 : d (3 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h3]
  have h43 : d (4 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, h3, h4]
  have h76 : d (7 / 6 : F) = 0 := by
    simp [Derivation.leibniz_div, h6, h7]
  have h56c : d (5 / 6 : F) = 0 := by
    simp [Derivation.leibniz_div, h6, h5]
  have h23 : d (2 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, h3, h2]
  have h12 : d (1 / 2 : F) = 0 := by
    simp [Derivation.leibniz_inv, h2]
  have h109 : d (10 / 9 : F) = 0 := by
    have h10 : d (10 : F) = 0 := d.map_natCast 10
    simp [Derivation.leibniz_div, h9, h10]
  have h49 : d (4 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h4]
  have h772 : d (7 / 72 : F) = 0 := by
    simp [Derivation.leibniz_div, h72, h7]
  have h581 : d (5 / 81 : F) = 0 := by
    simp [Derivation.leibniz_div, h81, h5]
  have h736 : d (7 / 36 : F) = 0 := by
    simp [Derivation.leibniz_div, h36, h7]
  have h1027 : d (10 / 27 : F) = 0 := by
    have h10 : d (10 : F) = 0 := d.map_natCast 10
    simp [Derivation.leibniz_div, h27, h10]
  have h572 : d (5 / 72 : F) = 0 := by
    simp [Derivation.leibniz_div, h72, h5]
  have h527 : d (5 / 27 : F) = 0 := by
    simp [Derivation.leibniz_div, h27, h5]
  have h427 : d (4 / 27 : F) = 0 := by
    simp [Derivation.leibniz_div, h27, h4]
  have h351296 : d (35 / 1296 : F) = 0 := by
    have h35 : d (35 : F) = 0 := d.map_natCast 35
    simp [Derivation.leibniz_div, h1296, h35]
  have h20243 : d (20 / 243 : F) = 0 := by
    have h20 : d (20 : F) = 0 := d.map_natCast 20
    simp [Derivation.leibniz_div, h243, h20]
  have h38 : d (3 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h3]
  have h34 : d (3 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h3]
  have h316 : d (3 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h3]
  have h3128 : d (3 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h3]
  have hsq : d (A * A) = (2 : F) * A * d A := by
    simp [Derivation.leibniz]
    ring
  have hsqB : d (B * B) = (2 : F) * B * d B := by
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  have hsqC : d (C0 * C0) = (2 : F) * C0 * d C0 := by
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  have hcub : d (A ^ 3) = (3 : F) * A ^ 2 * d A := by
    have h2A : d (A ^ 2) = (2 : F) * A * d A := by
      simpa [pow_two] using hsq
    simp [pow_three, Derivation.leibniz, h2A]
    ring
  have hcubB : d (B ^ 3) = (3 : F) * B ^ 2 * d B := by
    have h2B : d (B ^ 2) = (2 : F) * B * d B := by
      simpa [pow_two] using hsqB
    simp [pow_three, Derivation.leibniz, h2B]
    ring
  have hquar : d (A ^ 4) = (4 : F) * A ^ 3 * d A := by
    have : A ^ 4 = A ^ 3 * A := by ring
    rw [this]
    simp [Derivation.leibniz, hcub]
    ring
  have h10n : d (10 : F) = 0 := d.map_natCast 10
  have h20n : d (20 : F) = 0 := d.map_natCast 20
  have h32n : d (32 : F) = 0 := d.map_natCast 32
  have h35n : d (35 : F) = 0 := d.map_natCast 35
  have h64n : d (64 : F) = 0 := d.map_natCast 64
  have h256n : d (256 : F) = 0 := d.map_natCast 256
  have h385n : d (385 : F) = 0 := d.map_natCast 385
  have h432n : d (432 : F) = 0 := d.map_natCast 432
  have h729n : d (729 : F) = 0 := d.map_natCast 729
  have h31104n : d (31104 : F) = 0 := d.map_natCast 31104
  have h16f : d (1 / 6 : F) = 0 := by
    simp [Derivation.leibniz_inv, h6]
  have h13 : d (1 / 3 : F) = 0 := by
    simp [Derivation.leibniz_inv, h3]
  have h18f : d (1 / 8 : F) = 0 := by
    simp [Derivation.leibniz_inv, h8]
  have h29 : d (2 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h2]
  have h536 : d (5 / 36 : F) = 0 := by
    simp [Derivation.leibniz_div, h36, h5]
  have h827 : d (8 / 27 : F) = 0 := by
    simp [Derivation.leibniz_div, h27, h8]
  have h481 : d (4 / 81 : F) = 0 := by
    simp [Derivation.leibniz_div, h81, h4]
  have h38531104 : d (385 / 31104 : F) = 0 := by
    simp [Derivation.leibniz_div, h31104n, h385n]
  have h35432 : d (35 / 432 : F) = 0 := by
    simp [Derivation.leibniz_div, h432n, h35n]
  have h3256 : d (3 / 256 : F) = 0 := by
    simp [Derivation.leibniz_div, h256n, h3]
  have h332 : d (3 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32n, h3]
  have h964 : d (9 / 64 : F) = 0 := by
    simp [Derivation.leibniz_div, h64n, h9]
  have h35729 : d (35 / 729 : F) = 0 := by
    simp [Derivation.leibniz_div, h729n, h35n]
  have h2081 : d (20 / 81 : F) = 0 := by
    simp [Derivation.leibniz_div, h81, h20n]
  have hsqD : d (D0 * D0) = (2 : F) * D0 * d D0 := by
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  have hquint : d (A ^ 5) = (5 : F) * A ^ 4 * d A := by
    have : A ^ 5 = A ^ 4 * A := by ring
    rw [this]
    simp [Derivation.leibniz, hquar]
    ring
  have hPderiv : d P = (5 / 3 : F) * d A := by
    have halpha' : d P - (5 / 3 : F) * d A = 0 := by
      simpa [alphaResidual610, map_sub, Derivation.leibniz, h53, zero_mul,
        add_zero] using halpha
    linear_combination halpha'
  have hQderiv : d Q = (5 / 3 : F) * d B + (3 / 2 : F) * L * d A := by
    have hbeta' :
        d Q - (5 / 3 : F) * d B - (3 / 2 : F) * L * d A = 0 := by
      simpa [betaResidual610, map_sub, Derivation.leibniz, h53, h32, hL,
        zero_mul, add_zero, mul_zero] using hbeta
    linear_combination hbeta'
  have hRderiv : d R = (5 / 3 : F) * d C0 + (3 / 2 : F) * L * d B +
      (4 / 3 : F) * P * d A - (10 / 9 : F) * A * d A := by
    have hgamma' :
        d R - (5 / 3 : F) * d C0 - (3 / 2 : F) * L * d B -
          ((4 / 3 : F) * P * d A + A * ((4 / 3 : F) * d P)) +
          (5 / 3 : F) * (A * d A + A * d A) = 0 := by
      simpa [gammaResidual610, map_sub, map_add, Derivation.leibniz, h53,
        h32, h43, hL, zero_mul, add_zero, mul_zero, pow_two] using hgamma
    linear_combination hgamma' + (-(4 / 3 : F) * A) * hPderiv.symm
  have hSderiv : d S0 = (5 / 3 : F) * d D0 + (3 / 2 : F) * L * d C0 +
      (4 / 3 : F) * P * d B - (10 / 9 : F) * A * d B +
      (7 / 6 : F) * Q * d A - (A * L + (5 / 6 : F) * B) * d A := by
    have hexp :
        deltaResidual610 L A B C0 D0 P Q S0 =
          S0 - (5 / 3 : F) * D0 - (3 / 2 : F) * L * C0 -
            (4 / 3 : F) * P * B - (7 / 6 : F) * Q * A +
            (55 / 18 : F) * A * B + (11 / 8 : F) * L * (A * A) := by
      simp only [deltaResidual610, alphaResidual610, betaResidual610,
        pow_two]
      ring
    have hdlt := hdelta
    rw [hexp] at hdlt
    have h18 : d (18 : F) = 0 := d.map_natCast 18
    have h55 : d (55 : F) = 0 := d.map_natCast 55
    have h11 : d (11 : F) = 0 := d.map_natCast 11
    have h5518 : d (55 / 18 : F) = 0 := by
      simp [Derivation.leibniz_div, h18, h55]
    have h118 : d (11 / 8 : F) = 0 := by
      simp [Derivation.leibniz_div, h8, h11]
    simp [map_sub, map_add, Derivation.leibniz, h53, h32, h43, h76, hL,
      h5518, h118, zero_mul, add_zero, mul_zero, hsq] at hdlt
    rw [hPderiv, hQderiv] at hdlt
    linear_combination hdlt
  have hTderiv : d T0 = (5 / 3 : F) * d E0 + (3 / 2 : F) * L * d D0 +
      (4 / 3 : F) * P * d C0 - (10 / 9 : F) * A * d C0 +
      (7 / 6 : F) * Q * d B - (A * L + (5 / 6 : F) * B) * d B +
      R * d A +
      ((20 / 27 : F) * A ^ 2 - (8 / 9 : F) * A * P - (3 / 4 : F) * L * B -
        (5 / 9 : F) * C0) * d A := by
    have hexp :
        epsilonResidual610 L A B C0 D0 E0 P Q R T0 =
          T0 - (5 / 3 : F) * E0 - (3 / 2 : F) * L * D0 -
            (4 / 3 : F) * P * C0 - (7 / 6 : F) * Q * B - R * A +
            (25 / 9 : F) * A * C0 + (25 / 18 : F) * (B * B) +
            (5 / 2 : F) * L * A * B + (10 / 9 : F) * P * (A * A) -
            (100 / 81 : F) * (A * A * A) := by
      simp only [epsilonResidual610, alphaResidual610, betaResidual610,
        gammaResidual610, pow_two, pow_three]
      ring
    have heps := hepsilon
    rw [hexp] at heps
    have h18 : d (18 : F) = 0 := d.map_natCast 18
    have h25 : d (25 : F) = 0 := d.map_natCast 25
    have h10 : d (10 : F) = 0 := d.map_natCast 10
    have h100 : d (100 : F) = 0 := d.map_natCast 100
    have h259 : d (25 / 9 : F) = 0 := by
      simp [Derivation.leibniz_div, h9, h25]
    have h2518 : d (25 / 18 : F) = 0 := by
      simp [Derivation.leibniz_div, h18, h25]
    have h52 : d (5 / 2 : F) = 0 := by
      simp [Derivation.leibniz_div, h2, h5]
    have h10081 : d (100 / 81 : F) = 0 := by
      simp [Derivation.leibniz_div, h81, h100]
    have hcub' : d (A * A * A) = (3 : F) * (A * A) * d A := by
      simp [Derivation.leibniz]
      ring
    simp [map_sub, map_add, Derivation.leibniz, h53, h32, h43, h76, hL,
      h259, h2518, h52, h109, h10081, zero_mul, add_zero, mul_zero, hsq,
      hcub', hsqB] at heps
    rw [hPderiv, hQderiv, hRderiv] at heps
    linear_combination heps
  have hUderiv : d U0 =
      (3 / 2 : F) * L * d E0 +
        (4 / 3 : F) * P * d D0 + (4 / 3 : F) * D0 * d P +
        (7 / 6 : F) * Q * d C0 + (7 / 6 : F) * C0 * d Q +
        R * d B + B * d R +
        (5 / 6 : F) * S0 * d A + (5 / 6 : F) * A * d S0 -
        (5 / 2 : F) * A * d D0 - (5 / 2 : F) * D0 * d A -
        (5 / 2 : F) * B * d C0 - (5 / 2 : F) * C0 * d B -
        (2 : F) * A * B * d P - (2 : F) * A * P * d B -
        (2 : F) * B * P * d A -
        (7 / 8 : F) * (A * A) * d Q - (7 / 4 : F) * Q * A * d A -
        (9 / 4 : F) * L * A * d C0 - (9 / 4 : F) * L * C0 * d A -
        (9 / 4 : F) * L * B * d B +
        (25 / 8 : F) * (A * A) * d B + (25 / 4 : F) * A * B * d A +
        (45 / 16 : F) * L * (A * A) * d A := by
    have hexp :
        zetaResidual610 L A B C0 D0 E0 P Q R S0 U0 =
          U0 - (3 / 2 : F) * L * E0 - (4 / 3 : F) * P * D0 -
            (7 / 6 : F) * Q * C0 - R * B - (5 / 6 : F) * S0 * A +
            (5 / 2 : F) * A * D0 + (5 / 2 : F) * B * C0 +
            (2 : F) * A * B * P + (7 / 8 : F) * Q * (A * A) +
            (9 / 4 : F) * L * A * C0 + (9 / 8 : F) * L * (B * B) -
            (25 / 8 : F) * (A * A) * B -
            (15 / 16 : F) * L * (A * A * A) := by
      simp only [zetaResidual610, alphaResidual610, betaResidual610,
        gammaResidual610, deltaResidual610, pow_two, pow_three]
      ring
    have hz := hzeta
    rw [hexp] at hz
    have h25 : d (25 : F) = 0 := d.map_natCast 25
    have h15 : d (15 : F) = 0 := d.map_natCast 15
    have h52 : d (5 / 2 : F) = 0 := by
      simp [Derivation.leibniz_div, h2, h5]
    have h78 : d (7 / 8 : F) = 0 := by
      simp [Derivation.leibniz_div, h8, h7]
    have h94 : d (9 / 4 : F) = 0 := by
      simp [Derivation.leibniz_div, h4, h9]
    have h98 : d (9 / 8 : F) = 0 := by
      simp [Derivation.leibniz_div, h8, h9]
    have h258 : d (25 / 8 : F) = 0 := by
      simp [Derivation.leibniz_div, h8, h25]
    have h16ne : (16 : F) ≠ 0 := by norm_num
    have h16inv : d (16 : F)⁻¹ = 0 := by
      have hone : (16 : F) * (16 : F)⁻¹ = 1 := mul_inv_cancel₀ h16ne
      have hd1 : d ((16 : F) * (16 : F)⁻¹) = 0 := by
        rw [hone]
        exact d.map_one_eq_zero
      have hleib :
          d ((16 : F) * (16 : F)⁻¹) =
            (16 : F) • d (16 : F)⁻¹ + (16 : F)⁻¹ • d (16 : F) :=
        Derivation.leibniz d (16 : F) (16 : F)⁻¹
      have hsum : (16 : F) * d (16 : F)⁻¹ + (16 : F)⁻¹ * d (16 : F) = 0 := by
        simpa [smul_eq_mul, hd1] using hleib.symm
      have honly : (16 : F) * d (16 : F)⁻¹ = 0 := by
        simpa [h16, mul_zero, add_zero] using hsum
      exact (mul_eq_zero.mp honly).resolve_left h16ne
    have h1516 : d (15 / 16 : F) = 0 := by
      simp [div_eq_mul_inv, Derivation.leibniz, h15, h16inv, zero_mul,
        add_zero, mul_zero]
    have hcub' : d (A * A * A) = (3 : F) * (A * A) * d A := by
      simp [Derivation.leibniz]
      ring
    simp [map_sub, map_add, Derivation.leibniz, h32, h43, h76, h56c, hL,
      h52, h78, h94, h98, h258, h1516, zero_mul, add_zero, mul_zero, hsq,
      hsqB, hcub', h2] at hz
    linear_combination hz
  have hVderiv : d V0 =
      (2 / 3 : F) * (d A * T0 + A * d T0) +
        (5 / 6 : F) * (d B * S0 + B * d S0) +
        (d C0 * R + C0 * d R) -
        (2 / 3 : F) * ((2 : F) * A * d A * R + (A * A) * d R) +
        (7 / 6 : F) * (d D0 * Q + D0 * d Q) -
        (14 / 9 : F) * (d A * B * Q + A * d B * Q + A * B * d Q) +
        (4 / 3 : F) * (d E0 * P + E0 * d P) -
        (16 / 9 : F) * (d A * C0 * P + A * d C0 * P + A * C0 * d P) -
        (8 / 9 : F) * ((2 : F) * B * d B * P + (B * B) * d P) +
        (56 / 81 : F) * ((3 : F) * (A * A) * d A * P +
          (A * A * A) * d P) -
        (20 / 9 : F) * (d A * E0 + A * d E0) -
        (20 / 9 : F) * (d B * D0 + B * d D0) -
        (10 / 9 : F) * ((2 : F) * C0 * d C0) -
        (2 : F) * L * (d A * D0 + A * d D0) -
        (2 : F) * L * (d B * C0 + B * d C0) +
        (7 / 3 : F) * L * ((2 : F) * A * d A * B + (A * A) * d B) +
        (70 / 27 : F) * ((2 : F) * A * d A * C0 + (A * A) * d C0) +
        (70 / 27 : F) * (d A * (B * B) + A * ((2 : F) * B * d B)) -
        (175 / 243 : F) * ((4 : F) * (A * A * A) * d A) := by
    have hexp :
        etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0 =
          V0 - (2 / 3 : F) * A * T0 - (5 / 6 : F) * B * S0 - C0 * R +
            (2 / 3 : F) * (A * A) * R - (7 / 6 : F) * D0 * Q +
            (14 / 9 : F) * A * B * Q - (4 / 3 : F) * E0 * P +
            (16 / 9 : F) * A * C0 * P + (8 / 9 : F) * (B * B) * P -
            (56 / 81 : F) * (A * A * A) * P + (20 / 9 : F) * A * E0 +
            (20 / 9 : F) * B * D0 + (10 / 9 : F) * (C0 * C0) +
            (2 : F) * A * D0 * L + (2 : F) * B * C0 * L -
            (7 / 3 : F) * (A * A) * B * L - (70 / 27 : F) * (A * A) * C0 -
            (70 / 27 : F) * A * (B * B) +
            (175 / 243 : F) * (A * A * A * A) := by
      simp only [etaResidual610, alphaResidual610, betaResidual610,
        gammaResidual610, deltaResidual610, epsilonResidual610, pow_two,
        pow_three]
      ring
    have h14 : d (14 : F) = 0 := d.map_natCast 14
    have h20 : d (20 : F) = 0 := d.map_natCast 20
    have h56 : d (56 : F) = 0 := d.map_natCast 56
    have h70 : d (70 : F) = 0 := d.map_natCast 70
    have h175 : d (175 : F) = 0 := d.map_natCast 175
    have h10 : d (10 : F) = 0 := d.map_natCast 10
    have h149 : d (14 / 9 : F) = 0 := by
      simp [Derivation.leibniz_div, h9, h14]
    have h169 : d (16 / 9 : F) = 0 := by
      simp [Derivation.leibniz_div, h9, h16]
    have h89 : d (8 / 9 : F) = 0 := by
      simp [Derivation.leibniz_div, h9, h8]
    have h5681 : d (56 / 81 : F) = 0 := by
      simp [Derivation.leibniz_div, h81, h56]
    have h209 : d (20 / 9 : F) = 0 := by
      simp [Derivation.leibniz_div, h9, h20]
    have h73 : d (7 / 3 : F) = 0 := by
      simp [Derivation.leibniz_div, h3, h7]
    have h7027 : d (70 / 27 : F) = 0 := by
      simp [Derivation.leibniz_div, h27, h70]
    have h175243 : d (175 / 243 : F) = 0 := by
      simp [Derivation.leibniz_div, h243, h175]
    have h109' : d (10 / 9 : F) = 0 := by
      simp [Derivation.leibniz_div, h9, h10]
    have hcub' : d (A * A * A) = (3 : F) * (A * A) * d A := by
      simp [Derivation.leibniz]
      ring
    have hquart : d (A * A * A * A) =
        (4 : F) * (A * A * A) * d A := by
      simp [Derivation.leibniz]
      ring
    have hdAT : d ((2 / 3 : F) * A * T0) =
        (2 / 3 : F) * (d A * T0 + A * d T0) := by
      simp [Derivation.leibniz, smul_eq_mul, h23]
      ring
    have hdBS : d ((5 / 6 : F) * B * S0) =
        (5 / 6 : F) * (d B * S0 + B * d S0) := by
      simp [Derivation.leibniz, smul_eq_mul, h56c]
      ring
    have hdCR : d (C0 * R) = d C0 * R + C0 * d R := by
      simp [Derivation.leibniz, smul_eq_mul]
      ring
    have hdA2R : d ((2 / 3 : F) * (A * A) * R) =
        (2 / 3 : F) * ((2 : F) * A * d A * R + (A * A) * d R) := by
      simp [Derivation.leibniz, smul_eq_mul, h23, hsq]
      ring
    have hdDQ : d ((7 / 6 : F) * D0 * Q) =
        (7 / 6 : F) * (d D0 * Q + D0 * d Q) := by
      simp [Derivation.leibniz, smul_eq_mul, h76]
      ring
    have hdABQ : d ((14 / 9 : F) * A * B * Q) =
        (14 / 9 : F) * (d A * B * Q + A * d B * Q + A * B * d Q) := by
      simp [Derivation.leibniz, smul_eq_mul, h149]
      ring
    have hdEP : d ((4 / 3 : F) * E0 * P) =
        (4 / 3 : F) * (d E0 * P + E0 * d P) := by
      simp [Derivation.leibniz, smul_eq_mul, h43]
      ring
    have hdACP : d ((16 / 9 : F) * A * C0 * P) =
        (16 / 9 : F) * (d A * C0 * P + A * d C0 * P + A * C0 * d P) := by
      simp [Derivation.leibniz, smul_eq_mul, h169]
      ring
    have hdB2P : d ((8 / 9 : F) * (B * B) * P) =
        (8 / 9 : F) * ((2 : F) * B * d B * P + (B * B) * d P) := by
      simp [Derivation.leibniz, smul_eq_mul, h89, hsqB]
      ring
    have hdA3P : d ((56 / 81 : F) * (A * A * A) * P) =
        (56 / 81 : F) * ((3 : F) * (A * A) * d A * P +
          (A * A * A) * d P) := by
      simp [Derivation.leibniz, smul_eq_mul, h5681, hcub']
      ring
    have hdAE : d ((20 / 9 : F) * A * E0) =
        (20 / 9 : F) * (d A * E0 + A * d E0) := by
      simp [Derivation.leibniz, smul_eq_mul, h209]
      ring
    have hdBD : d ((20 / 9 : F) * B * D0) =
        (20 / 9 : F) * (d B * D0 + B * d D0) := by
      simp [Derivation.leibniz, smul_eq_mul, h209]
      ring
    have hdC2 : d ((10 / 9 : F) * (C0 * C0)) =
        (10 / 9 : F) * ((2 : F) * C0 * d C0) := by
      simp [Derivation.leibniz, smul_eq_mul, h109', hsqC]
      try ring
    have hdADL : d ((2 : F) * A * D0 * L) =
        (2 : F) * L * (d A * D0 + A * d D0) := by
      simp [Derivation.leibniz, smul_eq_mul, h2, hL, zero_mul, add_zero]
      ring
    have hdBCL : d ((2 : F) * B * C0 * L) =
        (2 : F) * L * (d B * C0 + B * d C0) := by
      simp [Derivation.leibniz, smul_eq_mul, h2, hL, zero_mul, add_zero]
      ring
    have hdA2BL : d ((7 / 3 : F) * (A * A) * B * L) =
        (7 / 3 : F) * L * ((2 : F) * A * d A * B + (A * A) * d B) := by
      simp [Derivation.leibniz, smul_eq_mul, h73, hL, hsq, zero_mul,
        add_zero]
      ring
    have hdA2C : d ((70 / 27 : F) * (A * A) * C0) =
        (70 / 27 : F) * ((2 : F) * A * d A * C0 + (A * A) * d C0) := by
      simp [Derivation.leibniz, smul_eq_mul, h7027, hsq]
      ring
    have hdAB2 : d ((70 / 27 : F) * A * (B * B)) =
        (70 / 27 : F) * (d A * (B * B) + A * ((2 : F) * B * d B)) := by
      simp [Derivation.leibniz, smul_eq_mul, h7027, hsqB]
      ring
    have hdA4 : d ((175 / 243 : F) * (A * A * A * A)) =
        (175 / 243 : F) * ((4 : F) * (A * A * A) * d A) := by
      simp [Derivation.leibniz, smul_eq_mul, h175243, hquart]
      try ring
    have he := heta
    rw [hexp] at he
    simp only [map_sub, map_add, hdAT, hdBS, hdCR, hdA2R, hdDQ, hdABQ,
      hdEP, hdACP, hdB2P, hdA3P, hdAE, hdBD, hdC2, hdADL, hdBCL, hdA2BL,
      hdA2C, hdAB2, hdA4] at he
    linear_combination he

  have hWderiv :
      d W0 = (7 / 6 : F) * Q * d E0 + R * d D0 +
        (5 / 6 : F) * S0 * d C0 + (2 / 3 : F) * T0 * d B +
        (1 / 2 : F) * U0 * d A -
        (1 / 6 : F) * D0 * d R - (1 / 3 : F) * C0 * d S0 -
        (1 / 2 : F) * B * d T0 - (2 / 3 : F) * A * d U0 := by
    linear_combination (-1 / 6 : F) * hrow6
  have hrow_red := hrow
  simp only [hWderiv, hPderiv, hQderiv, hRderiv, hSderiv, hTderiv, hUderiv,
    hVderiv] at hrow_red
  simp only [bridgeKappaResidual610, map_sub, map_add, Derivation.leibniz,
    smul_eq_mul, h16f, h13, h12, h18f, h23, h29, h56c, h351296, h536,
    h572, h20243, h427, h827, h481, h49, h38531104, h35432, h736, h772,
    h3256, h332, h964, h316, h38, h34, h35729, h2081, h1027, h527, h109,
    hL, halpha, hbeta, hgamma, hdelta, hepsilon, hzeta, heta, htheta,
    hsq, hsqB, hsqC, hsqD, hcub, hcubB, hquar, hquint, pow_two,
    pow_three, zero_mul, add_zero, mul_zero]
  simp only [alphaResidual610, betaResidual610, gammaResidual610,
    deltaResidual610, epsilonResidual610, zetaResidual610,
    etaResidual610, bridgeThetaResidual610, pow_two, pow_three]
  linear_combination (1 / 6 : F) * hrow_red

end BridgeKappaDepressedRows610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaJetFactor610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 40000000 in
/-- On the fifteenth-face jet the cleared `κ` defect factors exactly as
`h⁴⁸` times its factored order-`48` head plus `h` times the tail. -/
theorem bridgeClearedKappaDefect610_jet_factored
    (h w1 a41 p31 s1 u1 b62 q52 p2 p1 p0 q4 q3 q2 q1 : k[X])
    (lambda : k) :
    bridgeClearedKappaDefect610 h (h ^ 5 * w1) (h ^ 3 * a41)
        (h * p31) p2 p1 p0 (h ^ 7 * s1) (h ^ 5 * u1) (h ^ 4 * b62)
        (h ^ 2 * q52) q4 q3 q2 q1 lambda =
      h ^ 48 *
        (bridgeKappaJetHead610 a41 p31 s1 u1 q52 q4 +
          h * bridgeKappaJetTail610 h w1 a41 p31 s1 u1 b62 q52 p2 p1
            p0 q4 q3 q2 q1 (Polynomial.C lambda)) := by
  unfold bridgeClearedKappaDefect610 bridgeKappaJetHead610 bridgeKappaJetTail610
  ring

end BridgeKappaJetFactor610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaJetFactor610

variable {k : Type*} [Field k] [CharZero k]

/-- Evaluation commutes with the order-`48` head. -/
theorem bridgeKappaJetHead610_eval
    (a41 p31 s1 u1 q52 q4 : k[X]) (x : k) :
    (bridgeKappaJetHead610 a41 p31 s1 u1 q52 q4).eval x =
      bridgeKappaJetHead610 (a41.eval x) (p31.eval x) (s1.eval x)
        (u1.eval x) (q52.eval x) (q4.eval x) := by
  simp only [bridgeKappaJetHead610, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat]

end BridgeKappaJetFactor610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaScalars610

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 4000000 in
/-- Chamber-free reduction of the vanishing order-`48` head modulo the
tenth-face root laws alone: the head reduces to the exact factored
relation `a₄₁ p₃₁³ = 0`. -/
theorem bridgeKappa_chamberFree_split610
    (a41 p31 s1 u1 q52 q4 : F)
    (hhead : bridgeKappaJetHead610 a41 p31 s1 u1 q52 q4 = 0)
    (hs : (3 : F) * s1 = (5 : F) * a41)
    (hu : (3 : F) * u1 = (5 : F) * p31)
    (hq52 : (9 : F) * q52 = (10 : F) * a41 * p31)
    (hq4 : (9 : F) * q4 = (5 : F) * p31 ^ 2) :
    a41 * p31 ^ 3 = 0 := by
  simp only [bridgeKappaJetHead610] at hhead
  linear_combination (1 / 580475289600 : F) * hhead -
      (11 / 15 : F) * p31 ^ 3 * hs -
      (77 / 40 : F) * a41 * p31 ^ 2 * hu +
      (1 / 4 : F) * p31 ^ 2 * hq52 + (2 / 5 : F) * a41 * p31 * hq4

end BridgeKappaScalars610

end Max11DegreeRoutes
open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

section BridgeKappaPowerRelation610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 80000000 in
/-- The tenth sextic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h⁵⁵`.  The degree-`5` iota
integral and the exact `18 q₀ h⁵⁰` residual remain available from the
ninth packet. -/
theorem nonzeroFace610_bridgeKappaPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ mu : k,
      bridgeClearedKappaDefect610 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) lambda =
        Polynomial.C mu * h0 ^ 55 := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let a4 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 4)
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
  have hh : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 6) = hRF ^ 6 := by
    simp only [hp6, hH, hRF, map_pow]
    ring
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = hRF ^ 10 := by
    simp only [hq10, hH, hRF, map_pow]
    ring
  have hpDep := affineDepress_sourceSextic68 p hRF
    (sexticDepressionR610 hRF a5) hp hh hpTop rfl
  have hNrat : 5 * a5 * hRF ^ 4 - 3 * b9 = RatFunc.C lambda * hRF ^ 9 := by
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hN
    have hH2 : algebraMap k[X] (RatFunc k) (H ^ 2) = hRF ^ 4 := by
      simp only [hH, hRF, map_pow]
      ring
    have hh9 : algebraMap k[X] (RatFunc k) (h0 ^ 9) = hRF ^ 9 := by
      simp only [hRF, map_pow]
    have hleft : algebraMap k[X] (RatFunc k)
        ((5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9) =
        5 * a5 * hRF ^ 4 - 3 * b9 := by
      simp only [map_sub, map_mul, map_ofNat, a5, b9, hH2]
    have hright : algebraMap k[X] (RatFunc k)
        (Polynomial.C lambda * h0 ^ 9) =
        RatFunc.C lambda * hRF ^ 9 := by
      simp only [map_mul, RatFunc.algebraMap_C, hh9]
    exact hleft.symm.trans (hmapped.trans hright)
  have hLval :
      depressedL610 hRF (sexticDepressionR610 hRF a5) b9 =
        RatFunc.C (-lambda / 3) := by
    have hL := depressedL610_eq_of_ninthPower hRF a5 b9
      (RatFunc.C lambda) hh (by simpa using hNrat)
    simpa [map_neg, map_div₀, map_ofNat] using hL
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j hRF (sexticDepressionR610 hRF a5) hh hD
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5) (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5) (sourceToRatFunc68 q)
  have hf5 : f.coeff 5 = 0 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedSextic68_five]
  have hf6 : f.coeff 6 = 1 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedSextic68_six]
  have hf_high : ∀ n, 6 < n → f.coeff n = 0 := by
    intro n hn
    dsimp only [f]
    rw [hpDep, coeff_depressedSextic68_of_gt_six _ _ _ _ _ hn]
  have hg_high_src : ∀ n, 10 < n → (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = hRF ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src
  have hg7 :
      g.coeff 7 =
        depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff7_810 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedQ610, depressedQ810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8, b7]
  have hg6 :
      g.coeff 6 =
        depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff6_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedR610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6]
  have hg5 :
      g.coeff 5 =
        depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6
          b5 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff5_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedS610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5]
  have hg4 :
      g.coeff 4 =
        depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
          b4 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff4_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedT610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4]
  have hg2 :
      g.coeff 2 =
        depressedV610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
          b4 b3 b2 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff2_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedV610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2]
  have hg3 :
      g.coeff 3 =
        depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
          b4 b3 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff3_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedU610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3]
  have hg1 :
      g.coeff 1 =
        terminalDepressedW610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
          b4 b3 b2 b1 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff1_610_bridge (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [terminalDepressedW610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2, b1]
  have hg8' :
      g.coeff 8 =
        depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8 := by
    dsimp only [g]
    rw [hg8]
    simp [depressedP610, depressedP810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8]
  have hg9' : g.coeff 9 = RatFunc.C (-lambda / 3) := by
    dsimp only [g]
    rw [hg9]
    have : -10 * sexticDepressionR610 hRF a5 +
        (sourceToRatFunc68 q).coeff 9 / hRF ^ 9 =
          depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
      simp [depressedL610, depressedL810, sexticDepressionR610,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    rw [this, hLval]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hg9']
    have hx := ratFuncDerivation46_polynomial (C (-lambda / 3) : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hrow13 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 4) -
        (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 8) = 0 := by
    have hrow :=
      differentialJacobian_coeff_13_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 13) hbracket
    simpa [f, g, Polynomial.coeff_C, show (13 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow12 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 3) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 4) -
        (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 7) = 0 := by
    have hrow :=
      differentialJacobian_coeff_12_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 12) hbracket
    simpa [f, g, Polynomial.coeff_C, show (12 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow11 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 2) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 3) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 4) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 8) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 6) = 0 := by
    have hrow :=
      differentialJacobian_coeff_11_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 11) hbracket
    simpa [f, g, Polynomial.coeff_C, show (11 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow10 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 1) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 2) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 3) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 4) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 8) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 7) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 5) = 0 := by
    have hrow :=
      differentialJacobian_coeff_10_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 10) hbracket
    simpa [f, g, Polynomial.coeff_C, show (10 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow9 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 0) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 1) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 2) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 3) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 4) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 8) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 7) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 6) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 4) = 0 := by
    have hrow :=
      differentialJacobian_coeff_9_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 9) hbracket
    simpa [f, g, Polynomial.coeff_C, show (9 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow7 :
      (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 0) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 1) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 2) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 3) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 4) -
          (1 : RatFunc k) * f.coeff 1 * ratFuncDerivation68 (g.coeff 7) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 6) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 5) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 4) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 2) = 0 := by
    have hrow :=
      differentialJacobian_coeff_7_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 7) hbracket
    simpa [f, g, Polynomial.coeff_C, show (7 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow8 :
      (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 0) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 1) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 2) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 3) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 4) -
          (1 : RatFunc k) * f.coeff 1 * ratFuncDerivation68 (g.coeff 8) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 7) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 6) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 5) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 3) = 0 := by
    have hrow :=
      differentialJacobian_coeff_8_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 8) hbracket
    simpa [f, g, Polynomial.coeff_C, show (8 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow6 :
      (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 0) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 1) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 2) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 3) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 4) -
          (1 : RatFunc k) * f.coeff 1 * ratFuncDerivation68 (g.coeff 6) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 5) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 4) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 3) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 1) = 0 := by
    have hrow :=
      differentialJacobian_coeff_6_monicSexticDecic_bridge
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 6) hbracket
    simpa [f, g, Polynomial.coeff_C, show (6 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow4 :
      (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 0) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 1) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 2) +
        (2 : RatFunc k) * g.coeff 2 * ratFuncDerivation68 (f.coeff 3) +
        (1 : RatFunc k) * g.coeff 1 * ratFuncDerivation68 (f.coeff 4) -
          (1 : RatFunc k) * f.coeff 1 * ratFuncDerivation68 (g.coeff 4) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 3) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 2) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 1) = 0 := by
    have hrow :=
      differentialJacobian_coeff_4_monicSexticDecic_bridge
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 4) hbracket
    simpa [f, g, Polynomial.coeff_C, show (4 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hf4 : f.coeff 4 =
      depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4 := by
    dsimp only [f, depressedA610, a5, a4]
    rw [hpDep, coeff_depressedSextic68_four]
  have hf3 : f.coeff 3 =
      depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 := by
    dsimp only [f, depressedB610, a5, a4, a3]
    rw [hpDep, coeff_depressedSextic68_three]
  have hf2 : f.coeff 2 =
      depressedC610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 := by
    dsimp only [f, depressedC610, a5, a4, a3, a2]
    rw [hpDep, coeff_depressedSextic68_two]
  have hf1 : f.coeff 1 =
      depressedD610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1 := by
    dsimp only [f, depressedD610, a5, a4, a3, a2, a1]
    rw [hpDep, coeff_depressedSextic68_one]
  have hf0 : f.coeff 0 =
      depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1
        a0 := by
    dsimp only [f, depressedE610, a5, a4, a3, a2, a1, a0]
    rw [hpDep, coeff_depressedSextic68_zero]
  have halpha0 :
      ratFuncDerivation68 (alphaResidual610 (f.coeff 4) (g.coeff 8)) = 0 :=
    alphaResidual610_deriv_zero ratFuncDerivation68 (f.coeff 4)
      (g.coeff 8) hrow13
  have hbeta0 :
      ratFuncDerivation68
        (betaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (g.coeff 7)) = 0 :=
    betaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (g.coeff 7) hLconst (by simpa using hrow12)
  have hgamma0 :
      ratFuncDerivation68
        (gammaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (g.coeff 8) (g.coeff 6)) = 0 :=
    gammaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (g.coeff 8) (g.coeff 6)
      hLconst halpha0 (by simpa using hrow11)
  have hdelta0 :
      ratFuncDerivation68
        (deltaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (g.coeff 8) (g.coeff 7)
          (g.coeff 5)) = 0 :=
    deltaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (g.coeff 8)
      (g.coeff 7) (g.coeff 5) hLconst halpha0 hbeta0
      (by simpa using hrow10)
  have heps0deriv :
      ratFuncDerivation68
        (epsilonResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 4)) = 0 :=
    epsilonResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 4) hLconst halpha0
      hbeta0 hgamma0 (by simpa using hrow9)
  have hzeta0deriv :
      ratFuncDerivation68
        (zetaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 3)) = 0 :=
    zetaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 3)
      hLconst halpha0 hbeta0 hgamma0 hdelta0 (by simpa using hrow8)
  have heta0deriv :
      ratFuncDerivation68
        (etaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 2)) = 0 :=
    etaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 2) hLconst halpha0 hbeta0 hgamma0 hdelta0 heps0deriv
      (by simpa using hrow7)
  have htheta0deriv :
      ratFuncDerivation68
        (bridgeThetaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 1)) = 0 :=
    bridgeThetaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 1) hLconst halpha0 hbeta0 hgamma0 hdelta0
      heps0deriv hzeta0deriv (by simpa using hrow6)
  have hkappa0deriv :
      ratFuncDerivation68
        (bridgeKappaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1)) = 0 :=
    bridgeKappaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1) hLconst halpha0 hbeta0
      hgamma0 hdelta0 heps0deriv hzeta0deriv heta0deriv htheta0deriv
      (by simpa using hrow6) (by simpa using hrow4)
  obtain ⟨mu0, hmu0⟩ :
      ∃ a : k,
        bridgeKappaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
            (g.coeff 2) (g.coeff 1) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      hkappa0deriv
  have hclear :
      algebraMap k[X] (RatFunc k)
          (bridgeClearedKappaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            lambda) =
        (3761479876608 : RatFunc k) * hRF ^ 55 *
          bridgeKappaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
            (g.coeff 2) (g.coeff 1) := by
    have hF := bridgeKappaDefect_eq_cleared610 hRF a5 a4 a3 a2 a1 a0 b9
      b8 b7 b6 b5 b4 b3 b2 b1 (RatFunc.C lambda) hh
      (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL610, depressedL810, sexticDepressionR610,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    unfold bridgeClearedKappaDefect610 bridgeKappaResidual610 alphaResidual610 betaResidual610 deltaResidual610 epsilonResidual610 zetaResidual610 etaResidual610 bridgeThetaResidual610 at hF ⊢
    simpa [gammaResidual610, map_sub, map_add, map_mul, map_pow, map_ofNat, map_neg, RatFunc.algebraMap_C, hRF, a5, a4, a3, a2, a1, a0, b8, b7, b6, b5, b4, b3, b2, b1, hf4, hf3, hf2, hf1, hf0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8', hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (bridgeClearedKappaDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (3761479876608 * mu0) * h0 ^ 55) := by
    rw [hclear, hmu0]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨3761479876608 * mu0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

end BridgeKappaPowerRelation610

end Max11DegreeRoutes
