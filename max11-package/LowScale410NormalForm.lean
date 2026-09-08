import LowScale68ScaleZero

/-!
# Direct differential normal form for the normalized `(4,10)` leaf

The quartic normal form and its coefficientwise derivation are reused from
the completed `(4,6)` route.  The decic side has six more coefficient rows
than the sextic side.  This module expands all twelve non-top rows
after the nonic coefficient has been shown constant, and integrates the
first four triangular rows.  It uses neither the arbitrary-pair nor the
twice-prime interface.
-/

noncomputable section

set_option maxHeartbeats 1000000

open Polynomial

namespace Max11DegreeRoutes

section DifferentialNormalForm410

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Monic decic whose nonic coefficient is a differential constant. -/
def depressedDecic410 (L P Q R S T U V W Z : F) : F[X] :=
  X ^ 10 + C L * X ^ 9 + C P * X ^ 8 + C Q * X ^ 7 +
    C R * X ^ 6 + C S * X ^ 5 + C T * X ^ 4 + C U * X ^ 3 +
    C V * X ^ 2 + C W * X + C Z

/-- Coefficientwise derivative of a depressed decic after its nonic
coefficient is known to be constant. -/
theorem coefficientDeriv_depressedDecic410 (d : Derivation k F F)
    (L P Q R S T U V W Z : F) (hL : d L = 0) :
    coefficientDeriv d (depressedDecic410 L P Q R S T U V W Z) =
      C (d P) * X ^ 8 + C (d Q) * X ^ 7 + C (d R) * X ^ 6 +
        C (d S) * X ^ 5 + C (d T) * X ^ 4 + C (d U) * X ^ 3 +
        C (d V) * X ^ 2 + C (d W) * X + C (d Z) := by
  ext n
  simp [depressedDecic410, hL, Polynomial.coeff_X, Polynomial.coeff_C]
  split_ifs <;> simp_all

/-- The twelve exact non-top rows of the depressed `(4,10)` differential
Jacobian, ordered from `z^11` down to the constant row.  Before imposing
`d L = 0`, there is one additional top row `-4 dL * z^12`.

Compared with `differentialJacobian_depressed46_eq`, the first two rows have
the identical triangular shape with `6` replaced by `10`; the remaining ten
rows are the genuinely new decic system. -/
theorem differentialJacobian_depressed410_eq (d : Derivation k F F)
    (L P Q R S T U V W Z A B C0 : F) (hL : d L = 0) :
    differentialJacobian d (depressedQuartic46 A B C0)
        (depressedDecic410 L P Q R S T U V W Z) =
      C (10 * d A - 4 * d P) * X ^ 11 +
      C (9 * L * d A + 10 * d B - 4 * d Q) * X ^ 10 +
      C (8 * P * d A + 9 * L * d B + 10 * d C0 -
        2 * A * d P - 4 * d R) * X ^ 9 +
      C (7 * Q * d A + 8 * P * d B + 9 * L * d C0 -
        2 * A * d Q - B * d P - 4 * d S) * X ^ 8 +
      C (6 * R * d A + 7 * Q * d B + 8 * P * d C0 -
        2 * A * d R - B * d Q - 4 * d T) * X ^ 7 +
      C (5 * S * d A + 6 * R * d B + 7 * Q * d C0 -
        2 * A * d S - B * d R - 4 * d U) * X ^ 6 +
      C (4 * T * d A + 5 * S * d B + 6 * R * d C0 -
        2 * A * d T - B * d S - 4 * d V) * X ^ 5 +
      C (3 * U * d A + 4 * T * d B + 5 * S * d C0 -
        2 * A * d U - B * d T - 4 * d W) * X ^ 4 +
      C (2 * V * d A + 3 * U * d B + 4 * T * d C0 -
        2 * A * d V - B * d U - 4 * d Z) * X ^ 3 +
      C (W * d A + 2 * V * d B + 3 * U * d C0 -
        2 * A * d W - B * d V) * X ^ 2 +
      C (W * d B + 2 * V * d C0 - 2 * A * d Z - B * d W) * X +
      C (W * d C0 - B * d Z) := by
  rw [differentialJacobian, coefficientDeriv_depressedQuartic46,
    coefficientDeriv_depressedDecic410 d L P Q R S T U V W Z hL]
  simp only [depressedQuartic46, depressedDecic410,
    Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_X,
    Polynomial.derivative_C, Polynomial.C_0, zero_mul, zero_add,
    one_mul, mul_one]
  push_cast
  simp only [map_add, map_sub, map_mul, map_neg, map_natCast]
  ring

section IntegratedUpperRows410

variable [CharZero F]

/-- First integrated decic coefficient (the `z^11` row). -/
def integratedP410 (A alpha : F) : F :=
  (5 / 2 : F) * A + alpha

/-- Second integrated decic coefficient (the `z^10` row). -/
def integratedQ410 (L A B beta : F) : F :=
  (9 / 4 : F) * L * A + (5 / 2 : F) * B + beta

/-- Third integrated decic coefficient (the `z^9` row). -/
def integratedR410 (L A B C0 alpha gamma : F) : F :=
  (15 / 8 : F) * A ^ 2 + 2 * alpha * A +
    (9 / 4 : F) * L * B + (5 / 2 : F) * C0 + gamma

/-- Fourth integrated decic coefficient (the `z^8` row). -/
def integratedS410 (L A B C0 alpha beta delta : F) : F :=
  (45 / 32 : F) * L * A ^ 2 + (15 / 4 : F) * A * B +
    (7 / 4 : F) * beta * A + 2 * alpha * B +
    (9 / 4 : F) * L * C0 + delta

/-- Fifth integrated decic coefficient (the `z^7` row). -/
def integratedT410 (L A B C0 alpha beta gamma epsilon : F) : F :=
  (5 / 16 : F) * A ^ 3 + alpha * A ^ 2 +
    (45 / 16 : F) * L * A * B + (15 / 4 : F) * A * C0 +
    (3 / 2 : F) * gamma * A + (15 / 8 : F) * B ^ 2 +
    (7 / 4 : F) * beta * B + 2 * alpha * C0 + epsilon

/-- Sixth integrated decic coefficient (the `z^6` row). -/
def integratedU410 (L A B C0 alpha beta gamma delta zeta : F) : F :=
  (15 / 128 : F) * L * A ^ 3 + (15 / 16 : F) * A ^ 2 * B +
    (21 / 32 : F) * beta * A ^ 2 + 2 * alpha * A * B +
    (45 / 16 : F) * L * A * C0 + (45 / 32 : F) * L * B ^ 2 +
    (5 / 4 : F) * delta * A + (15 / 4 : F) * B * C0 +
    (3 / 2 : F) * gamma * B + (7 / 4 : F) * beta * C0 + zeta

/-- Seventh integrated decic coefficient (the `z^5` row). -/
def integratedV410 (L A B C0 alpha beta gamma delta epsilon eta : F) : F :=
  (-5 / 128 : F) * A ^ 4 + (45 / 128 : F) * L * A ^ 2 * B +
    (15 / 16 : F) * A ^ 2 * C0 + (3 / 8 : F) * gamma * A ^ 2 +
    (15 / 16 : F) * A * B ^ 2 + (21 / 16 : F) * beta * A * B +
    2 * alpha * A * C0 + alpha * B ^ 2 +
    (45 / 16 : F) * L * B * C0 + epsilon * A +
    (5 / 4 : F) * delta * B + (15 / 8 : F) * C0 ^ 2 +
    (3 / 2 : F) * gamma * C0 + eta

/-- Eighth integrated decic coefficient (the `z^4` row). -/
def integratedW410 (L A B C0 alpha beta gamma delta epsilon zeta theta : F) : F :=
  (-45 / 2048 : F) * L * A ^ 4 - (5 / 32 : F) * A ^ 3 * B -
    (7 / 128 : F) * beta * A ^ 3 + (45 / 128 : F) * L * A ^ 2 * C0 +
    (45 / 128 : F) * L * A * B ^ 2 + (5 / 32 : F) * delta * A ^ 2 +
    (15 / 8 : F) * A * B * C0 + (3 / 4 : F) * gamma * A * B +
    (21 / 16 : F) * beta * A * C0 + (5 / 16 : F) * B ^ 3 +
    (21 / 32 : F) * beta * B ^ 2 + 2 * alpha * B * C0 +
    (45 / 32 : F) * L * C0 ^ 2 + (3 / 4 : F) * zeta * A +
    epsilon * B + (5 / 4 : F) * delta * C0 + theta

/-- Ninth integrated decic coefficient (the `z^3` row). -/
def integratedZ410
    (L A B C0 alpha beta gamma delta epsilon zeta eta iota : F) : F :=
  (3 / 256 : F) * A ^ 5 - (45 / 512 : F) * L * A ^ 3 * B -
    (5 / 32 : F) * A ^ 3 * C0 - (1 / 16 : F) * gamma * A ^ 3 -
    (15 / 64 : F) * A ^ 2 * B ^ 2 - (21 / 128 : F) * beta * A ^ 2 * B +
    (45 / 64 : F) * L * A * B * C0 + (15 / 128 : F) * L * B ^ 3 +
    (5 / 16 : F) * delta * A * B + (15 / 16 : F) * A * C0 ^ 2 +
    (3 / 4 : F) * gamma * A * C0 + (15 / 16 : F) * B ^ 2 * C0 +
    (3 / 8 : F) * gamma * B ^ 2 + (21 / 16 : F) * beta * B * C0 +
    alpha * C0 ^ 2 + (1 / 2 : F) * eta * A +
    (3 / 4 : F) * zeta * B + epsilon * C0 + iota

/-- The first four decic rows integrate universally.  This is the exact
triangular prefix needed before the six new middle rows and three terminal
rows can be studied. -/
theorem integratedUpperFourRows410 (d : Derivation k F F)
    (L A B C0 alpha beta gamma delta : F)
    (hL : d L = 0) (halpha : d alpha = 0) (hbeta : d beta = 0)
    (hgamma : d gamma = 0) (hdelta : d delta = 0) :
    let P := integratedP410 A alpha
    let Q := integratedQ410 L A B beta
    let R := integratedR410 L A B C0 alpha gamma
    let S := integratedS410 L A B C0 alpha beta delta
    (10 * d A - 4 * d P = 0) ∧
    (9 * L * d A + 10 * d B - 4 * d Q = 0) ∧
    (8 * P * d A + 9 * L * d B + 10 * d C0 -
      2 * A * d P - 4 * d R = 0) ∧
    (7 * Q * d A + 8 * P * d B + 9 * L * d C0 -
      2 * A * d Q - B * d P - 4 * d S = 0) := by
  dsimp only
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h7 : d (7 : F) = 0 := d.map_natCast 7
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h10 : d (10 : F) = 0 := d.map_natCast 10
  have h15 : d (15 : F) = 0 := d.map_natCast 15
  have h32 : d (32 : F) = 0 := d.map_natCast 32
  have h45 : d (45 : F) = 0 := d.map_natCast 45
  have h52 : d (5 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h2, h5]
  have h94 : d (9 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h4, h9]
  have h158 : d (15 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h8, h15]
  have h4532 : d (45 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h32, h45]
  have h154 : d (15 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h4, h15]
  have h74 : d (7 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h4, h7]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [integratedP410, integratedQ410, integratedR410,
      integratedS410, map_add, map_sub, map_neg, Derivation.leibniz,
      Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, h52, h94,
      h158, h4532, h154, h74, hL, halpha, hbeta, hgamma, hdelta,
      mul_zero, zero_mul, add_zero, zero_add] <;>
    norm_num <;>
    (try simp only [h2, h4, h5, h7, h8, h9, h10, h15, h32, h45,
      map_zero, mul_zero, zero_mul, add_zero, zero_add]) <;>
    ring

/-- After all nine triangular upper rows are integrated, the `(4,10)`
Jacobian is exactly a three-row lower system.  This is the decic analogue of
`differentialJacobian_integrated46_eq`; unlike the sextic case, identifying
and exploiting primitives of these last three rows remains open. -/
theorem differentialJacobian_integrated410_eq (d : Derivation k F F)
    (L A B C0 alpha beta gamma delta epsilon zeta eta theta iota : F)
    (hL : d L = 0) (halpha : d alpha = 0) (hbeta : d beta = 0)
    (hgamma : d gamma = 0) (hdelta : d delta = 0)
    (hepsilon : d epsilon = 0) (hzeta : d zeta = 0)
    (heta : d eta = 0) (htheta : d theta = 0) (hiota : d iota = 0) :
    let P := integratedP410 A alpha
    let Q := integratedQ410 L A B beta
    let R := integratedR410 L A B C0 alpha gamma
    let S := integratedS410 L A B C0 alpha beta delta
    let T := integratedT410 L A B C0 alpha beta gamma epsilon
    let U := integratedU410 L A B C0 alpha beta gamma delta zeta
    let V := integratedV410 L A B C0 alpha beta gamma delta epsilon eta
    let W := integratedW410 L A B C0 alpha beta gamma delta epsilon zeta theta
    let Z := integratedZ410 L A B C0 alpha beta gamma delta epsilon zeta eta iota
    differentialJacobian d (depressedQuartic46 A B C0)
        (depressedDecic410 L P Q R S T U V W Z) =
      C (W * d A + 2 * V * d B + 3 * U * d C0 -
        2 * A * d W - B * d V) * X ^ 2 +
      C (W * d B + 2 * V * d C0 - 2 * A * d Z - B * d W) * X +
      C (W * d C0 - B * d Z) := by
  dsimp only
  rw [differentialJacobian_depressed410_eq d L
    (integratedP410 A alpha) (integratedQ410 L A B beta)
    (integratedR410 L A B C0 alpha gamma)
    (integratedS410 L A B C0 alpha beta delta)
    (integratedT410 L A B C0 alpha beta gamma epsilon)
    (integratedU410 L A B C0 alpha beta gamma delta zeta)
    (integratedV410 L A B C0 alpha beta gamma delta epsilon eta)
    (integratedW410 L A B C0 alpha beta gamma delta epsilon zeta theta)
    (integratedZ410 L A B C0 alpha beta gamma delta epsilon zeta eta iota)
    A B C0 hL]
  obtain ⟨h11, h10, h9, h8⟩ := integratedUpperFourRows410 d
    L A B C0 alpha beta gamma delta hL halpha hbeta hgamma hdelta
  have hn2 : d (2 : F) = 0 := d.map_natCast 2
  have hn16 : d (16 : F) = 0 := d.map_natCast 16
  have h12 : d (1 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, hn2]
  have h32 : d (3 / 2 : F) = 0 := derivation_natDiv_zero68 d 3 2
  have h52 : d (5 / 2 : F) = 0 := derivation_natDiv_zero68 d 5 2
  have h34 : d (3 / 4 : F) = 0 := derivation_natDiv_zero68 d 3 4
  have h54 : d (5 / 4 : F) = 0 := derivation_natDiv_zero68 d 5 4
  have h74 : d (7 / 4 : F) = 0 := derivation_natDiv_zero68 d 7 4
  have h94 : d (9 / 4 : F) = 0 := derivation_natDiv_zero68 d 9 4
  have h154 : d (15 / 4 : F) = 0 := derivation_natDiv_zero68 d 15 4
  have h38 : d (3 / 8 : F) = 0 := derivation_natDiv_zero68 d 3 8
  have h158 : d (15 / 8 : F) = 0 := derivation_natDiv_zero68 d 15 8
  have h116 : d (1 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, hn16]
  have h516 : d (5 / 16 : F) = 0 := derivation_natDiv_zero68 d 5 16
  have h1516 : d (15 / 16 : F) = 0 := derivation_natDiv_zero68 d 15 16
  have h2116 : d (21 / 16 : F) = 0 := derivation_natDiv_zero68 d 21 16
  have h4516 : d (45 / 16 : F) = 0 := derivation_natDiv_zero68 d 45 16
  have h532 : d (5 / 32 : F) = 0 := derivation_natDiv_zero68 d 5 32
  have h2132 : d (21 / 32 : F) = 0 := derivation_natDiv_zero68 d 21 32
  have h4532 : d (45 / 32 : F) = 0 := derivation_natDiv_zero68 d 45 32
  have h1564 : d (15 / 64 : F) = 0 := derivation_natDiv_zero68 d 15 64
  have h4564 : d (45 / 64 : F) = 0 := derivation_natDiv_zero68 d 45 64
  have h7128 : d (7 / 128 : F) = 0 := derivation_natDiv_zero68 d 7 128
  have h5128 : d (5 / 128 : F) = 0 := derivation_natDiv_zero68 d 5 128
  have h15128 : d (15 / 128 : F) = 0 := derivation_natDiv_zero68 d 15 128
  have h21128 : d (21 / 128 : F) = 0 := derivation_natDiv_zero68 d 21 128
  have h45128 : d (45 / 128 : F) = 0 := derivation_natDiv_zero68 d 45 128
  have h3256 : d (3 / 256 : F) = 0 := derivation_natDiv_zero68 d 3 256
  have h45512 : d (45 / 512 : F) = 0 := derivation_natDiv_zero68 d 45 512
  have h452048 : d (45 / 2048 : F) = 0 := derivation_natDiv_zero68 d 45 2048
  have hn5128 : d (-5 / 128 : F) = 0 := by
    have heq : (-5 / 128 : F) = -(5 / 128 : F) := by ring
    rw [heq, map_neg, h5128, neg_zero]
  have hn452048 : d (-45 / 2048 : F) = 0 := by
    have heq : (-45 / 2048 : F) = -(45 / 2048 : F) := by ring
    rw [heq, map_neg, h452048, neg_zero]
  have hn45512 : d (-45 / 512 : F) = 0 := by
    have heq : (-45 / 512 : F) = -(45 / 512 : F) := by ring
    rw [heq, map_neg, h45512, neg_zero]
  have hn532 : d (-5 / 32 : F) = 0 := by
    have heq : (-5 / 32 : F) = -(5 / 32 : F) := by ring
    rw [heq, map_neg, h532, neg_zero]
  have hn116 : d (-1 / 16 : F) = 0 := by
    have heq : (-1 / 16 : F) = -(1 / 16 : F) := by ring
    rw [heq, map_neg, h116, neg_zero]
  have hn1564 : d (-15 / 64 : F) = 0 := by
    have heq : (-15 / 64 : F) = -(15 / 64 : F) := by ring
    rw [heq, map_neg, h1564, neg_zero]
  have hn21128 : d (-21 / 128 : F) = 0 := by
    have heq : (-21 / 128 : F) = -(21 / 128 : F) := by ring
    rw [heq, map_neg, h21128, neg_zero]
  have hrows :
      (6 * integratedR410 L A B C0 alpha gamma * d A +
          7 * integratedQ410 L A B beta * d B +
          8 * integratedP410 A alpha * d C0 -
          2 * A * d (integratedR410 L A B C0 alpha gamma) -
          B * d (integratedQ410 L A B beta) -
          4 * d (integratedT410 L A B C0 alpha beta gamma epsilon) = 0) ∧
      (5 * integratedS410 L A B C0 alpha beta delta * d A +
          6 * integratedR410 L A B C0 alpha gamma * d B +
          7 * integratedQ410 L A B beta * d C0 -
          2 * A * d (integratedS410 L A B C0 alpha beta delta) -
          B * d (integratedR410 L A B C0 alpha gamma) -
          4 * d (integratedU410 L A B C0 alpha beta gamma delta zeta) = 0) ∧
      (4 * integratedT410 L A B C0 alpha beta gamma epsilon * d A +
          5 * integratedS410 L A B C0 alpha beta delta * d B +
          6 * integratedR410 L A B C0 alpha gamma * d C0 -
          2 * A * d (integratedT410 L A B C0 alpha beta gamma epsilon) -
          B * d (integratedS410 L A B C0 alpha beta delta) -
          4 * d (integratedV410 L A B C0 alpha beta gamma delta epsilon eta) = 0) ∧
      (3 * integratedU410 L A B C0 alpha beta gamma delta zeta * d A +
          4 * integratedT410 L A B C0 alpha beta gamma epsilon * d B +
          5 * integratedS410 L A B C0 alpha beta delta * d C0 -
          2 * A * d (integratedU410 L A B C0 alpha beta gamma delta zeta) -
          B * d (integratedT410 L A B C0 alpha beta gamma epsilon) -
          4 * d (integratedW410 L A B C0 alpha beta gamma delta epsilon zeta theta) = 0) ∧
      (2 * integratedV410 L A B C0 alpha beta gamma delta epsilon eta * d A +
          3 * integratedU410 L A B C0 alpha beta gamma delta zeta * d B +
          4 * integratedT410 L A B C0 alpha beta gamma epsilon * d C0 -
          2 * A * d (integratedV410 L A B C0 alpha beta gamma delta epsilon eta) -
          B * d (integratedU410 L A B C0 alpha beta gamma delta zeta) -
          4 * d (integratedZ410 L A B C0 alpha beta gamma delta epsilon zeta eta iota) = 0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [integratedP410, integratedQ410, integratedR410,
        integratedS410, integratedT410, integratedU410, integratedV410,
        integratedW410, integratedZ410, map_add, map_sub, map_neg,
        Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul,
        smul_eq_mul, hn2, hn16, h12, h32, h52, h34, h54, h74, h94, h154,
        h38, h158, h116, h516, h1516, h2116, h4516, h532, h2132,
        h4532, h1564, h4564, h7128, h5128, h15128, h21128, h45128, h3256,
        h45512, h452048, hn5128, hn452048, hn45512, hn532, hn116, hn1564,
        hn21128,
        hL, halpha, hbeta, hgamma, hdelta, hepsilon, hzeta, heta,
        htheta, hiota, mul_zero, zero_mul, add_zero, zero_add] <;>
      norm_num <;>
      ring
  rcases hrows with ⟨h7, h6, h5, h4, h3⟩
  rw [h11, h10, h9, h8, h7, h6, h5, h4, h3]
  simp only [Polynomial.C_0, zero_mul, zero_add]

end IntegratedUpperRows410

end DifferentialNormalForm410

end Max11DegreeRoutes
