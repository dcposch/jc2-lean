import LowScale46Rows

/-! # Differential normal form for the genuine `(4,6)` leaf

This module records the common depressed quartic/sextic normal form over an
arbitrary differential field extension and expands its Jacobian exactly.
The formulation is deliberately independent of how the quadratic working
field is constructed, so it applies to both the aligned and mismatch
branches of the imprimitive discriminator.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section DifferentialNormalForm

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Apply a derivation coefficientwise while retaining the normal-form
variable. -/
def coefficientDeriv (d : Derivation k F F) (p : F[X]) : F[X] :=
  PolynomialModule.equivPolynomialSelf (d.mapCoeffs p)

@[simp]
theorem coeff_coefficientDeriv (d : Derivation k F F) (p : F[X]) (n : ℕ) :
    (coefficientDeriv d p).coeff n = d (p.coeff n) := by
  rfl

/-- The Jacobian in the independent depressed variable `z`. -/
def differentialJacobian (d : Derivation k F F) (f g : F[X]) : F[X] :=
  coefficientDeriv d f * g.derivative - f.derivative * coefficientDeriv d g

/-- Monic depressed quartic coordinate. -/
def depressedQuartic46 (A B C0 : F) : F[X] :=
  X ^ 4 + Polynomial.C A * X ^ 2 + Polynomial.C B * X + Polynomial.C C0

/-- Monic sextic coordinate with constant quintic coefficient. -/
def depressedSextic46 (L P Q R S T : F) : F[X] :=
  X ^ 6 + C L * X ^ 5 + C P * X ^ 4 + C Q * X ^ 3 +
    C R * X ^ 2 + C S * X + C T

theorem coefficientDeriv_depressedQuartic46 (d : Derivation k F F)
    (A B C0 : F) :
    coefficientDeriv d (depressedQuartic46 A B C0) =
      Polynomial.C (d A) * X ^ 2 + Polynomial.C (d B) * X +
        Polynomial.C (d C0) := by
  ext n
  simp [depressedQuartic46, Polynomial.coeff_X, Polynomial.coeff_C]
  split_ifs <;> simp_all

theorem coefficientDeriv_depressedSextic46 (d : Derivation k F F)
    (L P Q R S T : F) (hL : d L = 0) :
    coefficientDeriv d (depressedSextic46 L P Q R S T) =
      Polynomial.C (d P) * X ^ 4 + Polynomial.C (d Q) * X ^ 3 +
        Polynomial.C (d R) * X ^ 2 + Polynomial.C (d S) * X +
          Polynomial.C (d T) := by
  ext n
  simp [depressedSextic46, hL, Polynomial.coeff_X, Polynomial.coeff_C]
  split_ifs <;> simp_all

/-- The eight exact coefficient rows of the depressed `(4,6)` Jacobian,
ordered from `z⁷` down to the constant row. -/
theorem differentialJacobian_depressed46_eq (d : Derivation k F F)
    (L P Q R S T A B C0 : F) (hL : d L = 0) :
    differentialJacobian d (depressedQuartic46 A B C0)
        (depressedSextic46 L P Q R S T) =
      Polynomial.C (6 * d A - 4 * d P) * X ^ 7 +
      Polynomial.C (5 * L * d A + 6 * d B - 4 * d Q) * X ^ 6 +
      Polynomial.C
        (-2 * A * d P + 5 * L * d B + 4 * P * d A + 6 * d C0 - 4 * d R) *
          X ^ 5 +
      Polynomial.C
        (-2 * A * d Q - B * d P + 5 * L * d C0 + 4 * P * d B +
          3 * Q * d A - 4 * d S) * X ^ 4 +
      Polynomial.C
        (-2 * A * d R - B * d Q + 4 * P * d C0 + 3 * Q * d B +
          2 * R * d A - 4 * d T) * X ^ 3 +
      Polynomial.C
        (-2 * A * d S - B * d R + 3 * Q * d C0 + 2 * R * d B + S * d A) *
          X ^ 2 +
      Polynomial.C
        (-2 * A * d T - B * d S + 2 * R * d C0 + S * d B) * X +
      Polynomial.C (-B * d T + S * d C0) := by
  rw [differentialJacobian, coefficientDeriv_depressedQuartic46,
    coefficientDeriv_depressedSextic46 d L P Q R S T hL]
  simp only [depressedQuartic46, depressedSextic46,
    Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_X,
    Polynomial.derivative_C, Polynomial.C_0, zero_mul, zero_add,
    one_mul, mul_one]
  push_cast
  simp only [map_add, map_sub, map_mul, map_neg, map_natCast]
  ring

section IntegratedRows

variable [CharZero F]

/-- First integrated sextic coefficient. -/
def integratedP46 (A alpha : F) : F := (3 / 2 : F) * A + alpha

/-- Second integrated sextic coefficient. -/
def integratedQ46 (L A B beta : F) : F :=
  (5 / 4 : F) * L * A + (3 / 2 : F) * B + beta

/-- Third integrated sextic coefficient. -/
def integratedR46 (L A B C0 alpha gamma : F) : F :=
  (3 / 8 : F) * A ^ 2 + alpha * A + (5 / 4 : F) * L * B +
    (3 / 2 : F) * C0 + gamma

/-- Fourth integrated sextic coefficient. -/
def integratedS46 (L A B C0 alpha beta delta : F) : F :=
  (5 / 32 : F) * L * A ^ 2 + (3 / 4 : F) * A * B +
    (3 / 4 : F) * beta * A + alpha * B + (5 / 4 : F) * L * C0 + delta

/-- Fifth integrated sextic coefficient. -/
def integratedT46 (L A B C0 alpha beta gamma epsilon : F) : F :=
  (-1 / 16 : F) * A ^ 3 + (5 / 16 : F) * L * A * B +
    (3 / 4 : F) * A * C0 + (1 / 2 : F) * gamma * A +
    (3 / 8 : F) * B ^ 2 + (3 / 4 : F) * beta * B + alpha * C0 + epsilon

/-- The first integral whose derivative is the `z²` Jacobian row. -/
def firstIntegralTwo46 (L A B C0 beta gamma delta : F) : F :=
  (-5 / 32 : F) * L * A ^ 3 - (3 / 4 : F) * A ^ 2 * B +
    (5 / 4 : F) * L * A * C0 - (3 / 8 : F) * beta * A ^ 2 +
    delta * A + (5 / 8 : F) * L * B ^ 2 + 3 * B * C0 +
    2 * gamma * B + 3 * beta * C0

/-- The first integral whose derivative is the `z` Jacobian row. -/
def firstIntegralOne46 (L A B C0 beta gamma delta : F) : F :=
  (3 / 32 : F) * A ^ 4 - (15 / 32 : F) * L * A ^ 2 * B -
    (3 / 4 : F) * A * B ^ 2 - (3 / 4 : F) * A ^ 2 * C0 -
    (3 / 4 : F) * beta * A * B - (1 / 2 : F) * gamma * A ^ 2 +
    (5 / 4 : F) * L * B * C0 + delta * B + (3 / 2 : F) * C0 ^ 2 +
    2 * gamma * C0

/-- After the five upper rows are integrated, the full Jacobian has only
three rows left: the derivatives of the two displayed first integrals and
the literal last row.  This is valid in every characteristic-zero
differential field extension. -/
theorem differentialJacobian_integrated46_eq (d : Derivation k F F)
    (L A B C0 alpha beta gamma delta epsilon : F)
    (hL : d L = 0) (halpha : d alpha = 0) (hbeta : d beta = 0)
    (hgamma : d gamma = 0) (hdelta : d delta = 0)
    (hepsilon : d epsilon = 0) :
    let P := integratedP46 A alpha
    let Q := integratedQ46 L A B beta
    let R := integratedR46 L A B C0 alpha gamma
    let S := integratedS46 L A B C0 alpha beta delta
    let T := integratedT46 L A B C0 alpha beta gamma epsilon
    differentialJacobian d (depressedQuartic46 A B C0)
        (depressedSextic46 L P Q R S T) =
      Polynomial.C (d (firstIntegralTwo46 L A B C0 beta gamma delta)) * X ^ 2 +
      Polynomial.C (d (firstIntegralOne46 L A B C0 beta gamma delta)) * X +
      Polynomial.C (-B * d T + S * d C0) := by
  dsimp only
  rw [differentialJacobian_depressed46_eq d L
    (integratedP46 A alpha) (integratedQ46 L A B beta)
    (integratedR46 L A B C0 alpha gamma)
    (integratedS46 L A B C0 alpha beta delta)
    (integratedT46 L A B C0 alpha beta gamma epsilon) A B C0 hL]
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h3 : d (3 : F) = 0 := d.map_natCast 3
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h15 : d (15 : F) = 0 := d.map_natCast 15
  have h16 : d (16 : F) = 0 := d.map_natCast 16
  have h32n : d (32 : F) = 0 := d.map_natCast 32
  have h12 : d (1 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h2]
  have h32 : d (3 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h2, h3]
  have h34 : d (3 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h3, h4]
  have h54 : d (5 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h4, h5]
  have h38 : d (3 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h3, h8]
  have h58 : d (5 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h5, h8]
  have h116 : d (1 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h16]
  have h516 : d (5 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h5, h16]
  have h332 : d (3 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h3, h32n]
  have h532 : d (5 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h5, h32n]
  have h1532 : d (15 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h15, h32n]
  have hrows :
      (6 * d A - 4 * d (integratedP46 A alpha) = 0) ∧
      (5 * L * d A + 6 * d B - 4 * d (integratedQ46 L A B beta) = 0) ∧
      (-2 * A * d (integratedP46 A alpha) + 5 * L * d B +
          4 * integratedP46 A alpha * d A + 6 * d C0 -
          4 * d (integratedR46 L A B C0 alpha gamma) = 0) ∧
      (-2 * A * d (integratedQ46 L A B beta) -
          B * d (integratedP46 A alpha) + 5 * L * d C0 +
          4 * integratedP46 A alpha * d B +
          3 * integratedQ46 L A B beta * d A -
          4 * d (integratedS46 L A B C0 alpha beta delta) = 0) ∧
      (-2 * A * d (integratedR46 L A B C0 alpha gamma) -
          B * d (integratedQ46 L A B beta) +
          4 * integratedP46 A alpha * d C0 +
          3 * integratedQ46 L A B beta * d B +
          2 * integratedR46 L A B C0 alpha gamma * d A -
          4 * d (integratedT46 L A B C0 alpha beta gamma epsilon) = 0) ∧
      (-2 * A * d (integratedS46 L A B C0 alpha beta delta) -
          B * d (integratedR46 L A B C0 alpha gamma) +
          3 * integratedQ46 L A B beta * d C0 +
          2 * integratedR46 L A B C0 alpha gamma * d B +
          integratedS46 L A B C0 alpha beta delta * d A =
        d (firstIntegralTwo46 L A B C0 beta gamma delta)) ∧
      (-2 * A * d (integratedT46 L A B C0 alpha beta gamma epsilon) -
          B * d (integratedS46 L A B C0 alpha beta delta) +
          2 * integratedR46 L A B C0 alpha gamma * d C0 +
          integratedS46 L A B C0 alpha beta delta * d B =
        d (firstIntegralOne46 L A B C0 beta gamma delta)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [integratedP46, integratedQ46, integratedR46,
        integratedS46, integratedT46, firstIntegralTwo46,
        firstIntegralOne46, map_add, map_sub, map_neg,
        Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul,
        smul_eq_mul, h12, h32, h34, h54, h38, h58, h116, h516,
        h332, h532, h1532, hL, halpha, hbeta, hgamma, hdelta,
        hepsilon, mul_zero, zero_mul, add_zero, zero_add] <;>
      norm_num <;>
      (try simp only [h12, h32, h34, h54, h38, h58, h116, h516,
        h332, h532, h1532, h2, h3, h4, h5, h8, h15, h16, h32n,
        map_zero, mul_zero, zero_mul, add_zero, zero_add]) <;>
      ring
  rcases hrows with ⟨h7, h6, h5row, h4row, h3row, h2row, h1row⟩
  rw [h7, h6, h5row, h4row, h3row, h2row, h1row]
  simp only [Polynomial.C_0, zero_mul, zero_add]

end IntegratedRows

end DifferentialNormalForm

end Max11DegreeRoutes
