import LowScale46NormalForm

/-! # Differential normal form for the normalized `(6,8)` leaf

After adjoining a square root of the common leading core and applying the
common affine depression, the normalized `(6,8)` source becomes a monic
depressed sextic and a monic octic.  This module records those two shapes and
expands their differential Jacobian into its twelve exact coefficient rows.

The construction is independent of the eventual square/nonsquare source
bridge.  It works over every characteristic-zero differential field and is
therefore shared by the scale-zero and scale-two branches.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section DifferentialNormalForm68

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Monic sextic with its quintic coefficient depressed to zero. -/
def depressedSextic68 (A B C0 D E : F) : F[X] :=
  X ^ 6 + C A * X ^ 4 + C B * X ^ 3 + C C0 * X ^ 2 + C D * X + C E

/-- Monic octic whose septic coefficient is a differential constant. -/
def depressedOctic68 (L P Q R S T U V : F) : F[X] :=
  X ^ 8 + C L * X ^ 7 + C P * X ^ 6 + C Q * X ^ 5 +
    C R * X ^ 4 + C S * X ^ 3 + C T * X ^ 2 + C U * X + C V

theorem coefficientDeriv_depressedSextic68 (d : Derivation k F F)
    (A B C0 D E : F) :
    coefficientDeriv d (depressedSextic68 A B C0 D E) =
      C (d A) * X ^ 4 + C (d B) * X ^ 3 + C (d C0) * X ^ 2 +
        C (d D) * X + C (d E) := by
  ext n
  simp [depressedSextic68, Polynomial.coeff_X, Polynomial.coeff_C]
  split_ifs <;> simp_all

theorem coefficientDeriv_depressedOctic68 (d : Derivation k F F)
    (L P Q R S T U V : F) (hL : d L = 0) :
    coefficientDeriv d (depressedOctic68 L P Q R S T U V) =
      C (d P) * X ^ 6 + C (d Q) * X ^ 5 + C (d R) * X ^ 4 +
        C (d S) * X ^ 3 + C (d T) * X ^ 2 + C (d U) * X + C (d V) := by
  ext n
  simp [depressedOctic68, hL, Polynomial.coeff_X, Polynomial.coeff_C]
  split_ifs <;> simp_all

/-- The full coefficientwise derivative before the septic coefficient has
been shown constant. -/
theorem coefficientDeriv_depressedOctic68_full (d : Derivation k F F)
    (L P Q R S T U V : F) :
    coefficientDeriv d (depressedOctic68 L P Q R S T U V) =
      C (d L) * X ^ 7 + C (d P) * X ^ 6 + C (d Q) * X ^ 5 +
        C (d R) * X ^ 4 + C (d S) * X ^ 3 + C (d T) * X ^ 2 +
        C (d U) * X + C (d V) := by
  ext n
  simp [depressedOctic68, Polynomial.coeff_X, Polynomial.coeff_C]
  split_ifs <;> simp_all

/-- Constancy of the whole depressed bracket forces its septic coefficient
to be a differential constant.  This is the omitted top row (`z^12`) of the
twelve-row system below. -/
theorem depressedL_deriv_zero68 [CharZero F] (d : Derivation k F F)
    (L P Q R S T U V A B C0 D E terminal : F)
    (hbracket : differentialJacobian d (depressedSextic68 A B C0 D E)
        (depressedOctic68 L P Q R S T U V) = C terminal) :
    d L = 0 := by
  have h12 := congrArg (fun f : F[X] => f.coeff 12) hbracket
  rw [differentialJacobian, coefficientDeriv_depressedSextic68,
    coefficientDeriv_depressedOctic68_full] at h12
  simp only [Polynomial.coeff_sub, Polynomial.coeff_mul, coeff_C,
    show (12 : ℕ) ≠ 0 by norm_num, if_false] at h12
  have hanti : (Finset.HasAntidiagonal.antidiagonal 12 : Finset (ℕ × ℕ)) =
      ({(0, 12), (1, 11), (2, 10), (3, 9), (4, 8), (5, 7), (6, 6),
        (7, 5), (8, 4), (9, 3), (10, 2), (11, 1), (12, 0)} :
        Finset (ℕ × ℕ)) := by decide
  rw [hanti] at h12
  norm_num [depressedSextic68, depressedOctic68,
    Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_X,
    Polynomial.derivative_C, coeff_add, coeff_C, coeff_C_mul,
    coeff_mul_X_pow', coeff_X, coeff_X_pow] at h12
  exact h12

/-- The twelve exact coefficient rows of the depressed `(6,8)` differential
Jacobian, from `z^11` down to its constant coefficient. -/
theorem differentialJacobian_depressed68_eq (d : Derivation k F F)
    (L P Q R S T U V A B C0 D E : F) (hL : d L = 0) :
    differentialJacobian d (depressedSextic68 A B C0 D E)
        (depressedOctic68 L P Q R S T U V) =
      C (8 * d A - 6 * d P) * X ^ 11 +
      C (7 * L * d A + 8 * d B - 6 * d Q) * X ^ 10 +
      C (6 * P * d A + 7 * L * d B + 8 * d C0 -
        4 * A * d P - 6 * d R) * X ^ 9 +
      C (5 * Q * d A + 6 * P * d B + 7 * L * d C0 + 8 * d D -
        4 * A * d Q - 3 * B * d P - 6 * d S) * X ^ 8 +
      C (4 * R * d A + 5 * Q * d B + 6 * P * d C0 + 7 * L * d D +
        8 * d E - 4 * A * d R - 3 * B * d Q - 2 * C0 * d P -
        6 * d T) * X ^ 7 +
      C (3 * S * d A + 4 * R * d B + 5 * Q * d C0 + 6 * P * d D +
        7 * L * d E - 4 * A * d S - 3 * B * d R - 2 * C0 * d Q -
        D * d P - 6 * d U) * X ^ 6 +
      C (2 * T * d A + 3 * S * d B + 4 * R * d C0 + 5 * Q * d D +
        6 * P * d E - 4 * A * d T - 3 * B * d S - 2 * C0 * d R -
        D * d Q - 6 * d V) * X ^ 5 +
      C (U * d A + 2 * T * d B + 3 * S * d C0 + 4 * R * d D +
        5 * Q * d E - 4 * A * d U - 3 * B * d T - 2 * C0 * d S -
        D * d R) * X ^ 4 +
      C (U * d B + 2 * T * d C0 + 3 * S * d D + 4 * R * d E -
        4 * A * d V - 3 * B * d U - 2 * C0 * d T - D * d S) * X ^ 3 +
      C (U * d C0 + 2 * T * d D + 3 * S * d E - 3 * B * d V -
        2 * C0 * d U - D * d T) * X ^ 2 +
      C (U * d D + 2 * T * d E - 2 * C0 * d V - D * d U) * X +
      C (U * d E - D * d V) := by
  rw [differentialJacobian, coefficientDeriv_depressedSextic68,
    coefficientDeriv_depressedOctic68 d L P Q R S T U V hL]
  simp only [depressedSextic68, depressedOctic68,
    Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_X,
    Polynomial.derivative_C, Polynomial.C_0, zero_mul, zero_add,
    one_mul, mul_one]
  push_cast
  simp only [map_add, map_sub, map_mul, map_neg, map_natCast]
  ring

section IntegratedUpperRows68

variable [CharZero F]

/-- A derivation over the ground field kills every rational scalar. -/
theorem derivation_ratCast_zero68 (d : Derivation k F F) (q : ℚ) :
    d (q : F) = 0 := by
  rw [← map_ratCast (algebraMap k F) q, d.map_algebraMap]

/-- The surface syntax `(m / n : F)` elaborates as a quotient of natural
casts, rather than as a rational cast.  This companion lemma is therefore
the form used by the residual computations below. -/
theorem derivation_natDiv_zero68 (d : Derivation k F F) (m n : ℕ) :
    d ((m : F) / (n : F)) = 0 := by
  simp [Derivation.leibniz_div, Derivation.leibniz_inv]

/-- A derivation kills literal natural numerals.  Unlike `map_natCast`, this
form matches `OfNat` syntax and is useful in a second simplifier pass after
quotient differentiation has exposed numerator and denominator derivatives. -/
theorem derivation_ofNat_zero68 (d : Derivation k F F) (n : ℕ)
    [n.AtLeastTwo] : d (OfNat.ofNat n : F) = 0 := by
  rw [← Nat.cast_ofNat]
  exact d.map_natCast (OfNat.ofNat n)

/-- The seven integration residuals in the octic Faber expansion.  Their
successive definitions are triangular: each new octic coefficient is
compared with the polynomial part of `f^(8/6)` and the preceding constant
Faber directions `f^(m/6)`, `m = 6,5,...,2`. -/
def alphaResidual68 (A P : F) : F :=
  P - (4 / 3 : F) * A

def betaResidual68 (L A B Q : F) : F :=
  Q - (4 / 3 : F) * B - (7 / 6 : F) * L * A

def gammaResidual68 (L A B C0 P R : F) : F :=
  R - ((4 / 3 : F) * C0 + (2 / 9 : F) * A ^ 2 +
    (7 / 6 : F) * L * B + alphaResidual68 A P * A)

def deltaResidual68 (L A B C0 D P Q S : F) : F :=
  S - ((4 / 3 : F) * D + (4 / 9 : F) * A * B +
    L * ((7 / 6 : F) * C0 + (7 / 72 : F) * A ^ 2) +
    alphaResidual68 A P * B +
    (5 / 6 : F) * betaResidual68 L A B Q * A)

def epsilonResidual68 (L A B C0 D E P Q R T : F) : F :=
  T - ((4 / 3 : F) * E + (2 / 9 : F) * B ^ 2 +
    (4 / 9 : F) * A * C0 - (4 / 81 : F) * A ^ 3 +
    L * ((7 / 6 : F) * D + (7 / 36 : F) * A * B) +
    alphaResidual68 A P * C0 +
    (5 / 6 : F) * betaResidual68 L A B Q * B +
    (2 / 3 : F) * gammaResidual68 L A B C0 P R * A)

def zetaResidual68 (L A B C0 D E P Q R S U : F) : F :=
  U - ((4 / 9 : F) * B * C0 + (4 / 9 : F) * A * D -
    (4 / 27 : F) * A ^ 2 * B +
    L * ((7 / 6 : F) * E + (7 / 72 : F) * B ^ 2 +
      (7 / 36 : F) * A * C0 - (35 / 1296 : F) * A ^ 3) +
    alphaResidual68 A P * D +
    betaResidual68 L A B Q * ((5 / 6 : F) * C0 - (5 / 72 : F) * A ^ 2) +
    (2 / 3 : F) * gammaResidual68 L A B C0 P R * B +
    (1 / 2 : F) * deltaResidual68 L A B C0 D P Q S * A)

def etaResidual68 (L A B C0 D E P Q R S T V : F) : F :=
  V - ((2 / 9 : F) * C0 ^ 2 + (4 / 9 : F) * B * D +
    (4 / 9 : F) * A * E - (4 / 27 : F) * A * B ^ 2 -
    (4 / 27 : F) * A ^ 2 * C0 + (5 / 243 : F) * A ^ 4 +
    L * ((7 / 36 : F) * B * C0 + (7 / 36 : F) * A * D -
      (35 / 432 : F) * A ^ 2 * B) +
    alphaResidual68 A P * E +
    betaResidual68 L A B Q * ((5 / 6 : F) * D - (5 / 36 : F) * A * B) +
    gammaResidual68 L A B C0 P R *
      ((2 / 3 : F) * C0 - (1 / 9 : F) * A ^ 2) +
    (1 / 2 : F) * deltaResidual68 L A B C0 D P Q S * B +
    (1 / 3 : F) * epsilonResidual68 L A B C0 D E P Q R T * A)

set_option maxHeartbeats 1000000 in
/-- The upper seven coefficients of a constant depressed bracket vanish.
These are precisely the rows that solve successively for `P,...,V`. -/
theorem depressedUpperRows68
    (d : Derivation k F F)
    (L P Q R S T U V A B C0 D E terminal : F) (hL : d L = 0)
    (hbracket : differentialJacobian d (depressedSextic68 A B C0 D E)
        (depressedOctic68 L P Q R S T U V) = C terminal) :
    (8 * d A - 6 * d P = 0) ∧
    (7 * L * d A + 8 * d B - 6 * d Q = 0) ∧
    (6 * P * d A + 7 * L * d B + 8 * d C0 -
      4 * A * d P - 6 * d R = 0) ∧
    (5 * Q * d A + 6 * P * d B + 7 * L * d C0 + 8 * d D -
      4 * A * d Q - 3 * B * d P - 6 * d S = 0) ∧
    (4 * R * d A + 5 * Q * d B + 6 * P * d C0 + 7 * L * d D +
      8 * d E - 4 * A * d R - 3 * B * d Q - 2 * C0 * d P -
      6 * d T = 0) ∧
    (3 * S * d A + 4 * R * d B + 5 * Q * d C0 + 6 * P * d D +
      7 * L * d E - 4 * A * d S - 3 * B * d R - 2 * C0 * d Q -
      D * d P - 6 * d U = 0) ∧
    (2 * T * d A + 3 * S * d B + 4 * R * d C0 + 5 * Q * d D +
      6 * P * d E - 4 * A * d T - 3 * B * d S - 2 * C0 * d R -
      D * d Q - 6 * d V = 0) := by
  have hfull := hbracket
  rw [differentialJacobian_depressed68_eq d L P Q R S T U V
    A B C0 D E hL] at hfull
  have h11 := congrArg (fun f : F[X] => f.coeff 11) hfull
  have h10 := congrArg (fun f : F[X] => f.coeff 10) hfull
  have h9 := congrArg (fun f : F[X] => f.coeff 9) hfull
  have h8 := congrArg (fun f : F[X] => f.coeff 8) hfull
  have h7 := congrArg (fun f : F[X] => f.coeff 7) hfull
  have h6 := congrArg (fun f : F[X] => f.coeff 6) hfull
  have h5 := congrArg (fun f : F[X] => f.coeff 5) hfull
  norm_num [coeff_add, coeff_C, coeff_C_mul, coeff_mul_X_pow',
    coeff_X, coeff_X_pow] at h11 h10 h9 h8 h7 h6 h5
  exact ⟨h11, h10, h9, h8, h7, h6, h5⟩

set_option maxHeartbeats 1000000 in
/-- The five surviving rows of a constant depressed `(6,8)` bracket.  The
first four vanish and the last one is the prescribed bracket constant. -/
theorem depressedLowerRows68
    (d : Derivation k F F)
    (L P Q R S T U V A B C0 D E terminal : F) (hL : d L = 0)
    (hbracket : differentialJacobian d (depressedSextic68 A B C0 D E)
        (depressedOctic68 L P Q R S T U V) = C terminal) :
    (U * d A + 2 * T * d B + 3 * S * d C0 + 4 * R * d D +
      5 * Q * d E - 4 * A * d U - 3 * B * d T - 2 * C0 * d S -
      D * d R = 0) ∧
    (U * d B + 2 * T * d C0 + 3 * S * d D + 4 * R * d E -
      4 * A * d V - 3 * B * d U - 2 * C0 * d T - D * d S = 0) ∧
    (U * d C0 + 2 * T * d D + 3 * S * d E - 3 * B * d V -
      2 * C0 * d U - D * d T = 0) ∧
    (U * d D + 2 * T * d E - 2 * C0 * d V - D * d U = 0) ∧
    (U * d E - D * d V = terminal) := by
  have hfull := hbracket
  rw [differentialJacobian_depressed68_eq d L P Q R S T U V
    A B C0 D E hL] at hfull
  have h4 := congrArg (fun f : F[X] => f.coeff 4) hfull
  have h3 := congrArg (fun f : F[X] => f.coeff 3) hfull
  have h2 := congrArg (fun f : F[X] => f.coeff 2) hfull
  have h1 := congrArg (fun f : F[X] => f.coeff 1) hfull
  have h0 := congrArg (fun f : F[X] => f.coeff 0) hfull
  norm_num [coeff_add, coeff_C, coeff_C_mul, coeff_mul_X_pow',
    coeff_X, coeff_X_pow] at h4 h3 h2 h1 h0
  exact ⟨h4, h3, h2, h1, h0⟩

set_option maxHeartbeats 2000000 in
/-- All seven Faber residuals supplied by the upper octic rows are
differential constants.  This is the exact `(6,8)` analogue of the five
integrated upper rows in the `(4,6)` normal form. -/
theorem depressedUpperResiduals_deriv_zero68
    (d : Derivation k F F)
    (L P Q R S T U V A B C0 D E terminal : F) (hL : d L = 0)
    (hbracket : differentialJacobian d (depressedSextic68 A B C0 D E)
        (depressedOctic68 L P Q R S T U V) = C terminal) :
    d (alphaResidual68 A P) = 0 ∧
    d (betaResidual68 L A B Q) = 0 ∧
    d (gammaResidual68 L A B C0 P R) = 0 ∧
    d (deltaResidual68 L A B C0 D P Q S) = 0 ∧
    d (epsilonResidual68 L A B C0 D E P Q R T) = 0 ∧
    d (zetaResidual68 L A B C0 D E P Q R S U) = 0 ∧
    d (etaResidual68 L A B C0 D E P Q R S T V) = 0 := by
  rcases depressedUpperRows68 d L P Q R S T U V A B C0 D E terminal hL
      hbracket with ⟨h11, h10, h9, h8, h7, h6, h5⟩
  have hc1 : d (1 : F) = 0 := by simpa only [Nat.cast_one] using d.map_natCast 1
  have hc2 : d (2 : F) = 0 := d.map_natCast 2
  have hc3 : d (3 : F) = 0 := d.map_natCast 3
  have hc4 : d (4 : F) = 0 := d.map_natCast 4
  have hc5 : d (5 : F) = 0 := d.map_natCast 5
  have hc6 : d (6 : F) = 0 := d.map_natCast 6
  have hc7 : d (7 : F) = 0 := d.map_natCast 7
  have hc9 : d (9 : F) = 0 := d.map_natCast 9
  have hc27 : d (27 : F) = 0 := d.map_natCast 27
  have hc35 : d (35 : F) = 0 := d.map_natCast 35
  have hc36 : d (36 : F) = 0 := d.map_natCast 36
  have hc72 : d (72 : F) = 0 := d.map_natCast 72
  have hc81 : d (81 : F) = 0 := d.map_natCast 81
  have hc243 : d (243 : F) = 0 := d.map_natCast 243
  have hc432 : d (432 : F) = 0 := d.map_natCast 432
  have hc1296 : d (1296 : F) = 0 := d.map_natCast 1296
  have hc12 : d (1 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, hc1, hc2]
  have hc13 : d (1 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, hc1, hc3]
  have hc19 : d (1 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, hc1, hc9]
  have hcInv2 : d ((2 : F)⁻¹) = 0 := by
    simp [Derivation.leibniz_inv, hc2]
  have hcInv3 : d ((3 : F)⁻¹) = 0 := by
    simp [Derivation.leibniz_inv, hc3]
  have hcInv9 : d ((9 : F)⁻¹) = 0 := by
    simp [Derivation.leibniz_inv, hc9]
  have hPderiv : d P = (4 / 3 : F) * d A := by
    linear_combination (-1 / 6 : F) * h11
  have hQderiv : d Q = (7 / 6 : F) * L * d A + (4 / 3 : F) * d B := by
    linear_combination (-1 / 6 : F) * h10
  have hRderiv : d R = P * d A + (7 / 6 : F) * L * d B +
      (4 / 3 : F) * d C0 - (2 / 3 : F) * A * d P := by
    linear_combination (-1 / 6 : F) * h9
  have hSderiv : d S = (5 / 6 : F) * Q * d A + P * d B +
      (7 / 6 : F) * L * d C0 + (4 / 3 : F) * d D -
      (2 / 3 : F) * A * d Q - (1 / 2 : F) * B * d P := by
    linear_combination (-1 / 6 : F) * h8
  have hTderiv : d T = (2 / 3 : F) * R * d A + (5 / 6 : F) * Q * d B +
      P * d C0 + (7 / 6 : F) * L * d D + (4 / 3 : F) * d E -
      (2 / 3 : F) * A * d R - (1 / 2 : F) * B * d Q -
      (1 / 3 : F) * C0 * d P := by
    linear_combination (-1 / 6 : F) * h7
  have hUderiv : d U = (1 / 2 : F) * S * d A + (2 / 3 : F) * R * d B +
      (5 / 6 : F) * Q * d C0 + P * d D + (7 / 6 : F) * L * d E -
      (2 / 3 : F) * A * d S - (1 / 2 : F) * B * d R -
      (1 / 3 : F) * C0 * d Q - (1 / 6 : F) * D * d P := by
    linear_combination (-1 / 6 : F) * h6
  have hVderiv : d V = (1 / 3 : F) * T * d A + (1 / 2 : F) * S * d B +
      (2 / 3 : F) * R * d C0 + (5 / 6 : F) * Q * d D + P * d E -
      (2 / 3 : F) * A * d T - (1 / 2 : F) * B * d S -
      (1 / 3 : F) * C0 * d R - (1 / 6 : F) * D * d Q := by
    linear_combination (-1 / 6 : F) * h5
  have halpha : d (alphaResidual68 A P) = 0 := by
    simp only [alphaResidual68, map_sub, Derivation.leibniz,
      derivation_natDiv_zero68, smul_eq_mul, zero_mul, add_zero]
    rw [hPderiv]
    simp [Derivation.leibniz_div, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
      hc9, hc27, hc35, hc36, hc72, hc81, hc243, hc432, hc1296,
      hc12, hc13, hc19] <;> ring
  have hbeta : d (betaResidual68 L A B Q) = 0 := by
    simp only [betaResidual68, map_sub, Derivation.leibniz,
      derivation_natDiv_zero68, hL, smul_eq_mul, zero_mul, add_zero,
      mul_zero, zero_add]
    rw [hQderiv]
    simp [Derivation.leibniz_div, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
      hc9, hc27, hc35, hc36, hc72, hc81, hc243, hc432, hc1296,
      hc12, hc13, hc19] <;> ring
  have hgamma : d (gammaResidual68 L A B C0 P R) = 0 := by
    simp only [gammaResidual68, map_sub, map_add, Derivation.leibniz,
      Derivation.leibniz_pow, derivation_natDiv_zero68, hL, halpha,
      nsmul_eq_mul, smul_eq_mul, zero_mul, add_zero, mul_zero, zero_add]
    rw [hRderiv, hPderiv]
    simp only [alphaResidual68]
    simp [Derivation.leibniz_div, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
      hc9, hc27, hc35, hc36, hc72, hc81, hc243, hc432, hc1296,
      hc12, hc13] <;> ring
  have hdelta : d (deltaResidual68 L A B C0 D P Q S) = 0 := by
    simp only [deltaResidual68, map_sub, map_add, Derivation.leibniz,
      Derivation.leibniz_pow, derivation_natDiv_zero68, hL, halpha, hbeta,
      nsmul_eq_mul, smul_eq_mul, zero_mul, add_zero, mul_zero, zero_add]
    rw [hSderiv, hPderiv, hQderiv]
    simp only [alphaResidual68, betaResidual68]
    simp [Derivation.leibniz_div, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
      hc9, hc27, hc35, hc36, hc72, hc81, hc243, hc432, hc1296,
      hc12, hc13] <;> ring
  have hepsilon : d (epsilonResidual68 L A B C0 D E P Q R T) = 0 := by
    simp only [epsilonResidual68, map_sub, map_add, map_neg,
      Derivation.leibniz, Derivation.leibniz_pow, derivation_natDiv_zero68,
      hL, halpha, hbeta, hgamma, nsmul_eq_mul, smul_eq_mul, zero_mul,
      add_zero, mul_zero, zero_add]
    rw [hTderiv, hRderiv, hQderiv, hPderiv]
    simp only [alphaResidual68, betaResidual68, gammaResidual68]
    simp [Derivation.leibniz_div, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
      hc9, hc27, hc35, hc36, hc72, hc81, hc243, hc432, hc1296,
      hc12, hc13] <;> ring
  have hzeta : d (zetaResidual68 L A B C0 D E P Q R S U) = 0 := by
    simp only [zetaResidual68, map_sub, map_add, map_neg,
      Derivation.leibniz, Derivation.leibniz_pow, derivation_natDiv_zero68,
      hL, halpha, hbeta, hgamma, hdelta, nsmul_eq_mul, smul_eq_mul,
      zero_mul, add_zero, mul_zero, zero_add]
    rw [hUderiv, hSderiv, hRderiv, hQderiv, hPderiv]
    simp only [alphaResidual68, betaResidual68, gammaResidual68,
      deltaResidual68]
    simp [Derivation.leibniz_div, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
      hc9, hc27, hc35, hc36, hc72, hc81, hc243, hc432, hc1296,
      hc12, hc13, hc19]
    rw [hcInv2]
    ring
  have heta : d (etaResidual68 L A B C0 D E P Q R S T V) = 0 := by
    simp only [etaResidual68, map_sub, map_add, map_neg,
      Derivation.leibniz, Derivation.leibniz_pow, derivation_natDiv_zero68,
      hL, halpha, hbeta, hgamma, hdelta, hepsilon, nsmul_eq_mul,
      smul_eq_mul, zero_mul, add_zero, mul_zero, zero_add]
    rw [hVderiv, hTderiv, hSderiv, hRderiv, hQderiv, hPderiv]
    simp only [alphaResidual68, betaResidual68, gammaResidual68,
      deltaResidual68, epsilonResidual68]
    simp [Derivation.leibniz_div, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
      hc9, hc27, hc35, hc36, hc72, hc81, hc243, hc432, hc1296,
      hc12, hc13, hc19]
    rw [hcInv2, hcInv3, hcInv9]
    ring
  exact ⟨halpha, hbeta, hgamma, hdelta, hepsilon, hzeta, heta⟩

end IntegratedUpperRows68

end DifferentialNormalForm68

#print axioms coefficientDeriv_depressedSextic68
#print axioms coefficientDeriv_depressedOctic68
#print axioms coefficientDeriv_depressedOctic68_full
#print axioms depressedL_deriv_zero68
#print axioms differentialJacobian_depressed68_eq
#print axioms derivation_ratCast_zero68
#print axioms derivation_natDiv_zero68
#print axioms derivation_ofNat_zero68
#print axioms depressedUpperRows68
#print axioms depressedLowerRows68
#print axioms depressedUpperResiduals_deriv_zero68

end Max11DegreeRoutes
