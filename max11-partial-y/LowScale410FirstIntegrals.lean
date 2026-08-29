import LowScale410NormalForm

/-!
# First integrals for the terminal `(4,10)` differential rows

This module continues the direct quartic--decic route.  The nine
upper rows have already been integrated in
`LowScale410NormalForm`; here the `z^2` and `z` rows are identified
as exact derivatives, leaving one literal scalar row.
-/

noncomputable section

set_option maxHeartbeats 2000000

open Polynomial

namespace Max11DegreeRoutes

section FirstIntegrals410

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- A primitive of the `z^2` row after all nine upper decic rows have been
integrated. -/
def firstIntegralTwo410
    (L A B C0 beta gamma delta zeta eta theta : F) : F :=
  ((63 / 2048 : ℚ) : F) * L * A ^ 5 +
    ((15 / 64 : ℚ) : F) * A ^ 4 * B +
    ((35 / 512 : ℚ) : F) * beta * A ^ 4 -
    ((45 / 128 : ℚ) : F) * L * A ^ 3 * C0 -
    ((135 / 256 : ℚ) : F) * L * A ^ 2 * B ^ 2 -
    ((5 / 32 : ℚ) : F) * delta * A ^ 3 -
    ((15 / 8 : ℚ) : F) * A ^ 2 * B * C0 -
    ((3 / 4 : ℚ) : F) * gamma * A ^ 2 * B -
    ((21 / 32 : ℚ) : F) * beta * A ^ 2 * C0 -
    ((5 / 8 : ℚ) : F) * A * B ^ 3 -
    ((21 / 32 : ℚ) : F) * beta * A * B ^ 2 +
    ((45 / 32 : ℚ) : F) * L * A * C0 ^ 2 +
    ((45 / 32 : ℚ) : F) * L * B ^ 2 * C0 -
    ((3 / 8 : ℚ) : F) * zeta * A ^ 2 +
    ((5 / 4 : ℚ) : F) * delta * A * C0 +
    ((5 / 8 : ℚ) : F) * delta * B ^ 2 +
    ((15 / 4 : ℚ) : F) * B * C0 ^ 2 +
    (3 : F) * gamma * B * C0 +
    ((21 / 8 : ℚ) : F) * beta * C0 ^ 2 +
    theta * A + 2 * eta * B + 3 * zeta * C0

/-- A primitive of the `z` row after all nine upper decic rows have been
integrated. -/
def firstIntegralOne410
    (L A B C0 beta gamma delta zeta eta theta : F) : F :=
  -((5 / 256 : ℚ) : F) * A ^ 6 +
    ((315 / 2048 : ℚ) : F) * L * A ^ 4 * B +
    ((15 / 64 : ℚ) : F) * A ^ 4 * C0 +
    ((3 / 32 : ℚ) : F) * gamma * A ^ 4 +
    ((15 / 32 : ℚ) : F) * A ^ 3 * B ^ 2 +
    ((35 / 128 : ℚ) : F) * beta * A ^ 3 * B -
    ((135 / 128 : ℚ) : F) * L * A ^ 2 * B * C0 -
    ((45 / 128 : ℚ) : F) * L * A * B ^ 3 -
    ((15 / 32 : ℚ) : F) * delta * A ^ 2 * B -
    ((15 / 16 : ℚ) : F) * A ^ 2 * C0 ^ 2 -
    ((3 / 4 : ℚ) : F) * gamma * A ^ 2 * C0 -
    ((15 / 8 : ℚ) : F) * A * B ^ 2 * C0 -
    ((3 / 4 : ℚ) : F) * gamma * A * B ^ 2 -
    ((21 / 16 : ℚ) : F) * beta * A * B * C0 -
    ((5 / 32 : ℚ) : F) * B ^ 4 -
    ((7 / 32 : ℚ) : F) * beta * B ^ 3 +
    ((45 / 32 : ℚ) : F) * L * B * C0 ^ 2 -
    ((1 / 2 : ℚ) : F) * eta * A ^ 2 -
    ((3 / 4 : ℚ) : F) * zeta * A * B +
    ((5 / 4 : ℚ) : F) * delta * B * C0 +
    ((5 / 4 : ℚ) : F) * C0 ^ 3 +
    ((3 / 2 : ℚ) : F) * gamma * C0 ^ 2 +
    theta * B + 2 * eta * C0

/-- The two nonconstant terminal rows are exact one-forms. -/
theorem integratedTerminalRows410_eq_deriv (d : Derivation k F F)
    (L A B C0 alpha beta gamma delta epsilon zeta eta theta iota : F)
    (hL : d L = 0) (halpha : d alpha = 0) (hbeta : d beta = 0)
    (hgamma : d gamma = 0) (hdelta : d delta = 0)
    (hepsilon : d epsilon = 0) (hzeta : d zeta = 0)
    (heta : d eta = 0) (htheta : d theta = 0) (hiota : d iota = 0) :
    let U := integratedU410 L A B C0 alpha beta gamma delta zeta
    let V := integratedV410 L A B C0 alpha beta gamma delta epsilon eta
    let W := integratedW410 L A B C0 alpha beta gamma delta epsilon zeta theta
    let Z := integratedZ410 L A B C0 alpha beta gamma delta epsilon zeta eta iota
    (W * d A + 2 * V * d B + 3 * U * d C0 -
        2 * A * d W - B * d V =
      d (firstIntegralTwo410 L A B C0 beta gamma delta zeta eta theta)) ∧
    (W * d B + 2 * V * d C0 - 2 * A * d Z - B * d W =
      d (firstIntegralOne410 L A B C0 beta gamma delta zeta eta theta)) := by
  dsimp only
  have hn2 : d (2 : F) = 0 := d.map_natCast 2
  have hn3 : d (3 : F) = 0 := d.map_natCast 3
  have hn16 : d (16 : F) = 0 := d.map_natCast 16
  have h12 : d (1 / 2 : F) = 0 := by
    simp [Derivation.leibniz_inv, hn2]
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
    simp [Derivation.leibniz_inv, hn16]
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
  refine ⟨?_, ?_⟩ <;>
    simp only [integratedU410, integratedV410, integratedW410,
      integratedZ410, firstIntegralTwo410, firstIntegralOne410,
      map_add, map_sub, map_neg, Derivation.leibniz,
      Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul,
      derivation_ratCast_zero68, hn2, hn3, hn16, h12, h32, h52, h34, h54,
      h74, h94, h154, h38, h158, h116, h516, h1516, h2116, h4516,
      h532, h2132, h4532, h1564, h4564, h7128, h5128, h15128,
      h21128, h45128, h3256, h45512, h452048, hn5128, hn452048,
      hn45512, hn532, hn116, hn1564, hn21128, hL, halpha, hbeta,
      hgamma, hdelta, hepsilon, hzeta, heta, htheta, hiota,
      mul_zero, zero_mul, add_zero, zero_add] <;>
    norm_num <;>
    ring

/-- Fully integrated quartic--decic Jacobian: two exact first-integral rows
and one literal scalar row. -/
theorem differentialJacobian_integrated410_firstIntegrals_eq
    (d : Derivation k F F)
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
      C (d (firstIntegralTwo410 L A B C0 beta gamma delta zeta eta theta)) *
          X ^ 2 +
      C (d (firstIntegralOne410 L A B C0 beta gamma delta zeta eta theta)) * X +
      C (W * d C0 - B * d Z) := by
  dsimp only
  rw [differentialJacobian_integrated410_eq d L A B C0 alpha beta gamma
    delta epsilon zeta eta theta iota hL halpha hbeta hgamma hdelta
    hepsilon hzeta heta htheta hiota]
  obtain ⟨h2, h1⟩ := integratedTerminalRows410_eq_deriv d L A B C0 alpha
    beta gamma delta epsilon zeta eta theta iota hL halpha hbeta hgamma
    hdelta hepsilon hzeta heta htheta hiota
  rw [h2, h1]

/-- If the differential bracket is constant, its exact rational lower
system consists of two conserved first integrals and the last scalar row. -/
theorem integrated410_lowerSystem_of_constantBracket
    (d : Derivation k F F)
    (L A B C0 alpha beta gamma delta epsilon zeta eta theta iota terminal : F)
    (hL : d L = 0) (halpha : d alpha = 0) (hbeta : d beta = 0)
    (hgamma : d gamma = 0) (hdelta : d delta = 0)
    (hepsilon : d epsilon = 0) (hzeta : d zeta = 0)
    (heta : d eta = 0) (htheta : d theta = 0) (hiota : d iota = 0)
    (hbracket :
      differentialJacobian d (depressedQuartic46 A B C0)
        (depressedDecic410 L (integratedP410 A alpha)
          (integratedQ410 L A B beta)
          (integratedR410 L A B C0 alpha gamma)
          (integratedS410 L A B C0 alpha beta delta)
          (integratedT410 L A B C0 alpha beta gamma epsilon)
          (integratedU410 L A B C0 alpha beta gamma delta zeta)
          (integratedV410 L A B C0 alpha beta gamma delta epsilon eta)
          (integratedW410 L A B C0 alpha beta gamma delta epsilon zeta theta)
          (integratedZ410 L A B C0 alpha beta gamma delta epsilon zeta eta iota)) =
        C terminal) :
    d (firstIntegralTwo410 L A B C0 beta gamma delta zeta eta theta) = 0 ∧
    d (firstIntegralOne410 L A B C0 beta gamma delta zeta eta theta) = 0 ∧
    integratedW410 L A B C0 alpha beta gamma delta epsilon zeta theta * d C0 -
        B * d (integratedZ410 L A B C0 alpha beta gamma delta epsilon zeta eta iota) =
      terminal := by
  rw [differentialJacobian_integrated410_firstIntegrals_eq d L A B C0
    alpha beta gamma delta epsilon zeta eta theta iota hL halpha hbeta
    hgamma hdelta hepsilon hzeta heta htheta hiota] at hbracket
  have h2 := congrArg (fun f : F[X] => f.coeff 2) hbracket
  have h1 := congrArg (fun f : F[X] => f.coeff 1) hbracket
  have h0 := congrArg (fun f : F[X] => f.coeff 0) hbracket
  norm_num at h2 h1 h0
  exact ⟨h2, h1, h0⟩

end FirstIntegrals410

section PolynomialPullback410

variable {k : Type*} [Field k] [CharZero k]

/-- Literal polynomial representative of the first decic invariant in the
constant-scale branch. -/
def firstIntegralTwoPolynomial410
    (l beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : k[X] :=
  (63 / 2048 : k) • (l • A ^ 5) + (15 / 64 : k) • (A ^ 4 * B) +
    (35 / 512 * beta : k) • A ^ 4 - (45 / 128 * l : k) • (A ^ 3 * C0) -
    (135 / 256 * l : k) • (A ^ 2 * B ^ 2) -
    (5 / 32 * delta : k) • A ^ 3 - (15 / 8 : k) • (A ^ 2 * B * C0) -
    (3 / 4 * gamma : k) • (A ^ 2 * B) -
    (21 / 32 * beta : k) • (A ^ 2 * C0) - (5 / 8 : k) • (A * B ^ 3) -
    (21 / 32 * beta : k) • (A * B ^ 2) +
    (45 / 32 * l : k) • (A * C0 ^ 2) +
    (45 / 32 * l : k) • (B ^ 2 * C0) - (3 / 8 * zeta : k) • A ^ 2 +
    (5 / 4 * delta : k) • (A * C0) + (5 / 8 * delta : k) • B ^ 2 +
    (15 / 4 : k) • (B * C0 ^ 2) + (3 * gamma : k) • (B * C0) +
    (21 / 8 * beta : k) • C0 ^ 2 + theta • A +
    (2 * eta : k) • B + (3 * zeta : k) • C0

/-- Literal polynomial representative of the second decic invariant in the
constant-scale branch. -/
def firstIntegralOnePolynomial410
    (l beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : k[X] :=
  -(5 / 256 : k) • A ^ 6 + (315 / 2048 * l : k) • (A ^ 4 * B) +
    (15 / 64 : k) • (A ^ 4 * C0) + (3 / 32 * gamma : k) • A ^ 4 +
    (15 / 32 : k) • (A ^ 3 * B ^ 2) +
    (35 / 128 * beta : k) • (A ^ 3 * B) -
    (135 / 128 * l : k) • (A ^ 2 * B * C0) -
    (45 / 128 * l : k) • (A * B ^ 3) -
    (15 / 32 * delta : k) • (A ^ 2 * B) -
    (15 / 16 : k) • (A ^ 2 * C0 ^ 2) -
    (3 / 4 * gamma : k) • (A ^ 2 * C0) -
    (15 / 8 : k) • (A * B ^ 2 * C0) -
    (3 / 4 * gamma : k) • (A * B ^ 2) -
    (21 / 16 * beta : k) • (A * B * C0) - (5 / 32 : k) • B ^ 4 -
    (7 / 32 * beta : k) • B ^ 3 + (45 / 32 * l : k) • (B * C0 ^ 2) -
    (1 / 2 * eta : k) • A ^ 2 - (3 / 4 * zeta : k) • (A * B) +
    (5 / 4 * delta : k) • (B * C0) + (5 / 4 : k) • C0 ^ 3 +
    (3 / 2 * gamma : k) • C0 ^ 2 + theta • B + (2 * eta : k) • C0

theorem algebraMap_firstIntegralTwoPolynomial410
    (l beta gamma delta zeta eta theta : k) (A B C0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (firstIntegralTwoPolynomial410 l beta gamma delta zeta eta theta
          A B C0) =
      firstIntegralTwo410 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C zeta) (RatFunc.C eta) (RatFunc.C theta) := by
  simp only [firstIntegralTwoPolynomial410, firstIntegralTwo410, map_add,
    map_sub, map_neg, Polynomial.smul_eq_C_mul, map_mul, map_pow,
    RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_one]
  ring

theorem algebraMap_firstIntegralOnePolynomial410
    (l beta gamma delta zeta eta theta : k) (A B C0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (firstIntegralOnePolynomial410 l beta gamma delta zeta eta theta
          A B C0) =
      firstIntegralOne410 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C zeta) (RatFunc.C eta) (RatFunc.C theta) := by
  simp only [firstIntegralOnePolynomial410, firstIntegralOne410, map_add,
    map_sub, map_neg, Polynomial.smul_eq_C_mul, map_mul, map_pow,
    RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_one]
  ring

/-- Polynomial pullback of the sole non-exact decic terminal row. -/
def lowerRowZeroPolynomial410 (W Z B C0 : k[X]) : k[X] :=
  W * derivative C0 - B * derivative Z

theorem algebraMap_lowerRowZeroPolynomial410 (W Z B C0 : k[X]) :
    algebraMap k[X] (RatFunc k) (lowerRowZeroPolynomial410 W Z B C0) =
      algebraMap k[X] (RatFunc k) W *
          ratFuncDerivation46 (algebraMap k[X] (RatFunc k) C0) -
        algebraMap k[X] (RatFunc k) B *
          ratFuncDerivation46 (algebraMap k[X] (RatFunc k) Z) := by
  rw [ratFuncDerivation46_polynomial, ratFuncDerivation46_polynomial]
  simp only [lowerRowZeroPolynomial410, map_sub, map_mul]

/-- Once the constant-scale adapter supplies polynomial coordinates and the
residual constants lie in `k`, the two rational conserved quantities are
literal constant polynomials. -/
theorem polynomialFirstIntegrals410_exist_constants
    (l beta gamma delta zeta eta theta : k) (A B C0 : k[X])
    (hTwo : ratFuncDerivation46
      (firstIntegralTwo410 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C zeta) (RatFunc.C eta) (RatFunc.C theta)) = 0)
    (hOne : ratFuncDerivation46
      (firstIntegralOne410 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C zeta) (RatFunc.C eta) (RatFunc.C theta)) = 0) :
    ∃ k2 k1 : k,
      firstIntegralTwoPolynomial410 l beta gamma delta zeta eta theta
          A B C0 = C k2 ∧
        firstIntegralOnePolynomial410 l beta gamma delta zeta eta theta
          A B C0 = C k1 := by
  let I2 := firstIntegralTwoPolynomial410 l beta gamma delta zeta eta theta
    A B C0
  let I1 := firstIntegralOnePolynomial410 l beta gamma delta zeta eta theta
    A B C0
  have hd2map : algebraMap k[X] (RatFunc k) I2.derivative = 0 := by
    rw [← ratFuncDerivation46_polynomial]
    simp only [I2, algebraMap_firstIntegralTwoPolynomial410]
    exact hTwo
  have hd1map : algebraMap k[X] (RatFunc k) I1.derivative = 0 := by
    rw [← ratFuncDerivation46_polynomial]
    simp only [I1, algebraMap_firstIntegralOnePolynomial410]
    exact hOne
  have hd2 : I2.derivative = 0 := by
    apply RatFunc.algebraMap_injective k
    simpa using hd2map
  have hd1 : I1.derivative = 0 := by
    apply RatFunc.algebraMap_injective k
    simpa using hd1map
  refine ⟨I2.coeff 0, I1.coeff 0, ?_, ?_⟩
  · exact Polynomial.eq_C_of_derivative_eq_zero hd2
  · exact Polynomial.eq_C_of_derivative_eq_zero hd1

end PolynomialPullback410

end Max11DegreeRoutes
