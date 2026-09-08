import LowScale68NormalForm

/-! # Integrated upper normal form for the normalized `(6,8)` leaf

The seven upper Jacobian rows are triangular.  This module solves them in
the Faber basis: seven differential constants reconstruct the octic
coefficients `P,...,V` explicitly.  The construction is purely algebraic and
will be shared by the square and quadratic-source branches.
-/

noncomputable section

namespace Max11DegreeRoutes

section IntegratedNormalForm68

variable {F : Type*} [Field F] [CharZero F]

def integratedP68 (A alpha : F) : F :=
  (4 / 3 : F) * A + alpha

def integratedQ68 (L A B beta : F) : F :=
  (4 / 3 : F) * B + (7 / 6 : F) * L * A + beta

def integratedR68 (L A B C0 alpha gamma : F) : F :=
  (4 / 3 : F) * C0 + (2 / 9 : F) * A ^ 2 +
    (7 / 6 : F) * L * B + alpha * A + gamma

def integratedS68 (L A B C0 D alpha beta delta : F) : F :=
  (4 / 3 : F) * D + (4 / 9 : F) * A * B +
    L * ((7 / 6 : F) * C0 + (7 / 72 : F) * A ^ 2) +
    alpha * B + (5 / 6 : F) * beta * A + delta

def integratedT68 (L A B C0 D E alpha beta gamma epsilon : F) : F :=
  (4 / 3 : F) * E + (2 / 9 : F) * B ^ 2 +
    (4 / 9 : F) * A * C0 - (4 / 81 : F) * A ^ 3 +
    L * ((7 / 6 : F) * D + (7 / 36 : F) * A * B) +
    alpha * C0 + (5 / 6 : F) * beta * B +
    (2 / 3 : F) * gamma * A + epsilon

def integratedU68
    (L A B C0 D E alpha beta gamma delta zeta : F) : F :=
  (4 / 9 : F) * B * C0 + (4 / 9 : F) * A * D -
    (4 / 27 : F) * A ^ 2 * B +
    L * ((7 / 6 : F) * E + (7 / 72 : F) * B ^ 2 +
      (7 / 36 : F) * A * C0 - (35 / 1296 : F) * A ^ 3) +
    alpha * D + beta * ((5 / 6 : F) * C0 - (5 / 72 : F) * A ^ 2) +
    (2 / 3 : F) * gamma * B + (1 / 2 : F) * delta * A + zeta

def integratedV68
    (L A B C0 D E alpha beta gamma delta epsilon eta : F) : F :=
  (2 / 9 : F) * C0 ^ 2 + (4 / 9 : F) * B * D +
    (4 / 9 : F) * A * E - (4 / 27 : F) * A * B ^ 2 -
    (4 / 27 : F) * A ^ 2 * C0 + (5 / 243 : F) * A ^ 4 +
    L * ((7 / 36 : F) * B * C0 + (7 / 36 : F) * A * D -
      (35 / 432 : F) * A ^ 2 * B) +
    alpha * E + beta * ((5 / 6 : F) * D - (5 / 36 : F) * A * B) +
    gamma * ((2 / 3 : F) * C0 - (1 / 9 : F) * A ^ 2) +
    (1 / 2 : F) * delta * B + (1 / 3 : F) * epsilon * A + eta

set_option maxHeartbeats 1000000 in
/-- Substituting the integrated coefficient formulas recovers exactly the
seven chosen Faber constants. -/
theorem integratedResiduals68
    (L A B C0 D E alpha beta gamma delta epsilon zeta eta : F) :
    alphaResidual68 A (integratedP68 A alpha) = alpha ∧
    betaResidual68 L A B (integratedQ68 L A B beta) = beta ∧
    gammaResidual68 L A B C0 (integratedP68 A alpha)
      (integratedR68 L A B C0 alpha gamma) = gamma ∧
    deltaResidual68 L A B C0 D (integratedP68 A alpha)
      (integratedQ68 L A B beta)
      (integratedS68 L A B C0 D alpha beta delta) = delta ∧
    epsilonResidual68 L A B C0 D E (integratedP68 A alpha)
      (integratedQ68 L A B beta) (integratedR68 L A B C0 alpha gamma)
      (integratedT68 L A B C0 D E alpha beta gamma epsilon) = epsilon ∧
    zetaResidual68 L A B C0 D E (integratedP68 A alpha)
      (integratedQ68 L A B beta) (integratedR68 L A B C0 alpha gamma)
      (integratedS68 L A B C0 D alpha beta delta)
      (integratedU68 L A B C0 D E alpha beta gamma delta zeta) = zeta ∧
    etaResidual68 L A B C0 D E (integratedP68 A alpha)
      (integratedQ68 L A B beta) (integratedR68 L A B C0 alpha gamma)
      (integratedS68 L A B C0 D alpha beta delta)
      (integratedT68 L A B C0 D E alpha beta gamma epsilon)
      (integratedV68 L A B C0 D E alpha beta gamma delta epsilon eta) =
        eta := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [alphaResidual68, betaResidual68, gammaResidual68,
      deltaResidual68, epsilonResidual68, zetaResidual68, etaResidual68,
      integratedP68, integratedQ68, integratedR68, integratedS68,
      integratedT68, integratedU68, integratedV68] <;>
    ring

set_option maxHeartbeats 1000000 in
/-- Conversely, arbitrary octic coefficients are reconstructed by taking
their seven triangular residuals as the integration constants. -/
theorem reconstructOcticCoefficients68
    (L P Q R S T U V A B C0 D E : F) :
    let alpha := alphaResidual68 A P
    let beta := betaResidual68 L A B Q
    let gamma := gammaResidual68 L A B C0 P R
    let delta := deltaResidual68 L A B C0 D P Q S
    let epsilon := epsilonResidual68 L A B C0 D E P Q R T
    let zeta := zetaResidual68 L A B C0 D E P Q R S U
    let eta := etaResidual68 L A B C0 D E P Q R S T V
    P = integratedP68 A alpha ∧
    Q = integratedQ68 L A B beta ∧
    R = integratedR68 L A B C0 alpha gamma ∧
    S = integratedS68 L A B C0 D alpha beta delta ∧
    T = integratedT68 L A B C0 D E alpha beta gamma epsilon ∧
    U = integratedU68 L A B C0 D E alpha beta gamma delta zeta ∧
    V = integratedV68 L A B C0 D E alpha beta gamma delta epsilon eta := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [alphaResidual68, betaResidual68, gammaResidual68,
      deltaResidual68, epsilonResidual68, zetaResidual68, etaResidual68,
      integratedP68, integratedQ68, integratedR68, integratedS68,
      integratedT68, integratedU68, integratedV68] <;>
    ring

/-- First exact lower-row integral, whose derivative is the `z⁴` row after
the seven upper coefficients have been integrated. -/
def firstIntegralFour68
    (L A B C0 D E beta gamma delta epsilon zeta : F) : F :=
  (-8 / 27 : F) * B ^ 3 + A * zeta + 2 * B * epsilon +
    3 * C0 * delta + 4 * D * gamma + 5 * E * beta -
    (8 / 9 : F) * A ^ 2 * D - (5 / 12 : F) * B ^ 2 * beta -
    (3 / 4 : F) * A ^ 2 * delta + (7 / 12 : F) * C0 ^ 2 * L +
    (8 / 3 : F) * B * E + (8 / 3 : F) * C0 * D +
    (35 / 216 : F) * A ^ 3 * beta + (40 / 81 : F) * A ^ 3 * B +
    (385 / 5184 : F) * A ^ 4 * L - (35 / 72 : F) * A * B ^ 2 * L -
    (35 / 72 : F) * A ^ 2 * C0 * L - (16 / 9 : F) * A * B * C0 -
    (5 / 6 : F) * A * C0 * beta - (4 / 3 : F) * A * B * gamma +
    (7 / 6 : F) * A * E * L + (7 / 6 : F) * B * D * L

/-- Second exact lower-row integral, whose derivative is the `z³` row after
the seven upper coefficients have been integrated. -/
def firstIntegralThree68
    (L A B C0 D E beta gamma delta epsilon zeta : F) : F :=
  (-16 / 243 : F) * A ^ 5 + (4 / 3 : F) * D ^ 2 + B * zeta +
    2 * C0 * epsilon + 3 * D * delta + 4 * E * gamma -
    (35 / 216 : F) * B ^ 3 * L - (8 / 9 : F) * A * C0 ^ 2 -
    (8 / 9 : F) * B ^ 2 * C0 - (8 / 9 : F) * A ^ 2 * E -
    (2 / 3 : F) * A ^ 2 * epsilon - (2 / 3 : F) * B ^ 2 * gamma +
    (8 / 3 : F) * C0 * E + (8 / 27 : F) * A ^ 3 * gamma +
    (20 / 27 : F) * A ^ 2 * B ^ 2 + (40 / 81 : F) * A ^ 3 * C0 -
    (35 / 72 : F) * A ^ 2 * D * L - (16 / 9 : F) * A * B * D -
    (5 / 6 : F) * A * D * beta - (5 / 6 : F) * B * C0 * beta -
    (4 / 3 : F) * A * C0 * gamma - (3 / 2 : F) * A * B * delta +
    (7 / 6 : F) * B * E * L + (7 / 6 : F) * C0 * D * L +
    (35 / 72 : F) * A ^ 2 * B * beta +
    (385 / 1296 : F) * A ^ 3 * B * L -
    (35 / 36 : F) * A * B * C0 * L

section DifferentialFirstIntegrals68

variable {k : Type*} [Field k] [Algebra k F]

set_option maxHeartbeats 2000000 in
/-- The literal integrated `z⁴` Jacobian row is the derivative of the first
displayed coefficient invariant. -/
theorem lowerRowFour_integrated68_eq_deriv
    (d : Derivation k F F)
    (L A B C0 D E alpha beta gamma delta epsilon zeta : F)
    (hL : d L = 0) (halpha : d alpha = 0) (hbeta : d beta = 0)
    (hgamma : d gamma = 0) (hdelta : d delta = 0)
    (hepsilon : d epsilon = 0) (hzeta : d zeta = 0) :
    let Q := integratedQ68 L A B beta
    let R := integratedR68 L A B C0 alpha gamma
    let S := integratedS68 L A B C0 D alpha beta delta
    let T := integratedT68 L A B C0 D E alpha beta gamma epsilon
    let U := integratedU68 L A B C0 D E alpha beta gamma delta zeta
    U * d A + 2 * T * d B + 3 * S * d C0 + 4 * R * d D +
        5 * Q * d E - 4 * A * d U - 3 * B * d T -
        2 * C0 * d S - D * d R =
      d (firstIntegralFour68 L A B C0 D E beta gamma delta epsilon zeta) := by
  dsimp only
  have h1 : d (1 : F) = 0 := by
    simpa only [Nat.cast_one] using d.map_natCast 1
  simp only [integratedQ68, integratedR68, integratedS68, integratedT68,
    integratedU68, firstIntegralFour68, map_add, map_sub, map_neg,
    Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_div,
    Derivation.leibniz_inv, nsmul_eq_mul, smul_eq_mul, hL, halpha, hbeta,
    hgamma, hdelta, hepsilon, hzeta]
  simp [derivation_ofNat_zero68 d, h1]
  ring

set_option maxHeartbeats 2000000 in
/-- The literal integrated `z³` Jacobian row is the derivative of the second
displayed coefficient invariant. -/
theorem lowerRowThree_integrated68_eq_deriv
    (d : Derivation k F F)
    (L A B C0 D E alpha beta gamma delta epsilon zeta eta : F)
    (hL : d L = 0) (halpha : d alpha = 0) (hbeta : d beta = 0)
    (hgamma : d gamma = 0) (hdelta : d delta = 0)
    (hepsilon : d epsilon = 0) (hzeta : d zeta = 0)
    (heta : d eta = 0) :
    let R := integratedR68 L A B C0 alpha gamma
    let S := integratedS68 L A B C0 D alpha beta delta
    let T := integratedT68 L A B C0 D E alpha beta gamma epsilon
    let U := integratedU68 L A B C0 D E alpha beta gamma delta zeta
    let V := integratedV68 L A B C0 D E alpha beta gamma delta epsilon eta
    U * d B + 2 * T * d C0 + 3 * S * d D + 4 * R * d E -
        4 * A * d V - 3 * B * d U - 2 * C0 * d T - D * d S =
      d (firstIntegralThree68 L A B C0 D E beta gamma delta epsilon zeta) := by
  dsimp only
  have h1 : d (1 : F) = 0 := by
    simpa only [Nat.cast_one] using d.map_natCast 1
  simp only [integratedR68, integratedS68, integratedT68, integratedU68,
    integratedV68, firstIntegralThree68, map_add, map_sub, map_neg,
    Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_div,
    Derivation.leibniz_inv, nsmul_eq_mul, smul_eq_mul, hL, halpha, hbeta,
    hgamma, hdelta, hepsilon, hzeta, heta]
  simp [derivation_ofNat_zero68 d, h1]
  ring

set_option maxHeartbeats 2000000 in
/-- Complete lower coefficient system for the integrated `(6,8)` normal
form: two exact coefficient invariants followed by the three irreducible
one-form rows, with the last row equal to the Keller constant. -/
theorem constantBracket_integrated68_lowerSystem
    (d : Derivation k F F)
    (L A B C0 D E alpha beta gamma delta epsilon zeta eta terminal : F)
    (hL : d L = 0) (halpha : d alpha = 0) (hbeta : d beta = 0)
    (hgamma : d gamma = 0) (hdelta : d delta = 0)
    (hepsilon : d epsilon = 0) (hzeta : d zeta = 0)
    (heta : d eta = 0)
    (hbracket :
      let P := integratedP68 A alpha
      let Q := integratedQ68 L A B beta
      let R := integratedR68 L A B C0 alpha gamma
      let S := integratedS68 L A B C0 D alpha beta delta
      let T := integratedT68 L A B C0 D E alpha beta gamma epsilon
      let U := integratedU68 L A B C0 D E alpha beta gamma delta zeta
      let V := integratedV68 L A B C0 D E alpha beta gamma delta epsilon eta
      differentialJacobian d (depressedSextic68 A B C0 D E)
        (depressedOctic68 L P Q R S T U V) = Polynomial.C terminal) :
    let P := integratedP68 A alpha
    let Q := integratedQ68 L A B beta
    let R := integratedR68 L A B C0 alpha gamma
    let S := integratedS68 L A B C0 D alpha beta delta
    let T := integratedT68 L A B C0 D E alpha beta gamma epsilon
    let U := integratedU68 L A B C0 D E alpha beta gamma delta zeta
    let V := integratedV68 L A B C0 D E alpha beta gamma delta epsilon eta
    d (firstIntegralFour68 L A B C0 D E beta gamma delta epsilon zeta) = 0 ∧
    d (firstIntegralThree68 L A B C0 D E beta gamma delta epsilon zeta) = 0 ∧
    (U * d C0 + 2 * T * d D + 3 * S * d E - 3 * B * d V -
      2 * C0 * d U - D * d T = 0) ∧
    (U * d D + 2 * T * d E - 2 * C0 * d V - D * d U = 0) ∧
    (U * d E - D * d V = terminal) := by
  dsimp only at hbracket ⊢
  rcases depressedLowerRows68 d L (integratedP68 A alpha)
      (integratedQ68 L A B beta) (integratedR68 L A B C0 alpha gamma)
      (integratedS68 L A B C0 D alpha beta delta)
      (integratedT68 L A B C0 D E alpha beta gamma epsilon)
      (integratedU68 L A B C0 D E alpha beta gamma delta zeta)
      (integratedV68 L A B C0 D E alpha beta gamma delta epsilon eta)
      A B C0 D E terminal hL hbracket with ⟨h4, h3, h2, h1, h0⟩
  rw [lowerRowFour_integrated68_eq_deriv d L A B C0 D E alpha beta gamma
    delta epsilon zeta hL halpha hbeta hgamma hdelta hepsilon hzeta] at h4
  rw [lowerRowThree_integrated68_eq_deriv d L A B C0 D E alpha beta gamma
    delta epsilon zeta eta hL halpha hbeta hgamma hdelta hepsilon hzeta
    heta] at h3
  exact ⟨h4, h3, h2, h1, h0⟩

end DifferentialFirstIntegrals68

#print axioms integratedResiduals68
#print axioms reconstructOcticCoefficients68
#print axioms lowerRowFour_integrated68_eq_deriv
#print axioms lowerRowThree_integrated68_eq_deriv
#print axioms constantBracket_integrated68_lowerSystem

end IntegratedNormalForm68

end Max11DegreeRoutes
