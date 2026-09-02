import Grok610ScaleZeroFinalRowScratch

/-! # Scale-zero valuation endgame for the normalized `(6,10)`, `H = 0` leaf

Continuation of `Grok610ScaleZeroFinalRowScratch` on the constant core
`H = (C t)²`.  The Jacobian tower is fully consumed: the last Keller
row is the inhomogeneous identity `W E' - D X' = j / t` with `j ≠ 0`,
and the weight-fifteen primitive differentiates to that same nonzero
constant.  Every cleared defect through the weight-seventy residual
`ο` is a ground constant, including the exact selector
`6291456 p₀ q₃ h⁶²`.

This file supplies the missing `(4,10)`-style polynomial-trajectory
input: the nine triangular Faber coordinates of the depressed decic
are reconstructed from the already-constant residual tower
`α,…,ι`, so the remaining free core is the depressed sextic
`(A, B, C₀, D₀, E₀)`.  On that trajectory the primitive is a
function of the core and of ground constants, and its derivative is
the nonzero constant `j / t`.

A constant core has no finite root, so the scale-two square-chamber
`S0/S1` peel is unavailable.  One exact chamber of the remaining
trajectory is excluded: if every free core letter is a differential
constant, then every integrated decic coefficient is constant, the
primitive is constant, and `0 = j / t` contradicts `j ≠ 0`.  The
leaf is not closed.  The residual Newton-degree / leading-term
comparison of a nonconstant core against the constant lower first
integrals `κ, λ, μ` and the linear primitive is not claimed.  No
total-degree or twice-prime theorem is used.  No finite-root
shortcut is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false

/-! ## Triangular Faber reconstruction of the depressed decic -/

section IntegratedDecic610

variable {F : Type*} [Field F] [CharZero F]

/-- First integrated decic coefficient (the `z¹³` / `α` row). -/
def integratedP610 (A alpha : F) : F :=
  (5 / 3 : F) * A + alpha

/-- Second integrated decic coefficient (the `z¹²` / `β` row). -/
def integratedQ610 (L A B beta : F) : F :=
  (3 / 2 : F) * L * A + (5 / 3 : F) * B + beta

/-- Third integrated decic coefficient (the `z¹¹` / `γ` row). -/
def integratedR610 (L A B C0 alpha gamma : F) : F :=
  (3 / 2 : F) * L * B + (4 / 3 : F) * A * alpha +
    (5 / 9 : F) * A ^ 2 + (5 / 3 : F) * C0 + gamma

/-- Fourth integrated decic coefficient (the `z¹⁰` / `δ` row). -/
def integratedS610 (L A B C0 D0 alpha beta delta : F) : F :=
  (3 / 8 : F) * L * A ^ 2 + (10 / 9 : F) * A * B +
    (3 / 2 : F) * L * C0 + (4 / 3 : F) * B * alpha +
    (7 / 6 : F) * A * beta + (5 / 3 : F) * D0 + delta

/-- Fifth integrated decic coefficient (the `z⁹` / `ε` row). -/
def integratedT610 (L A B C0 D0 E0 alpha beta gamma epsilon : F) : F :=
  -(5 / 81 : F) * A ^ 3 + (2 / 9 : F) * A ^ 2 * alpha +
    (3 / 4 : F) * L * A * B + (10 / 9 : F) * A * C0 +
    (3 / 2 : F) * L * D0 + (4 / 3 : F) * C0 * alpha +
    (5 / 9 : F) * B ^ 2 + (7 / 6 : F) * B * beta +
    A * gamma + (5 / 3 : F) * E0 + epsilon

/-- Sixth integrated decic coefficient (the `z⁸` / `ζ` row). -/
def integratedU610
    (L A B C0 D0 E0 alpha beta gamma delta zeta : F) : F :=
  -(1 / 16 : F) * L * A ^ 3 - (5 / 27 : F) * A ^ 2 * B +
    (3 / 4 : F) * L * A * C0 + (3 / 8 : F) * L * B ^ 2 +
    (4 / 9 : F) * A * B * alpha + (7 / 72 : F) * A ^ 2 * beta +
    (10 / 9 : F) * A * D0 + (10 / 9 : F) * B * C0 +
    (3 / 2 : F) * L * E0 + (4 / 3 : F) * D0 * alpha +
    (5 / 6 : F) * A * delta + (7 / 6 : F) * C0 * beta +
    B * gamma + zeta

/-- Seventh integrated decic coefficient (the `z⁷` / `η` row). -/
def integratedV610
    (L A B C0 D0 E0 alpha beta gamma delta epsilon eta : F) : F :=
  -(3 / 16 : F) * L * A ^ 2 * B - (4 / 81 : F) * A ^ 3 * alpha +
    (5 / 243 : F) * A ^ 4 - (5 / 27 : F) * A ^ 2 * C0 -
    (5 / 27 : F) * A * B ^ 2 + (2 / 9 : F) * B ^ 2 * alpha +
    (3 / 4 : F) * L * A * D0 + (3 / 4 : F) * L * B * C0 +
    (4 / 9 : F) * A * C0 * alpha + (7 / 36 : F) * A * B * beta +
    (10 / 9 : F) * A * E0 + (10 / 9 : F) * B * D0 +
    (2 / 3 : F) * A * epsilon + (4 / 3 : F) * E0 * alpha +
    (5 / 6 : F) * B * delta + (5 / 9 : F) * C0 ^ 2 +
    (7 / 6 : F) * D0 * beta + C0 * gamma + eta

/-- Eighth integrated decic coefficient (the `z⁶` / `θ` row). -/
def integratedW610
    (L A B C0 D0 E0 alpha beta gamma delta epsilon zeta theta : F) : F :=
  (3 / 128 : F) * L * A ^ 4 - (3 / 16 : F) * L * A ^ 2 * C0 -
    (3 / 16 : F) * L * A * B ^ 2 - (35 / 1296 : F) * A ^ 3 * beta -
    (4 / 27 : F) * A ^ 2 * B * alpha + (20 / 243 : F) * A ^ 3 * B -
    (10 / 27 : F) * A * B * C0 - (5 / 27 : F) * A ^ 2 * D0 -
    (5 / 72 : F) * A ^ 2 * delta - (5 / 81 : F) * B ^ 3 +
    (3 / 4 : F) * L * A * E0 + (3 / 4 : F) * L * B * D0 +
    (3 / 8 : F) * L * C0 ^ 2 + (4 / 9 : F) * A * D0 * alpha +
    (4 / 9 : F) * B * C0 * alpha + (7 / 36 : F) * A * C0 * beta +
    (7 / 72 : F) * B ^ 2 * beta + (10 / 9 : F) * B * E0 +
    (10 / 9 : F) * C0 * D0 + (2 / 3 : F) * B * epsilon +
    (5 / 6 : F) * C0 * delta + (7 / 6 : F) * E0 * beta +
    (1 / 2 : F) * A * zeta + D0 * gamma + theta

/-- Ninth integrated decic coefficient (the `z⁵` / `ι` row). -/
def integratedX610
    (L A B C0 D0 E0 alpha beta gamma delta epsilon zeta eta iota : F) :
    F :=
  -(7 / 729 : F) * A ^ 5 + (3 / 32 : F) * L * A ^ 3 * B +
    (5 / 243 : F) * A ^ 4 * alpha - (3 / 16 : F) * L * A ^ 2 * D0 -
    (3 / 8 : F) * L * A * B * C0 - (35 / 432 : F) * A ^ 2 * B * beta -
    (4 / 27 : F) * A ^ 2 * C0 * alpha - (4 / 27 : F) * A * B ^ 2 * alpha -
    (1 / 16 : F) * L * B ^ 3 + (10 / 81 : F) * A ^ 2 * B ^ 2 +
    (20 / 243 : F) * A ^ 3 * C0 - (10 / 27 : F) * A * B * D0 -
    (5 / 27 : F) * A ^ 2 * E0 - (5 / 36 : F) * A * B * delta -
    (5 / 27 : F) * A * C0 ^ 2 - (5 / 27 : F) * B ^ 2 * C0 -
    (1 / 9 : F) * A ^ 2 * epsilon + (2 / 9 : F) * C0 ^ 2 * alpha +
    (3 / 4 : F) * L * B * E0 + (3 / 4 : F) * L * C0 * D0 +
    (4 / 9 : F) * A * E0 * alpha + (4 / 9 : F) * B * D0 * alpha +
    (7 / 36 : F) * A * D0 * beta + (7 / 36 : F) * B * C0 * beta +
    (10 / 9 : F) * C0 * E0 + (2 / 3 : F) * C0 * epsilon +
    (5 / 9 : F) * D0 ^ 2 + (5 / 6 : F) * D0 * delta +
    (1 / 3 : F) * A * eta + (1 / 2 : F) * B * zeta +
    E0 * gamma + iota

set_option maxHeartbeats 8000000 in
/-- Substituting the integrated coefficient formulas recovers exactly the
nine triangular Faber constants. -/
theorem integratedResiduals610
    (L A B C0 D0 E0 alpha beta gamma delta epsilon zeta eta theta iota : F) :
    alphaResidual610 A (integratedP610 A alpha) = alpha ∧
    betaResidual610 L A B (integratedQ610 L A B beta) = beta ∧
    gammaResidual610 L A B C0 (integratedP610 A alpha)
      (integratedR610 L A B C0 alpha gamma) = gamma ∧
    deltaResidual610 L A B C0 D0 (integratedP610 A alpha)
      (integratedQ610 L A B beta)
      (integratedS610 L A B C0 D0 alpha beta delta) = delta ∧
    epsilonResidual610 L A B C0 D0 E0 (integratedP610 A alpha)
      (integratedQ610 L A B beta) (integratedR610 L A B C0 alpha gamma)
      (integratedT610 L A B C0 D0 E0 alpha beta gamma epsilon) = epsilon ∧
    zetaResidual610 L A B C0 D0 E0 (integratedP610 A alpha)
      (integratedQ610 L A B beta) (integratedR610 L A B C0 alpha gamma)
      (integratedS610 L A B C0 D0 alpha beta delta)
      (integratedU610 L A B C0 D0 E0 alpha beta gamma delta zeta) = zeta ∧
    etaResidual610 L A B C0 D0 E0 (integratedP610 A alpha)
      (integratedQ610 L A B beta) (integratedR610 L A B C0 alpha gamma)
      (integratedS610 L A B C0 D0 alpha beta delta)
      (integratedT610 L A B C0 D0 E0 alpha beta gamma epsilon)
      (integratedV610 L A B C0 D0 E0 alpha beta gamma delta epsilon eta) =
        eta ∧
    thetaResidual610 L A B C0 D0 E0 (integratedP610 A alpha)
      (integratedQ610 L A B beta) (integratedR610 L A B C0 alpha gamma)
      (integratedS610 L A B C0 D0 alpha beta delta)
      (integratedT610 L A B C0 D0 E0 alpha beta gamma epsilon)
      (integratedU610 L A B C0 D0 E0 alpha beta gamma delta zeta)
      (integratedW610 L A B C0 D0 E0 alpha beta gamma delta epsilon zeta
        theta) = theta ∧
    iotaResidual610 L A B C0 D0 E0 (integratedP610 A alpha)
      (integratedQ610 L A B beta) (integratedR610 L A B C0 alpha gamma)
      (integratedS610 L A B C0 D0 alpha beta delta)
      (integratedT610 L A B C0 D0 E0 alpha beta gamma epsilon)
      (integratedU610 L A B C0 D0 E0 alpha beta gamma delta zeta)
      (integratedV610 L A B C0 D0 E0 alpha beta gamma delta epsilon eta)
      (integratedX610 L A B C0 D0 E0 alpha beta gamma delta epsilon zeta
        eta iota) = iota := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [alphaResidual610, betaResidual610, gammaResidual610,
      deltaResidual610, epsilonResidual610, zetaResidual610, etaResidual610,
      thetaResidual610, iotaResidual610, integratedP610, integratedQ610,
      integratedR610, integratedS610, integratedT610, integratedU610,
      integratedV610, integratedW610, integratedX610] <;>
    ring

set_option maxHeartbeats 8000000 in
/-- Conversely, arbitrary decic coefficients are reconstructed by taking
their nine triangular residuals as the integration constants. -/
theorem reconstructDecicCoefficients610
    (L P Q R S0 T0 U0 V0 W0 X0 A B C0 D0 E0 : F) :
    let alpha := alphaResidual610 A P
    let beta := betaResidual610 L A B Q
    let gamma := gammaResidual610 L A B C0 P R
    let delta := deltaResidual610 L A B C0 D0 P Q S0
    let epsilon := epsilonResidual610 L A B C0 D0 E0 P Q R T0
    let zeta := zetaResidual610 L A B C0 D0 E0 P Q R S0 U0
    let eta := etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0
    let theta := thetaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 W0
    let iota := iotaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 X0
    P = integratedP610 A alpha ∧
    Q = integratedQ610 L A B beta ∧
    R = integratedR610 L A B C0 alpha gamma ∧
    S0 = integratedS610 L A B C0 D0 alpha beta delta ∧
    T0 = integratedT610 L A B C0 D0 E0 alpha beta gamma epsilon ∧
    U0 = integratedU610 L A B C0 D0 E0 alpha beta gamma delta zeta ∧
    V0 = integratedV610 L A B C0 D0 E0 alpha beta gamma delta epsilon eta ∧
    W0 = integratedW610 L A B C0 D0 E0 alpha beta gamma delta epsilon zeta
      theta ∧
    X0 = integratedX610 L A B C0 D0 E0 alpha beta gamma delta epsilon zeta
      eta iota := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [alphaResidual610, betaResidual610, gammaResidual610,
      deltaResidual610, epsilonResidual610, zetaResidual610, etaResidual610,
      thetaResidual610, iotaResidual610, integratedP610, integratedQ610,
      integratedR610, integratedS610, integratedT610, integratedU610,
      integratedV610, integratedW610, integratedX610] <;>
    ring

end IntegratedDecic610

/-! ## Ground integration of the monic sextic/decic residual tower -/

section GroundIntegration610

variable {k : Type*} [Field k] [CharZero k]

/-- A ground constant is killed by the standard rational derivation. -/
theorem ratFuncDerivation68_C (a : k) :
    ratFuncDerivation68 (RatFunc.C a) = 0 := by
  have hp := ratFuncDerivation46_polynomial (C a : k[X])
  simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hp

/-- Differential constants in `k(x)` descend uniquely to the ground field. -/
theorem ratFuncDerivation68_exists_C {c : RatFunc k}
    (hc : ratFuncDerivation68 c = 0) :
    ∃ a : k, c = RatFunc.C a := by
  apply GCD369RatFuncConstantsOfPolynomialDerivative
    ratFuncDerivation46_polynomial
  simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using hc

set_option maxHeartbeats 32000000 in
/-- The nine triangular residuals of a monic constant-bracket pair, together
with the already-constant nonic coefficient, descend to the ground field. -/
theorem monicSexticDecic_residuals_exist_ground610
    (f g : (RatFunc k)[X]) (terminal : k)
    (hf_high : ∀ n, 6 < n → f.coeff n = 0) (hf6 : f.coeff 6 = 1)
    (hf5 : f.coeff 5 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : ratFuncDerivation68 (g.coeff 9) = 0)
    (hjac : differentialJacobian ratFuncDerivation68 f g =
      Polynomial.C (RatFunc.C terminal)) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota : k,
      g.coeff 9 = RatFunc.C l ∧
      alphaResidual610 (f.coeff 4) (g.coeff 8) = RatFunc.C alpha ∧
      betaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3) (g.coeff 7) =
        RatFunc.C beta ∧
      gammaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3) (f.coeff 2)
          (g.coeff 8) (g.coeff 6) = RatFunc.C gamma ∧
      deltaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3) (f.coeff 2)
          (f.coeff 1) (g.coeff 8) (g.coeff 7) (g.coeff 5) =
        RatFunc.C delta ∧
      epsilonResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3) (f.coeff 2)
          (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
          (g.coeff 4) = RatFunc.C epsilon ∧
      zetaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3) (f.coeff 2)
          (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
          (g.coeff 5) (g.coeff 3) = RatFunc.C zeta ∧
      etaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3) (f.coeff 2)
          (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
          (g.coeff 5) (g.coeff 4) (g.coeff 2) = RatFunc.C eta ∧
      thetaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3) (f.coeff 2)
          (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
          (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 1) =
        RatFunc.C theta ∧
      iotaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3) (f.coeff 2)
          (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
          (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 0) =
        RatFunc.C iota := by
  let d := ratFuncDerivation68 (k := k)
  have hcoeff (n : ℕ) (hn : n ≠ 0) :
      (differentialJacobian d f g).coeff n = 0 := by
    rw [hjac]
    simp [Polynomial.coeff_C, hn]
  have h13 := (differentialJacobian_coeff_13_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 13 (by norm_num))
  have h12 := (differentialJacobian_coeff_12_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 12 (by norm_num))
  have h11 := (differentialJacobian_coeff_11_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 11 (by norm_num))
  have h10 := (differentialJacobian_coeff_10_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 10 (by norm_num))
  have h9 := (differentialJacobian_coeff_9_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 9 (by norm_num))
  have h8 := (differentialJacobian_coeff_8_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 8 (by norm_num))
  have h7 := (differentialJacobian_coeff_7_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 7 (by norm_num))
  have h6 := (differentialJacobian_coeff_6_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 6 (by norm_num))
  have h5 := (differentialJacobian_coeff_5_monicSexticDecic d f g
    hf_high hf6 hf5 hg_high hg10 hL).symm.trans (hcoeff 5 (by norm_num))
  have halpha := alphaResidual610_deriv_zero d (f.coeff 4) (g.coeff 8)
    (by linear_combination h13)
  have hbeta := betaResidual610_deriv_zero d (g.coeff 9) (f.coeff 4)
    (f.coeff 3) (g.coeff 7) hL (by linear_combination h12)
  have hgamma := gammaResidual610_deriv_zero d (g.coeff 9) (f.coeff 4)
    (f.coeff 3) (f.coeff 2) (g.coeff 8) (g.coeff 6) hL halpha
    (by linear_combination h11)
  have hdelta := deltaResidual610_deriv_zero d (g.coeff 9) (f.coeff 4)
    (f.coeff 3) (f.coeff 2) (f.coeff 1) (g.coeff 8) (g.coeff 7)
    (g.coeff 5) hL halpha hbeta (by linear_combination h10)
  have hepsilon := epsilonResidual610_deriv_zero d (g.coeff 9) (f.coeff 4)
    (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
    (g.coeff 7) (g.coeff 6) (g.coeff 4) hL halpha hbeta hgamma
    (by linear_combination h9)
  have hzeta := zetaResidual610_deriv_zero d (g.coeff 9) (f.coeff 4)
    (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
    (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 3) hL halpha hbeta
    hgamma hdelta (by linear_combination h8)
  have heta := etaResidual610_deriv_zero d (g.coeff 9) (f.coeff 4)
    (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
    (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 2) hL
    halpha hbeta hgamma hdelta hepsilon (by linear_combination h7)
  have htheta := thetaResidual610_deriv_zero d (g.coeff 9) (f.coeff 4)
    (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
    (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
    (g.coeff 1) hL halpha hbeta hgamma hdelta hepsilon hzeta
    (by linear_combination h6)
  have hiota := iotaResidual610_deriv_zero d (g.coeff 9) (f.coeff 4)
    (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
    (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
    (g.coeff 2) (g.coeff 0) hL halpha hbeta hgamma hdelta hepsilon
    hzeta heta (by linear_combination h5)
  obtain ⟨l, hl⟩ := ratFuncDerivation68_exists_C hL
  obtain ⟨alpha, halphaC⟩ := ratFuncDerivation68_exists_C halpha
  obtain ⟨beta, hbetaC⟩ := ratFuncDerivation68_exists_C hbeta
  obtain ⟨gamma, hgammaC⟩ := ratFuncDerivation68_exists_C hgamma
  obtain ⟨delta, hdeltaC⟩ := ratFuncDerivation68_exists_C hdelta
  obtain ⟨epsilon, hepsilonC⟩ := ratFuncDerivation68_exists_C hepsilon
  obtain ⟨zeta, hzetaC⟩ := ratFuncDerivation68_exists_C hzeta
  obtain ⟨eta, hetaC⟩ := ratFuncDerivation68_exists_C heta
  obtain ⟨theta, hthetaC⟩ := ratFuncDerivation68_exists_C htheta
  obtain ⟨iota, hiotaC⟩ := ratFuncDerivation68_exists_C hiota
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    hl, halphaC, hbetaC, hgammaC, hdeltaC, hepsilonC, hzetaC, hetaC,
    hthetaC, hiotaC⟩

set_option maxHeartbeats 16000000 in
/-- Consequently every depressed decic coefficient has the integrated Faber
form with all nine integration parameters in the ground field. -/
theorem monicSexticDecic_integrate_over_ground610
    (f g : (RatFunc k)[X]) (terminal : k)
    (hf_high : ∀ n, 6 < n → f.coeff n = 0) (hf6 : f.coeff 6 = 1)
    (hf5 : f.coeff 5 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : ratFuncDerivation68 (g.coeff 9) = 0)
    (hjac : differentialJacobian ratFuncDerivation68 f g =
      Polynomial.C (RatFunc.C terminal)) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota : k,
      g.coeff 9 = RatFunc.C l ∧
      g.coeff 8 = integratedP610 (f.coeff 4) (RatFunc.C alpha) ∧
      g.coeff 7 = integratedQ610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
        (RatFunc.C beta) ∧
      g.coeff 6 = integratedR610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
        (f.coeff 2) (RatFunc.C alpha) (RatFunc.C gamma) ∧
      g.coeff 5 = integratedS610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
        (f.coeff 2) (f.coeff 1) (RatFunc.C alpha) (RatFunc.C beta)
        (RatFunc.C delta) ∧
      g.coeff 4 = integratedT610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
        (f.coeff 2) (f.coeff 1) (f.coeff 0) (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C epsilon) ∧
      g.coeff 3 = integratedU610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
        (f.coeff 2) (f.coeff 1) (f.coeff 0) (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C zeta) ∧
      g.coeff 2 = integratedV610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
        (f.coeff 2) (f.coeff 1) (f.coeff 0) (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C eta) ∧
      g.coeff 1 = integratedW610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
        (f.coeff 2) (f.coeff 1) (f.coeff 0) (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C theta) ∧
      g.coeff 0 = integratedX610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
        (f.coeff 2) (f.coeff 1) (f.coeff 0) (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
        (RatFunc.C iota) := by
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hl, halpha, hbeta, hgamma, hdelta, hepsilon, hzeta, heta, htheta,
      hiota⟩ :=
    monicSexticDecic_residuals_exist_ground610 f g terminal hf_high hf6 hf5
      hg_high hg10 hL hjac
  have hrec := reconstructDecicCoefficients610 (g.coeff 9) (g.coeff 8)
    (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
    (g.coeff 2) (g.coeff 1) (g.coeff 0) (f.coeff 4) (f.coeff 3)
    (f.coeff 2) (f.coeff 1) (f.coeff 0)
  dsimp only at hrec
  rw [halpha, hbeta, hgamma, hdelta, hepsilon, hzeta, heta, htheta, hiota]
    at hrec
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, hl,
    hrec.1, hrec.2.1, hrec.2.2.1, hrec.2.2.2.1, hrec.2.2.2.2.1,
    hrec.2.2.2.2.2.1, hrec.2.2.2.2.2.2.1, hrec.2.2.2.2.2.2.2.1,
    hrec.2.2.2.2.2.2.2.2⟩

end GroundIntegration610

/-! ## Constant free core is impossible -/

section ConstantCoreContradiction610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000 in
/-- If the free core is differentially constant and the triangular
residuals are ground constants, every integrated decic coefficient is
likewise a differential constant. -/
theorem integratedDecic_core_deriv_zero610
    (L A B C0 D0 E0 : RatFunc k)
    (alpha beta gamma delta epsilon zeta eta theta iota : k)
    (hL : ratFuncDerivation68 L = 0)
    (hA : ratFuncDerivation68 A = 0)
    (hB : ratFuncDerivation68 B = 0)
    (hC : ratFuncDerivation68 C0 = 0)
    (hD : ratFuncDerivation68 D0 = 0)
    (hE : ratFuncDerivation68 E0 = 0) :
    ratFuncDerivation68 (integratedP610 A (RatFunc.C alpha)) = 0 ∧
    ratFuncDerivation68 (integratedQ610 L A B (RatFunc.C beta)) = 0 ∧
    ratFuncDerivation68 (integratedR610 L A B C0 (RatFunc.C alpha)
      (RatFunc.C gamma)) = 0 ∧
    ratFuncDerivation68 (integratedS610 L A B C0 D0 (RatFunc.C alpha)
      (RatFunc.C beta) (RatFunc.C delta)) = 0 ∧
    ratFuncDerivation68 (integratedT610 L A B C0 D0 E0 (RatFunc.C alpha)
      (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C epsilon)) = 0 ∧
    ratFuncDerivation68 (integratedU610 L A B C0 D0 E0 (RatFunc.C alpha)
      (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
      (RatFunc.C zeta)) = 0 ∧
    ratFuncDerivation68 (integratedV610 L A B C0 D0 E0 (RatFunc.C alpha)
      (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
      (RatFunc.C epsilon) (RatFunc.C eta)) = 0 ∧
    ratFuncDerivation68 (integratedW610 L A B C0 D0 E0 (RatFunc.C alpha)
      (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
      (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C theta)) = 0 ∧
    ratFuncDerivation68 (integratedX610 L A B C0 D0 E0 (RatFunc.C alpha)
      (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
      (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
      (RatFunc.C iota)) = 0 := by
  have hConst (c : k) : ratFuncDerivation68 (RatFunc.C c) = 0 :=
    ratFuncDerivation68_C c
  have hfrac (m n : ℕ) :
      ratFuncDerivation68 ((m : RatFunc k) / (n : RatFunc k)) = 0 :=
    derivation_natDiv_zero68 ratFuncDerivation68 m n
  have h53 : ratFuncDerivation68 (5 / 3 : RatFunc k) = 0 := hfrac 5 3
  have h32 : ratFuncDerivation68 (3 / 2 : RatFunc k) = 0 := hfrac 3 2
  have h59 : ratFuncDerivation68 (5 / 9 : RatFunc k) = 0 := hfrac 5 9
  have h43 : ratFuncDerivation68 (4 / 3 : RatFunc k) = 0 := hfrac 4 3
  have h38 : ratFuncDerivation68 (3 / 8 : RatFunc k) = 0 := hfrac 3 8
  have h109 : ratFuncDerivation68 (10 / 9 : RatFunc k) = 0 := hfrac 10 9
  have h76 : ratFuncDerivation68 (7 / 6 : RatFunc k) = 0 := hfrac 7 6
  have h581 : ratFuncDerivation68 (5 / 81 : RatFunc k) = 0 := hfrac 5 81
  have h29 : ratFuncDerivation68 (2 / 9 : RatFunc k) = 0 := hfrac 2 9
  have h34 : ratFuncDerivation68 (3 / 4 : RatFunc k) = 0 := hfrac 3 4
  have h49 : ratFuncDerivation68 (4 / 9 : RatFunc k) = 0 := hfrac 4 9
  have h536 : ratFuncDerivation68 (5 / 36 : RatFunc k) = 0 := hfrac 5 36
  have h116 : ratFuncDerivation68 (1 / 16 : RatFunc k) = 0 := by
    simpa using hfrac 1 16
  have h527 : ratFuncDerivation68 (5 / 27 : RatFunc k) = 0 := hfrac 5 27
  have h772 : ratFuncDerivation68 (7 / 72 : RatFunc k) = 0 := hfrac 7 72
  have h56 : ratFuncDerivation68 (5 / 6 : RatFunc k) = 0 := hfrac 5 6
  have h316 : ratFuncDerivation68 (3 / 16 : RatFunc k) = 0 := hfrac 3 16
  have h481 : ratFuncDerivation68 (4 / 81 : RatFunc k) = 0 := hfrac 4 81
  have h5243 : ratFuncDerivation68 (5 / 243 : RatFunc k) = 0 := hfrac 5 243
  have h736 : ratFuncDerivation68 (7 / 36 : RatFunc k) = 0 := hfrac 7 36
  have h23 : ratFuncDerivation68 (2 / 3 : RatFunc k) = 0 := hfrac 2 3
  have h3128 : ratFuncDerivation68 (3 / 128 : RatFunc k) = 0 := hfrac 3 128
  have h351296 : ratFuncDerivation68 (35 / 1296 : RatFunc k) = 0 :=
    hfrac 35 1296
  have h427 : ratFuncDerivation68 (4 / 27 : RatFunc k) = 0 := hfrac 4 27
  have h20243 : ratFuncDerivation68 (20 / 243 : RatFunc k) = 0 :=
    hfrac 20 243
  have h1027 : ratFuncDerivation68 (10 / 27 : RatFunc k) = 0 := hfrac 10 27
  have h572 : ratFuncDerivation68 (5 / 72 : RatFunc k) = 0 := hfrac 5 72
  have h12 : ratFuncDerivation68 (1 / 2 : RatFunc k) = 0 := by
    simpa using hfrac 1 2
  have h7729 : ratFuncDerivation68 (7 / 729 : RatFunc k) = 0 := hfrac 7 729
  have h332 : ratFuncDerivation68 (3 / 32 : RatFunc k) = 0 := hfrac 3 32
  have h35432 : ratFuncDerivation68 (35 / 432 : RatFunc k) = 0 :=
    hfrac 35 432
  have h1081 : ratFuncDerivation68 (10 / 81 : RatFunc k) = 0 := hfrac 10 81
  have h19 : ratFuncDerivation68 (1 / 9 : RatFunc k) = 0 := by
    simpa using hfrac 1 9
  have h13 : ratFuncDerivation68 (1 / 3 : RatFunc k) = 0 := by
    simpa using hfrac 1 3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [integratedP610, integratedQ610, integratedR610,
      integratedS610, integratedT610, integratedU610, integratedV610,
      integratedW610, integratedX610, map_add, map_sub, map_neg,
      Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul,
      smul_eq_mul, hL, hA, hB, hC, hD, hE, hConst, h53, h32, h59, h43, h38,
      h109, h76, h581, h29, h34, h49, h536, h116, h527, h772, h56, h316,
      h481, h5243, h736, h23, h3128, h351296, h427, h20243, h1027, h572,
      h12, h7729, h332, h35432, h1081, h19, h13, zero_mul, mul_zero,
      add_zero,
      zero_add, sub_zero, neg_zero]

set_option maxHeartbeats 32000000 in
/-- A monic constant-bracket pair whose free core is differentially
constant cannot have a nonzero terminal constant.  The integrated
trajectory makes the weight-fifteen primitive a differential constant,
contradicting `primitive' = terminal ≠ 0`. -/
theorem monicSexticDecic_false_of_core_deriv_zero610
    (f g : (RatFunc k)[X]) (terminal : k)
    (hf_high : ∀ n, 6 < n → f.coeff n = 0) (hf6 : f.coeff 6 = 1)
    (hf5 : f.coeff 5 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : ratFuncDerivation68 (g.coeff 9) = 0)
    (hjac : differentialJacobian ratFuncDerivation68 f g =
      Polynomial.C (RatFunc.C terminal))
    (hterminal : terminal ≠ 0)
    (hA : ratFuncDerivation68 (f.coeff 4) = 0)
    (hB : ratFuncDerivation68 (f.coeff 3) = 0)
    (hC : ratFuncDerivation68 (f.coeff 2) = 0)
    (hD : ratFuncDerivation68 (f.coeff 1) = 0)
    (hE : ratFuncDerivation68 (f.coeff 0) = 0) :
    False := by
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hl, hP, hQ, hR, hS, hT, hU, hV, hW, hX⟩ :=
    monicSexticDecic_integrate_over_ground610 f g terminal hf_high hf6 hf5
      hg_high hg10 hL hjac
  have hcore := integratedDecic_core_deriv_zero610 (g.coeff 9) (f.coeff 4)
    (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) alpha beta gamma delta
    epsilon zeta eta theta iota (by simpa [hl] using ratFuncDerivation68_C l)
    hA hB hC hD hE
  have hP0 : ratFuncDerivation68 (g.coeff 8) = 0 := by
    rw [hP]; exact hcore.1
  have hQ0 : ratFuncDerivation68 (g.coeff 7) = 0 := by
    rw [hQ]; exact hcore.2.1
  have hR0 : ratFuncDerivation68 (g.coeff 6) = 0 := by
    rw [hR]; exact hcore.2.2.1
  have hS0 : ratFuncDerivation68 (g.coeff 5) = 0 := by
    rw [hS]; exact hcore.2.2.2.1
  have hT0 : ratFuncDerivation68 (g.coeff 4) = 0 := by
    rw [hT]; exact hcore.2.2.2.2.1
  have hU0 : ratFuncDerivation68 (g.coeff 3) = 0 := by
    rw [hU]; exact hcore.2.2.2.2.2.1
  have hV0 : ratFuncDerivation68 (g.coeff 2) = 0 := by
    rw [hV]; exact hcore.2.2.2.2.2.2.1
  have hW0 : ratFuncDerivation68 (g.coeff 1) = 0 := by
    rw [hW]; exact hcore.2.2.2.2.2.2.2.1
  have hX0 : ratFuncDerivation68 (g.coeff 0) = 0 := by
    rw [hX]; exact hcore.2.2.2.2.2.2.2.2
  have hprim :
      ratFuncDerivation68
          (degreeZeroPrimitive610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
            (g.coeff 1) (g.coeff 0)) =
        RatFunc.C terminal := by
    simpa only [ratFuncDerivation68, ratFuncDerivation46_apply] using
      degreeZeroPrimitive610_deriv_eq_constant_of_monic_differentialJacobian
        ratFuncDerivation68 f g (RatFunc.C terminal) hf_high hf6 hf5
        hg_high hg10 hL hjac
  have hcoeff (n : ℕ) (hn : n ≠ 0) :
      (differentialJacobian ratFuncDerivation68 f g).coeff n = 0 := by
    rw [hjac]
    simp [Polynomial.coeff_C, hn]
  have h13 := (differentialJacobian_coeff_13_monicSexticDecic
    ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hL).symm.trans
    (hcoeff 13 (by norm_num))
  have h12 := (differentialJacobian_coeff_12_monicSexticDecic
    ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hL).symm.trans
    (hcoeff 12 (by norm_num))
  have h11 := (differentialJacobian_coeff_11_monicSexticDecic
    ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hL).symm.trans
    (hcoeff 11 (by norm_num))
  have h10 := (differentialJacobian_coeff_10_monicSexticDecic
    ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hL).symm.trans
    (hcoeff 10 (by norm_num))
  have h9 := (differentialJacobian_coeff_9_monicSexticDecic
    ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hL).symm.trans
    (hcoeff 9 (by norm_num))
  have h8 := (differentialJacobian_coeff_8_monicSexticDecic
    ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hL).symm.trans
    (hcoeff 8 (by norm_num))
  have h7 := (differentialJacobian_coeff_7_monicSexticDecic
    ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hL).symm.trans
    (hcoeff 7 (by norm_num))
  have h6 := (differentialJacobian_coeff_6_monicSexticDecic
    ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hL).symm.trans
    (hcoeff 6 (by norm_num))
  have h5 := (differentialJacobian_coeff_5_monicSexticDecic
    ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hL).symm.trans
    (hcoeff 5 (by norm_num))
  have h4 := (differentialJacobian_coeff_4_monicSexticDecic
    ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hL).symm.trans
    (hcoeff 4 (by norm_num))
  have h3 := (differentialJacobian_coeff_3_monicSexticDecic
    ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hL).symm.trans
    (hcoeff 3 (by norm_num))
  have h2 := (differentialJacobian_coeff_2_monicSexticDecic
    ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hL).symm.trans
    (hcoeff 2 (by norm_num))
  have hrow := degreeZeroPrimitive610_deriv_eq_row_of_depressed_rows
    ratFuncDerivation68 (g.coeff 9) (f.coeff 4) (f.coeff 3) (f.coeff 2)
    (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
    (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1)
    (g.coeff 0) hL (by linear_combination h13) (by linear_combination h12)
    (by linear_combination h11) (by linear_combination h10)
    (by linear_combination h9) (by linear_combination h8)
    (by linear_combination h7) (by linear_combination h6)
    (by linear_combination h5) (by linear_combination h4)
    (by linear_combination h3) (by linear_combination h2)
  have hzero :
      ratFuncDerivation68
          (degreeZeroPrimitive610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
            (g.coeff 1) (g.coeff 0)) = 0 := by
    rw [hrow, hE, hX0]
    ring
  have : RatFunc.C terminal = (0 : RatFunc k) := hprim.symm.trans hzero
  exact hterminal (RatFunc.C_injective (this.trans (map_zero RatFunc.C).symm))

end ConstantCoreContradiction610

/-! ## Source-facing monic bracket and integrated trajectory -/

section SourceValuationEndgame610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 16000000 in
/-- Constant-scale monic depression of a normalized `(6,10)` source: the
affine-depressed pair is a monic sextic/decic with constant nonic
coefficient and constant outer Jacobian `j / t`. -/
theorem scaleZero_exists_monicDepressedBracket_610
    {p q : k[X][X]} {j t lambda : k} {H : k[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * (Polynomial.C t) ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    let hRF : RatFunc k := RatFunc.C t
    let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
    let f : (RatFunc k)[X] :=
      affineDepress68 hRF (sexticDepressionR610 hRF a5)
        (sourceToRatFunc68 p)
    let g : (RatFunc k)[X] :=
      affineDepress68 hRF (sexticDepressionR610 hRF a5)
        (sourceToRatFunc68 q)
    (∀ n, 6 < n → f.coeff n = 0) ∧
      f.coeff 6 = 1 ∧
      f.coeff 5 = 0 ∧
      (∀ n, 10 < n → g.coeff n = 0) ∧
      g.coeff 10 = 1 ∧
      ratFuncDerivation68 (g.coeff 9) = 0 ∧
      differentialJacobian ratFuncDerivation68 f g =
        Polynomial.C (RatFunc.C (j / t)) := by
  dsimp only
  let hRF : RatFunc k := RatFunc.C t
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5)
      (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5)
      (sourceToRatFunc68 q)
  have hh : hRF ≠ 0 := by
    intro hzero
    apply ht
    apply RatFunc.C_injective
    simpa only [hRF, map_zero] using hzero
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 6) = hRF ^ 6 := by
    simp only [hp6, hH, hRF, map_pow, RatFunc.algebraMap_C]
    ring
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = hRF ^ 10 := by
    simp only [hq10, hH, hRF, map_pow, RatFunc.algebraMap_C]
    ring
  have hpDep := affineDepress_sourceSextic68 p hRF
    (sexticDepressionR610 hRF a5) hp hh hpTop rfl
  have hNrat :
      5 * a5 * hRF ^ 4 - 3 * b9 = RatFunc.C lambda * hRF ^ 9 := by
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hN
    have hH2 : algebraMap k[X] (RatFunc k) (H ^ 2) = hRF ^ 4 := by
      simp only [hH, hRF, map_pow, RatFunc.algebraMap_C]
      ring
    have hh9 : algebraMap k[X] (RatFunc k) ((Polynomial.C t) ^ 9) =
        hRF ^ 9 := by
      simp only [hRF, map_pow, RatFunc.algebraMap_C]
    have hleft : algebraMap k[X] (RatFunc k)
        ((5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9) =
        5 * a5 * hRF ^ 4 - 3 * b9 := by
      simp only [map_sub, map_mul, map_ofNat, a5, b9, hH2]
    have hright : algebraMap k[X] (RatFunc k)
        (Polynomial.C lambda * (Polynomial.C t) ^ 9) =
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
  have hg_high_src : ∀ n, 10 < n →
      (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = hRF ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, _hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src
  have hg9L : g.coeff 9 =
      depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
    dsimp only [g]
    rw [hg9]
    simp [depressedL610, depressedL810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9]
  have hg9const : g.coeff 9 = RatFunc.C (-lambda / 3) := by
    rw [hg9L, hLval]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hg9const]
    exact ratFuncDerivation68_C (-lambda / 3)
  have hdiv : RatFunc.C j / hRF = RatFunc.C (j / t) := by
    simp only [hRF, map_div₀]
  refine ⟨hf_high, hf6, hf5, hg_high, hg10, hLconst, ?_⟩
  simpa only [f, g, hdiv] using hbracket

set_option maxHeartbeats 16000000 in
/-- Source-facing integrated polynomial trajectory of a normalized
scale-zero `(6,10)` pair: the decic coordinates are the nine triangular
Faber integrals of the free core against ground constants, and the
weight-fifteen primitive differentiates to the nonzero constant `j / t`.
The degree-one residual `ο` is preserved. -/
theorem normalized610ScaleZero_exists_integratedTrajectory
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota : k),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
      nonzeroLocalClearedFourteenthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          (Polynomial.C lambda) =
        Polynomial.C omicron ∧
      let hRF : RatFunc k := RatFunc.C t
      let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
      let f : (RatFunc k)[X] :=
        affineDepress68 hRF (sexticDepressionR610 hRF a5)
          (sourceToRatFunc68 p)
      let g : (RatFunc k)[X] :=
        affineDepress68 hRF (sexticDepressionR610 hRF a5)
          (sourceToRatFunc68 q)
      g.coeff 9 = RatFunc.C l ∧
        g.coeff 8 = integratedP610 (f.coeff 4) (RatFunc.C alpha) ∧
        g.coeff 7 = integratedQ610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (RatFunc.C beta) ∧
        g.coeff 6 = integratedR610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (RatFunc.C alpha) (RatFunc.C gamma) ∧
        g.coeff 5 = integratedS610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (RatFunc.C alpha) (RatFunc.C beta)
          (RatFunc.C delta) ∧
        g.coeff 4 = integratedT610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C epsilon) ∧
        g.coeff 3 = integratedU610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
          (RatFunc.C zeta) ∧
        g.coeff 2 = integratedV610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
          (RatFunc.C epsilon) (RatFunc.C eta) ∧
        g.coeff 1 = integratedW610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
          (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C theta) ∧
        g.coeff 0 = integratedX610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
          (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
          (RatFunc.C iota) ∧
        Differential.deriv
            (degreeZeroPrimitive610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
              (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
              (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
              (g.coeff 1) (g.coeff 0)) =
          RatFunc.C (j / t) := by
  dsimp only
  obtain ⟨t, j, lambda, omicron, ht, hj, hHsq, hrow, homicron, hprim⟩ :=
    normalized610ScaleZero_exists_degreeZeroPrimitive hsource
  rcases hsource with
    ⟨_hH, _hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j', _hj', hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j') := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  have hj' : j' = j := by
    have hsrc :
        (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j' :=
      scaleZeroRaw_fifteenthCoefficientJacobianRow_610 hjac
    have : Polynomial.C j' = Polynomial.C j := hsrc.symm.trans hrow
    exact Polynomial.C_injective this
  obtain ⟨lambdaN, _a, _g0, _d0, _e, _z, _et, _th, _iot, _ka, _mu, _nu, _xi,
      _omicron0, hN, _hM, _hT, _hU, _hV, _hW, _hX, _hY, _hI, _hZ, _hJ, _hnu,
      _hxi, _homicron⟩ :=
    scaleZero_degreeOneClearedDefect_exists_C_610 hp hq hD ht hHsq
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)
  have hD' : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa [hj'] using hD
  have hmonic :=
    scaleZero_exists_monicDepressedBracket_610 hp hq ht hHsq
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)
      (by simpa only [p, q] using hN) hD'
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hl, hPint, hQint, hRint, hSint, hTint, hUint, hVint, hWint, hXint⟩ :=
    monicSexticDecic_integrate_over_ground610
      (affineDepress68 (RatFunc.C t)
        (sexticDepressionR610 (RatFunc.C t)
          (algebraMap k[X] (RatFunc k) (p.coeff 5)))
        (sourceToRatFunc68 p))
      (affineDepress68 (RatFunc.C t)
        (sexticDepressionR610 (RatFunc.C t)
          (algebraMap k[X] (RatFunc k) (p.coeff 5)))
        (sourceToRatFunc68 q))
      (j / t) hmonic.1 hmonic.2.1 hmonic.2.2.1 hmonic.2.2.2.1
      hmonic.2.2.2.2.1 hmonic.2.2.2.2.2.1 hmonic.2.2.2.2.2.2
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, ht, hj, div_ne_zero hj ht, hHsq, hrow,
    homicron, ?_⟩
  exact ⟨hl, hPint, hQint, hRint, hSint, hTint, hUint, hVint, hWint, hXint,
    hprim⟩

/-- Constant-core exclusion on a supplied monic pair: if every depressed
free-core letter is a differential constant, the last row collapses to
`0 = j / t`. -/
theorem scaleZero_false_of_constant_depressed_core_610
    {p q : k[X][X]} {j t lambda : k} {H : k[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (ht : t ≠ 0) (hj : j ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * (Polynomial.C t) ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hA :
      let hRF : RatFunc k := RatFunc.C t
      let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
      let f : (RatFunc k)[X] :=
        affineDepress68 hRF (sexticDepressionR610 hRF a5)
          (sourceToRatFunc68 p)
      ratFuncDerivation68 (f.coeff 4) = 0)
    (hB :
      let hRF : RatFunc k := RatFunc.C t
      let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
      let f : (RatFunc k)[X] :=
        affineDepress68 hRF (sexticDepressionR610 hRF a5)
          (sourceToRatFunc68 p)
      ratFuncDerivation68 (f.coeff 3) = 0)
    (hC :
      let hRF : RatFunc k := RatFunc.C t
      let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
      let f : (RatFunc k)[X] :=
        affineDepress68 hRF (sexticDepressionR610 hRF a5)
          (sourceToRatFunc68 p)
      ratFuncDerivation68 (f.coeff 2) = 0)
    (hDcore :
      let hRF : RatFunc k := RatFunc.C t
      let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
      let f : (RatFunc k)[X] :=
        affineDepress68 hRF (sexticDepressionR610 hRF a5)
          (sourceToRatFunc68 p)
      ratFuncDerivation68 (f.coeff 1) = 0)
    (hE :
      let hRF : RatFunc k := RatFunc.C t
      let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
      let f : (RatFunc k)[X] :=
        affineDepress68 hRF (sexticDepressionR610 hRF a5)
          (sourceToRatFunc68 p)
      ratFuncDerivation68 (f.coeff 0) = 0) :
    False := by
  have hmonic :=
    scaleZero_exists_monicDepressedBracket_610 hp hq ht hH hp6 hq10 hN hD
  exact monicSexticDecic_false_of_core_deriv_zero610
    (affineDepress68 (RatFunc.C t)
      (sexticDepressionR610 (RatFunc.C t)
        (algebraMap k[X] (RatFunc k) (p.coeff 5)))
      (sourceToRatFunc68 p))
    (affineDepress68 (RatFunc.C t)
      (sexticDepressionR610 (RatFunc.C t)
        (algebraMap k[X] (RatFunc k) (p.coeff 5)))
      (sourceToRatFunc68 q))
    (j / t) hmonic.1 hmonic.2.1 hmonic.2.2.1 hmonic.2.2.2.1
    hmonic.2.2.2.2.1 hmonic.2.2.2.2.2.1 hmonic.2.2.2.2.2.2
    (div_ne_zero hj ht) hA hB hC hDcore hE

/-- The degree-one packet's exact residual selector
`6291456 p₀ q₃ h⁶²` remains available on the integrated trajectory. -/
theorem normalized610ScaleZero_twelfthSourceResidual_preserved_valuation
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda xi : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let h0 := Polynomial.C t
      (6291456 : k[X]) * p.coeff 0 * q.coeff 3 * h0 ^ 62 =
        Polynomial.C xi -
          (localClearedThirteenthDefect610 h0 (p.coeff 5) (p.coeff 4)
              (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
              (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
              (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
              lambda -
            (6291456 : k[X]) * p.coeff 0 * q.coeff 3 * h0 ^ 62) :=
  normalized610ScaleZero_twelfthSourceResidual_preserved hsource

/-- Honest residual of the scale-zero valuation endgame.

The nine triangular Faber coordinates of the depressed decic are
reconstructed from ground constants.  The remaining free core is
`(A, B, C₀, D₀, E₀)`.  The weight-fifteen primitive of that trajectory
has derivative `C (j / t) ≠ 0`.  If every free-core letter is a
differential constant, the chamber is empty.

The leaf is not closed.  A nonconstant polynomial core is still
compatible with the integrated identities as written.  The missing
input for `normalized610ScaleZero`-style `False` is the remaining
Newton-degree / leading-term comparison of `(A, B, C₀, D₀, E₀)` against
the already-constant lower first integrals `κ, λ, μ` (and the weight-
seventy residual `ο`) together with the inhomogeneous identity that
the primitive is linear. -/
theorem normalized610ScaleZero_valuationEndgameResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota : k),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
      nonzeroLocalClearedFourteenthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          (Polynomial.C lambda) =
        Polynomial.C omicron ∧
      let hRF : RatFunc k := RatFunc.C t
      let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
      let f : (RatFunc k)[X] :=
        affineDepress68 hRF (sexticDepressionR610 hRF a5)
          (sourceToRatFunc68 p)
      let g : (RatFunc k)[X] :=
        affineDepress68 hRF (sexticDepressionR610 hRF a5)
          (sourceToRatFunc68 q)
      g.coeff 9 = RatFunc.C l ∧
        g.coeff 8 = integratedP610 (f.coeff 4) (RatFunc.C alpha) ∧
        g.coeff 7 = integratedQ610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (RatFunc.C beta) ∧
        g.coeff 6 = integratedR610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (RatFunc.C alpha) (RatFunc.C gamma) ∧
        g.coeff 5 = integratedS610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (RatFunc.C alpha) (RatFunc.C beta)
          (RatFunc.C delta) ∧
        g.coeff 4 = integratedT610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C epsilon) ∧
        g.coeff 3 = integratedU610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
          (RatFunc.C zeta) ∧
        g.coeff 2 = integratedV610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
          (RatFunc.C epsilon) (RatFunc.C eta) ∧
        g.coeff 1 = integratedW610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
          (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C theta) ∧
        g.coeff 0 = integratedX610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (RatFunc.C alpha)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
          (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
          (RatFunc.C iota) ∧
        Differential.deriv
            (degreeZeroPrimitive610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
              (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
              (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
              (g.coeff 1) (g.coeff 0)) =
          RatFunc.C (j / t) :=
  normalized610ScaleZero_exists_integratedTrajectory hsource

end SourceValuationEndgame610

#print axioms integratedP610
#print axioms integratedQ610
#print axioms integratedR610
#print axioms integratedS610
#print axioms integratedT610
#print axioms integratedU610
#print axioms integratedV610
#print axioms integratedW610
#print axioms integratedX610
#print axioms integratedResiduals610
#print axioms reconstructDecicCoefficients610
#print axioms ratFuncDerivation68_C
#print axioms ratFuncDerivation68_exists_C
#print axioms monicSexticDecic_residuals_exist_ground610
#print axioms monicSexticDecic_integrate_over_ground610
#print axioms integratedDecic_core_deriv_zero610
#print axioms monicSexticDecic_false_of_core_deriv_zero610
#print axioms scaleZero_exists_monicDepressedBracket_610
#print axioms normalized610ScaleZero_exists_integratedTrajectory
#print axioms scaleZero_false_of_constant_depressed_core_610
#print axioms normalized610ScaleZero_twelfthSourceResidual_preserved_valuation
#print axioms normalized610ScaleZero_valuationEndgameResidual

end Max11DegreeRoutes
