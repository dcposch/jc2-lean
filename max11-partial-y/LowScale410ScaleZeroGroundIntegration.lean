import LowScale410ScaleZeroEarlyLoadElimination

/-!
# Ground integration of the depressed `(4,10)` upper rows

The ten coefficients of a depressed decic integrate triangularly over
`k(x)`.  This file supplies the missing mechanical bridge: `L` and the nine
successive Faber residuals descend to arbitrary ground constants.  No load
is assumed or proved to vanish.
-/

noncomputable section

set_option maxHeartbeats 5000000

open Polynomial

namespace Max11DegreeRoutes

section GroundIntegration410

variable {k : Type*} [Field k] [CharZero k]

/-- Coefficientwise derivative of the depressed decic before imposing
constancy of its nonic coefficient. -/
theorem coefficientDeriv_depressedDecic410_full
    (d : Derivation k (RatFunc k) (RatFunc k))
    (L P Q R S T U V W Z : RatFunc k) :
    coefficientDeriv d (depressedDecic410 L P Q R S T U V W Z) =
      C (d L) * X ^ 9 + C (d P) * X ^ 8 + C (d Q) * X ^ 7 +
      C (d R) * X ^ 6 + C (d S) * X ^ 5 + C (d T) * X ^ 4 +
      C (d U) * X ^ 3 + C (d V) * X ^ 2 + C (d W) * X + C (d Z) := by
  ext n
  simp [depressedDecic410, Polynomial.coeff_X, Polynomial.coeff_C]
  split_ifs <;> simp_all

/-- The omitted top row of the displayed `(4,10)` normal form: a constant
bracket forces the nonic coefficient `L` to be a differential constant. -/
theorem depressedL_deriv_zero410
    (L P Q R S T U V W Z A B C0 terminal : RatFunc k)
    (hbracket : differentialJacobian ratFuncDerivation46
      (depressedQuartic46 A B C0)
      (depressedDecic410 L P Q R S T U V W Z) = C terminal) :
    ratFuncDerivation46 L = 0 := by
  have h12 := congrArg (fun f : (RatFunc k)[X] => f.coeff 12) hbracket
  rw [differentialJacobian, coefficientDeriv_depressedQuartic46,
    coefficientDeriv_depressedDecic410_full] at h12
  simp only [Polynomial.coeff_sub, Polynomial.coeff_mul, coeff_C,
    show (12 : ℕ) ≠ 0 by norm_num, if_false] at h12
  have hanti : (Finset.HasAntidiagonal.antidiagonal 12 :
      Finset (ℕ × ℕ)) =
      ({(0, 12), (1, 11), (2, 10), (3, 9), (4, 8), (5, 7), (6, 6),
        (7, 5), (8, 4), (9, 3), (10, 2), (11, 1), (12, 0)} :
        Finset (ℕ × ℕ)) := by decide
  rw [hanti] at h12
  norm_num [depressedQuartic46, depressedDecic410,
    Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_X,
    Polynomial.derivative_C, coeff_add, coeff_C, coeff_C_mul,
    coeff_mul_X_pow', coeff_X, coeff_X_pow] at h12
  exact h12

/-- All ten depressed decic coefficients have the integrated Faber form over
ground constants.  The constants are arbitrary: this theorem contains no
wall or vanishing assertion. -/
theorem depressedCoefficients_integrate_over_ground410
    (L P Q R S T U V W Z A B C0 terminal : RatFunc k)
    (hbracket : differentialJacobian ratFuncDerivation46
      (depressedQuartic46 A B C0)
      (depressedDecic410 L P Q R S T U V W Z) = C terminal) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota : k,
      L = RatFunc.C l ∧
      P = integratedP410 A (RatFunc.C alpha) ∧
      Q = integratedQ410 (RatFunc.C l) A B (RatFunc.C beta) ∧
      R = integratedR410 (RatFunc.C l) A B C0
        (RatFunc.C alpha) (RatFunc.C gamma) ∧
      S = integratedS410 (RatFunc.C l) A B C0
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C delta) ∧
      T = integratedT410 (RatFunc.C l) A B C0
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C epsilon) ∧
      U = integratedU410 (RatFunc.C l) A B C0
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C zeta) ∧
      V = integratedV410 (RatFunc.C l) A B C0
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C eta) ∧
      W = integratedW410 (RatFunc.C l) A B C0
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
        (RatFunc.C theta) ∧
      Z = integratedZ410 (RatFunc.C l) A B C0
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
        (RatFunc.C eta) (RatFunc.C iota) := by
  let d := ratFuncDerivation46 (k := k)
  have hLderiv : d L = 0 := depressedL_deriv_zero410
    L P Q R S T U V W Z A B C0 terminal hbracket
  have descend (c : RatFunc k) (hc : d c = 0) :
      ∃ a : k, c = RatFunc.C a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [d, ratFuncDerivation46_apply] using hc
  obtain ⟨l, hL⟩ := descend L hLderiv
  have hconst (c : k) : d (RatFunc.C c) = 0 := by
    have hp := ratFuncDerivation46_polynomial (C c : k[X])
    simpa [d, RatFunc.algebraMap_C] using hp
  have hn2 : d (2 : RatFunc k) = 0 := d.map_natCast 2
  have hn16 : d (16 : RatFunc k) = 0 := d.map_natCast 16
  have h12 : d (1 / 2 : RatFunc k) = 0 := by
    simp [Derivation.leibniz_inv, hn2]
  have h32 : d (3 / 2 : RatFunc k) = 0 := derivation_natDiv_zero68 d 3 2
  have h52 : d (5 / 2 : RatFunc k) = 0 := derivation_natDiv_zero68 d 5 2
  have h34 : d (3 / 4 : RatFunc k) = 0 := derivation_natDiv_zero68 d 3 4
  have h54 : d (5 / 4 : RatFunc k) = 0 := derivation_natDiv_zero68 d 5 4
  have h74 : d (7 / 4 : RatFunc k) = 0 := derivation_natDiv_zero68 d 7 4
  have h94 : d (9 / 4 : RatFunc k) = 0 := derivation_natDiv_zero68 d 9 4
  have h154 : d (15 / 4 : RatFunc k) = 0 := derivation_natDiv_zero68 d 15 4
  have h38 : d (3 / 8 : RatFunc k) = 0 := derivation_natDiv_zero68 d 3 8
  have h158 : d (15 / 8 : RatFunc k) = 0 := derivation_natDiv_zero68 d 15 8
  have h116 : d (1 / 16 : RatFunc k) = 0 := by
    simp [Derivation.leibniz_inv, hn16]
  have h516 : d (5 / 16 : RatFunc k) = 0 := derivation_natDiv_zero68 d 5 16
  have h1516 : d (15 / 16 : RatFunc k) = 0 :=
    derivation_natDiv_zero68 d 15 16
  have h2116 : d (21 / 16 : RatFunc k) = 0 :=
    derivation_natDiv_zero68 d 21 16
  have h4516 : d (45 / 16 : RatFunc k) = 0 :=
    derivation_natDiv_zero68 d 45 16
  have h532 : d (5 / 32 : RatFunc k) = 0 := derivation_natDiv_zero68 d 5 32
  have h2132 : d (21 / 32 : RatFunc k) = 0 :=
    derivation_natDiv_zero68 d 21 32
  have h4532 : d (45 / 32 : RatFunc k) = 0 :=
    derivation_natDiv_zero68 d 45 32
  have h1564 : d (15 / 64 : RatFunc k) = 0 :=
    derivation_natDiv_zero68 d 15 64
  have h4564 : d (45 / 64 : RatFunc k) = 0 :=
    derivation_natDiv_zero68 d 45 64
  have h7128 : d (7 / 128 : RatFunc k) = 0 :=
    derivation_natDiv_zero68 d 7 128
  have h5128 : d (5 / 128 : RatFunc k) = 0 :=
    derivation_natDiv_zero68 d 5 128
  have h15128 : d (15 / 128 : RatFunc k) = 0 :=
    derivation_natDiv_zero68 d 15 128
  have h21128 : d (21 / 128 : RatFunc k) = 0 :=
    derivation_natDiv_zero68 d 21 128
  have h45128 : d (45 / 128 : RatFunc k) = 0 :=
    derivation_natDiv_zero68 d 45 128
  have h3256 : d (3 / 256 : RatFunc k) = 0 :=
    derivation_natDiv_zero68 d 3 256
  have h45512 : d (45 / 512 : RatFunc k) = 0 :=
    derivation_natDiv_zero68 d 45 512
  have h452048 : d (45 / 2048 : RatFunc k) = 0 :=
    derivation_natDiv_zero68 d 45 2048
  have hn5128 : d (-5 / 128 : RatFunc k) = 0 := by
    have heq : (-5 / 128 : RatFunc k) = -(5 / 128 : RatFunc k) := by ring
    rw [heq, map_neg, h5128, neg_zero]
  have hn452048 : d (-45 / 2048 : RatFunc k) = 0 := by
    have heq : (-45 / 2048 : RatFunc k) = -(45 / 2048 : RatFunc k) := by ring
    rw [heq, map_neg, h452048, neg_zero]
  have hn45512 : d (-45 / 512 : RatFunc k) = 0 := by
    have heq : (-45 / 512 : RatFunc k) = -(45 / 512 : RatFunc k) := by ring
    rw [heq, map_neg, h45512, neg_zero]
  have hn532 : d (-5 / 32 : RatFunc k) = 0 := by
    have heq : (-5 / 32 : RatFunc k) = -(5 / 32 : RatFunc k) := by ring
    rw [heq, map_neg, h532, neg_zero]
  have hn116 : d (-1 / 16 : RatFunc k) = 0 := by
    have heq : (-1 / 16 : RatFunc k) = -(1 / 16 : RatFunc k) := by ring
    rw [heq, map_neg, h116, neg_zero]
  have hn1564 : d (-15 / 64 : RatFunc k) = 0 := by
    have heq : (-15 / 64 : RatFunc k) = -(15 / 64 : RatFunc k) := by ring
    rw [heq, map_neg, h1564, neg_zero]
  have hn21128 : d (-21 / 128 : RatFunc k) = 0 := by
    have heq : (-21 / 128 : RatFunc k) = -(21 / 128 : RatFunc k) := by ring
    rw [heq, map_neg, h21128, neg_zero]
  have hb := hbracket
  rw [differentialJacobian_depressed410_eq d L P Q R S T U V W Z
    A B C0 hLderiv] at hb
  have h11 := congrArg (fun f : (RatFunc k)[X] => f.coeff 11) hb
  have h10 := congrArg (fun f : (RatFunc k)[X] => f.coeff 10) hb
  have h9 := congrArg (fun f : (RatFunc k)[X] => f.coeff 9) hb
  have h8 := congrArg (fun f : (RatFunc k)[X] => f.coeff 8) hb
  have h7 := congrArg (fun f : (RatFunc k)[X] => f.coeff 7) hb
  have h6 := congrArg (fun f : (RatFunc k)[X] => f.coeff 6) hb
  have h5 := congrArg (fun f : (RatFunc k)[X] => f.coeff 5) hb
  have h4 := congrArg (fun f : (RatFunc k)[X] => f.coeff 4) hb
  have h3 := congrArg (fun f : (RatFunc k)[X] => f.coeff 3) hb
  norm_num [coeff_add, coeff_C, coeff_C_mul, coeff_mul_X_pow', coeff_X,
    coeff_X_pow] at h11 h10 h9 h8 h7 h6 h5 h4 h3
  rw [hL] at h10 h9 h8
  let alphaR : RatFunc k := P - (5 / 2 : RatFunc k) * A
  have halphaD : d alphaR = 0 := by
    dsimp only [alphaR]
    simp [Derivation.leibniz, h52]
    linear_combination (-1 / 4 : RatFunc k) * h11
  obtain ⟨alpha, halpha⟩ := descend alphaR halphaD
  have hP : P = integratedP410 A (RatFunc.C alpha) := by
    rw [← halpha]
    simp only [alphaR, integratedP410]
    ring
  let betaR : RatFunc k := Q -
    ((9 / 4 : RatFunc k) * RatFunc.C l * A + (5 / 2 : RatFunc k) * B)
  have hbetaD : d betaR = 0 := by
    dsimp only [betaR]
    simp [Derivation.leibniz, hconst, h52, h94]
    linear_combination (-1 / 4 : RatFunc k) * h10
  obtain ⟨beta, hbeta⟩ := descend betaR hbetaD
  have hQ : Q = integratedQ410 (RatFunc.C l) A B (RatFunc.C beta) := by
    rw [← hbeta]
    simp only [betaR, integratedQ410]
    ring
  let gammaR : RatFunc k := R - integratedR410 (RatFunc.C l) A B C0
    (RatFunc.C alpha) 0
  have hgammaD : d gammaR = 0 := by
    rw [hP] at h9
    dsimp only [gammaR, integratedR410, integratedP410] at h9 ⊢
    simp [Derivation.leibniz, Derivation.leibniz_pow, hconst, hn2, h52, h94,
      h158] at h9 ⊢
    linear_combination (-1 / 4 : RatFunc k) * h9
  obtain ⟨gamma, hgamma⟩ := descend gammaR hgammaD
  have hR : R = integratedR410 (RatFunc.C l) A B C0
      (RatFunc.C alpha) (RatFunc.C gamma) := by
    rw [← hgamma]
    simp only [gammaR, integratedR410]
    ring
  let deltaR : RatFunc k := S - integratedS410 (RatFunc.C l) A B C0
    (RatFunc.C alpha) (RatFunc.C beta) 0
  have hdeltaD : d deltaR = 0 := by
    rw [hP, hQ] at h8
    dsimp only [deltaR, integratedS410, integratedP410,
      integratedQ410] at h8 ⊢
    simp [Derivation.leibniz, Derivation.leibniz_pow, hconst, hn2, h52, h74,
      h94, h154, h4532] at h8 ⊢
    linear_combination (-1 / 4 : RatFunc k) * h8
  obtain ⟨delta, hdelta⟩ := descend deltaR hdeltaD
  have hS : S = integratedS410 (RatFunc.C l) A B C0
      (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C delta) := by
    rw [← hdelta]
    simp only [deltaR, integratedS410]
    ring
  let epsilonR : RatFunc k := T - integratedT410 (RatFunc.C l) A B C0
    (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma) 0
  have hepsilonD : d epsilonR = 0 := by
    rw [hP, hQ, hR] at h7
    dsimp only [epsilonR, integratedT410, integratedP410, integratedQ410,
      integratedR410] at h7 ⊢
    simp [Derivation.leibniz, Derivation.leibniz_pow, hconst, hn2, h32, h52,
      h74, h94, h154, h158, h516, h4516] at h7 ⊢
    linear_combination (-1 / 4 : RatFunc k) * h7
  obtain ⟨epsilon, hepsilon⟩ := descend epsilonR hepsilonD
  have hT : T = integratedT410 (RatFunc.C l) A B C0
      (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
      (RatFunc.C epsilon) := by
    rw [← hepsilon]
    simp only [epsilonR, integratedT410]
    ring
  let zetaR : RatFunc k := U - integratedU410 (RatFunc.C l) A B C0
    (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
    (RatFunc.C delta) 0
  have hzetaD : d zetaR = 0 := by
    rw [hQ, hR, hS] at h6
    dsimp only [zetaR, integratedU410, integratedQ410, integratedR410,
      integratedS410] at h6 ⊢
    simp [Derivation.leibniz, Derivation.leibniz_pow, hconst, hn2, h32, h52,
      h54, h74, h94, h154, h158, h1516, h2132, h4516, h4532,
      h15128] at h6 ⊢
    linear_combination (-1 / 4 : RatFunc k) * h6
  obtain ⟨zeta, hzeta⟩ := descend zetaR hzetaD
  have hU : U = integratedU410 (RatFunc.C l) A B C0
      (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
      (RatFunc.C delta) (RatFunc.C zeta) := by
    rw [← hzeta]
    simp only [zetaR, integratedU410]
    ring
  let etaR : RatFunc k := V - integratedV410 (RatFunc.C l) A B C0
    (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
    (RatFunc.C delta) (RatFunc.C epsilon) 0
  have hetaD : d etaR = 0 := by
    rw [hR, hS, hT] at h5
    dsimp only [etaR, integratedV410, integratedR410, integratedS410,
      integratedT410] at h5 ⊢
    simp [Derivation.leibniz, Derivation.leibniz_pow, hconst, hn2, h32, h38,
      h52, h54, h74, h94, h154, h158, h516, h1516, h2116, h4516,
      h4532, h45128, hn5128] at h5 ⊢
    linear_combination (-1 / 4 : RatFunc k) * h5
  obtain ⟨eta, heta⟩ := descend etaR hetaD
  have hV : V = integratedV410 (RatFunc.C l) A B C0
      (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
      (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C eta) := by
    rw [← heta]
    simp only [etaR, integratedV410]
    ring
  let thetaR : RatFunc k := W - integratedW410 (RatFunc.C l) A B C0
    (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
    (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta) 0
  have hthetaD : d thetaR = 0 := by
    rw [hS, hT, hU] at h4
    dsimp only [thetaR, integratedW410, integratedS410, integratedT410,
      integratedU410] at h4 ⊢
    simp [Derivation.leibniz, Derivation.leibniz_pow, hconst, hn2, h32, h34,
      h52, h54, h74, h94, h154, h158, h516, h1516, h2116, h532,
      h2132, h4516, h4532, h15128, h45128, h7128, hn452048] at h4 ⊢
    linear_combination (-1 / 4 : RatFunc k) * h4
  obtain ⟨theta, htheta⟩ := descend thetaR hthetaD
  have hW : W = integratedW410 (RatFunc.C l) A B C0
      (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
      (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
      (RatFunc.C theta) := by
    rw [← htheta]
    simp only [thetaR, integratedW410]
    ring
  let iotaR : RatFunc k := Z - integratedZ410 (RatFunc.C l) A B C0
    (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
    (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
    (RatFunc.C eta) 0
  have hiotaD : d iotaR = 0 := by
    rw [hT, hU, hV] at h3
    have hintegrated := differentialJacobian_integrated410_eq d
      (RatFunc.C l) A B C0 (RatFunc.C alpha) (RatFunc.C beta)
      (RatFunc.C gamma) (RatFunc.C delta) (RatFunc.C epsilon)
      (RatFunc.C zeta) (RatFunc.C eta) 0 0
      (hconst l) (hconst alpha) (hconst beta) (hconst gamma)
      (hconst delta) (hconst epsilon) (hconst zeta) (hconst eta)
      (by simp) (by simp)
    dsimp only at hintegrated
    rw [differentialJacobian_depressed410_eq d (RatFunc.C l)
      (integratedP410 A (RatFunc.C alpha))
      (integratedQ410 (RatFunc.C l) A B (RatFunc.C beta))
      (integratedR410 (RatFunc.C l) A B C0 (RatFunc.C alpha)
        (RatFunc.C gamma))
      (integratedS410 (RatFunc.C l) A B C0 (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C delta))
      (integratedT410 (RatFunc.C l) A B C0 (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C epsilon))
      (integratedU410 (RatFunc.C l) A B C0 (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C zeta))
      (integratedV410 (RatFunc.C l) A B C0 (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C eta))
      (integratedW410 (RatFunc.C l) A B C0 (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) 0)
      (integratedZ410 (RatFunc.C l) A B C0 (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta) 0)
      A B C0 (hconst l)] at hintegrated
    have h3Integrated := congrArg
      (fun f : (RatFunc k)[X] => f.coeff 3) hintegrated
    norm_num [coeff_add, coeff_C, coeff_C_mul, coeff_mul_X_pow', coeff_X,
      coeff_X_pow] at h3Integrated
    dsimp only [iotaR]
    simp only [map_sub]
    linear_combination (-1 / 4 : RatFunc k) * h3 +
      (1 / 4 : RatFunc k) * h3Integrated
  obtain ⟨iota, hiota⟩ := descend iotaR hiotaD
  have hZ : Z = integratedZ410 (RatFunc.C l) A B C0
      (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
      (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
      (RatFunc.C eta) (RatFunc.C iota) := by
    rw [← hiota]
    simp only [iotaR, integratedZ410]
    ring
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    hL, hP, hQ, hR, hS, hT, hU, hV, hW, hZ⟩

/-- The exact ground-integration bridge required by the source-facing
early-load reduction. -/
theorem scaleZero410_groundIntegrationBridge :
    ScaleZero410GroundIntegrationBridge (k := k) := by
  intro terminal A B C0 L P Q R S T U V W Z _hterminal hbracket
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hL, hP, hQ, hR, hS, hT, hU, hV, hW, hZ⟩ :=
    depressedCoefficients_integrate_over_ground410
      (algebraMap k[X] (RatFunc k) L)
      (algebraMap k[X] (RatFunc k) P)
      (algebraMap k[X] (RatFunc k) Q)
      (algebraMap k[X] (RatFunc k) R)
      (algebraMap k[X] (RatFunc k) S)
      (algebraMap k[X] (RatFunc k) T)
      (algebraMap k[X] (RatFunc k) U)
      (algebraMap k[X] (RatFunc k) V)
      (algebraMap k[X] (RatFunc k) W)
      (algebraMap k[X] (RatFunc k) Z)
      (algebraMap k[X] (RatFunc k) A)
      (algebraMap k[X] (RatFunc k) B)
      (algebraMap k[X] (RatFunc k) C0)
      (RatFunc.C terminal) hbracket
  refine ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota, ?_⟩
  rw [hL, hP, hQ, hR, hS, hT, hU, hV, hW, hZ] at hbracket
  exact hbracket

end GroundIntegration410

end Max11DegreeRoutes
