import LowScale46SourceBridge

/-! # Constant-mismatch literal source bridge for `(4,6)`

This module removes the aligned restriction from the source integration.
Whenever the depressed quintic coefficient `L` lies in the ground field,
the five upper Jacobian rows integrate over that ground field and the final
three rows are exactly the two coefficient-curve equations and `eta`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section GeneralIntegration

variable {k : Type*} [Field k] [CharZero k]

/-- The five upper coefficient equations for a depressed bracket whose
quintic coefficient is a ground-field constant. -/
theorem depressedUpperRows46
    (L A B C0 P0 Q0 R0 S0 T0 terminal : RatFunc k)
    (hL : ratFuncDerivation46 L = 0)
    (hbracket : differentialJacobian ratFuncDerivation46
        (depressedQuartic46 A B C0)
        (depressedSextic46 L P0 Q0 R0 S0 T0) = C terminal) :
    (6 * ratFuncDerivation46 A - 4 * ratFuncDerivation46 P0 = 0) ∧
    (5 * L * ratFuncDerivation46 A + 6 * ratFuncDerivation46 B -
        4 * ratFuncDerivation46 Q0 = 0) ∧
    (-2 * A * ratFuncDerivation46 P0 + 5 * L * ratFuncDerivation46 B +
        4 * P0 * ratFuncDerivation46 A +
        6 * ratFuncDerivation46 C0 - 4 * ratFuncDerivation46 R0 = 0) ∧
    (-2 * A * ratFuncDerivation46 Q0 - B * ratFuncDerivation46 P0 +
        5 * L * ratFuncDerivation46 C0 +
        4 * P0 * ratFuncDerivation46 B + 3 * Q0 * ratFuncDerivation46 A -
        4 * ratFuncDerivation46 S0 = 0) ∧
    (-2 * A * ratFuncDerivation46 R0 - B * ratFuncDerivation46 Q0 +
        4 * P0 * ratFuncDerivation46 C0 + 3 * Q0 * ratFuncDerivation46 B +
        2 * R0 * ratFuncDerivation46 A - 4 * ratFuncDerivation46 T0 = 0) := by
  have hfull := hbracket
  rw [differentialJacobian_depressed46_eq ratFuncDerivation46
    L P0 Q0 R0 S0 T0 A B C0 hL] at hfull
  have h7 := congrArg (fun f : (RatFunc k)[X] => f.coeff 7) hfull
  have h6 := congrArg (fun f : (RatFunc k)[X] => f.coeff 6) hfull
  have h5 := congrArg (fun f : (RatFunc k)[X] => f.coeff 5) hfull
  have h4 := congrArg (fun f : (RatFunc k)[X] => f.coeff 4) hfull
  have h3 := congrArg (fun f : (RatFunc k)[X] => f.coeff 3) hfull
  norm_num [coeff_add, coeff_C, coeff_C_mul, coeff_mul_X_pow',
    coeff_X, coeff_X_pow] at h7 h6 h5 h4 h3
  refine ⟨h7, h6, ?_, ?_, ?_⟩
  · simp only [ratFuncDerivation46_apply]
    linear_combination h5
  · simp only [ratFuncDerivation46_apply]
    linear_combination h4
  · simp only [ratFuncDerivation46_apply]
    linear_combination h3

/-- Integration residual for the quartic row. -/
def alphaResidual46 (A P0 : RatFunc k) : RatFunc k :=
  P0 - (3 / 2 : RatFunc k) * A

/-- Integration residual for the sextic cubic row. -/
def betaResidual46 (L A B Q0 : RatFunc k) : RatFunc k :=
  Q0 - (5 / 4 : RatFunc k) * L * A - (3 / 2 : RatFunc k) * B

/-- Integration residual for the sextic quadratic row. -/
def gammaResidual46
    (L A B C0 P0 R0 : RatFunc k) : RatFunc k :=
  R0 - (3 / 8 : RatFunc k) * A ^ 2 - alphaResidual46 A P0 * A -
    (5 / 4 : RatFunc k) * L * B - (3 / 2 : RatFunc k) * C0

/-- Integration residual for the sextic linear row. -/
def deltaResidual46
    (L A B C0 P0 Q0 S0 : RatFunc k) : RatFunc k :=
  S0 - (5 / 32 : RatFunc k) * L * A ^ 2 -
    (3 / 4 : RatFunc k) * A * B -
    (3 / 4 : RatFunc k) * betaResidual46 L A B Q0 * A -
    alphaResidual46 A P0 * B - (5 / 4 : RatFunc k) * L * C0

/-- Integration residual for the sextic constant row. -/
def epsilonResidual46
    (L A B C0 P0 Q0 R0 T0 : RatFunc k) : RatFunc k :=
  T0 - ((-1 / 16 : RatFunc k) * A ^ 3 +
    (5 / 16 : RatFunc k) * L * A * B +
    (3 / 4 : RatFunc k) * A * C0 +
    (1 / 2 : RatFunc k) * gammaResidual46 L A B C0 P0 R0 * A +
    (3 / 8 : RatFunc k) * B ^ 2 +
    (3 / 4 : RatFunc k) * betaResidual46 L A B Q0 * B +
    alphaResidual46 A P0 * C0)

/-- The five general residuals have zero derivative. -/
theorem depressedResiduals_deriv_zero46
    (L A B C0 P0 Q0 R0 S0 T0 terminal : RatFunc k)
    (hL : ratFuncDerivation46 L = 0)
    (hbracket : differentialJacobian ratFuncDerivation46
        (depressedQuartic46 A B C0)
        (depressedSextic46 L P0 Q0 R0 S0 T0) = C terminal) :
    ratFuncDerivation46 (alphaResidual46 A P0) = 0 ∧
    ratFuncDerivation46 (betaResidual46 L A B Q0) = 0 ∧
    ratFuncDerivation46 (gammaResidual46 L A B C0 P0 R0) = 0 ∧
    ratFuncDerivation46 (deltaResidual46 L A B C0 P0 Q0 S0) = 0 ∧
    ratFuncDerivation46 (epsilonResidual46 L A B C0 P0 Q0 R0 T0) = 0 := by
  rcases depressedUpperRows46 L A B C0 P0 Q0 R0 S0 T0 terminal hL
      hbracket with ⟨h7, h6, h5, h4, h3⟩
  have h2 : ratFuncDerivation46 (2 : RatFunc k) = 0 :=
    ratFuncDerivation46.map_natCast 2
  have h3c : ratFuncDerivation46 (3 : RatFunc k) = 0 :=
    ratFuncDerivation46.map_natCast 3
  have h4c : ratFuncDerivation46 (4 : RatFunc k) = 0 :=
    ratFuncDerivation46.map_natCast 4
  have h5c : ratFuncDerivation46 (5 : RatFunc k) = 0 :=
    ratFuncDerivation46.map_natCast 5
  have h8 : ratFuncDerivation46 (8 : RatFunc k) = 0 :=
    ratFuncDerivation46.map_natCast 8
  have h16 : ratFuncDerivation46 (16 : RatFunc k) = 0 :=
    ratFuncDerivation46.map_natCast 16
  have h32c : ratFuncDerivation46 (32 : RatFunc k) = 0 :=
    ratFuncDerivation46.map_natCast 32
  have h12 : ratFuncDerivation46 (1 / 2 : RatFunc k) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h2]
  have h32 : ratFuncDerivation46 (3 / 2 : RatFunc k) = 0 := by
    simp [Derivation.leibniz_div, h2, h3c]
  have h34 : ratFuncDerivation46 (3 / 4 : RatFunc k) = 0 := by
    simp [Derivation.leibniz_div, h3c, h4c]
  have h54 : ratFuncDerivation46 (5 / 4 : RatFunc k) = 0 := by
    simp [Derivation.leibniz_div, h5c, h4c]
  have h38 : ratFuncDerivation46 (3 / 8 : RatFunc k) = 0 := by
    simp [Derivation.leibniz_div, h3c, h8]
  have h532 : ratFuncDerivation46 (5 / 32 : RatFunc k) = 0 := by
    simp [Derivation.leibniz_div, h5c, h32c]
  have h516 : ratFuncDerivation46 (5 / 16 : RatFunc k) = 0 := by
    simp [Derivation.leibniz_div, h5c, h16]
  have h116 : ratFuncDerivation46 (1 / 16 : RatFunc k) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h16]
  have hn116 : ratFuncDerivation46 (-1 / 16 : RatFunc k) = 0 := by
    rw [show (-1 / 16 : RatFunc k) = -(1 / 16) by ring, map_neg, h116,
      neg_zero]
  have halpha : ratFuncDerivation46 (alphaResidual46 A P0) = 0 := by
    simp only [alphaResidual46, map_sub, Derivation.leibniz, h32,
      zero_mul, add_zero]
    linear_combination (-1 / 4 : RatFunc k) * h7
  have hbeta : ratFuncDerivation46 (betaResidual46 L A B Q0) = 0 := by
    simp only [betaResidual46, map_sub, Derivation.leibniz, h54, h32, hL,
      zero_mul, zero_add, add_zero]
    linear_combination (-1 / 4 : RatFunc k) * h6
  have hPderiv : ratFuncDerivation46 P0 =
      (3 / 2 : RatFunc k) * ratFuncDerivation46 A := by
    linear_combination (-1 / 4 : RatFunc k) * h7
  have hQderiv : ratFuncDerivation46 Q0 =
      (5 / 4 : RatFunc k) * L * ratFuncDerivation46 A +
        (3 / 2 : RatFunc k) * ratFuncDerivation46 B := by
    linear_combination (-1 / 4 : RatFunc k) * h6
  have hRderiv : ratFuncDerivation46 R0 =
      (-1 / 2 : RatFunc k) * A * ratFuncDerivation46 P0 +
        (5 / 4 : RatFunc k) * L * ratFuncDerivation46 B +
        P0 * ratFuncDerivation46 A +
        (3 / 2 : RatFunc k) * ratFuncDerivation46 C0 := by
    linear_combination (-1 / 4 : RatFunc k) * h5
  have hSderiv : ratFuncDerivation46 S0 =
      (-1 / 2 : RatFunc k) * A * ratFuncDerivation46 Q0 -
        (1 / 4 : RatFunc k) * B * ratFuncDerivation46 P0 +
        (5 / 4 : RatFunc k) * L * ratFuncDerivation46 C0 +
        P0 * ratFuncDerivation46 B +
        (3 / 4 : RatFunc k) * Q0 * ratFuncDerivation46 A := by
    linear_combination (-1 / 4 : RatFunc k) * h4
  have hTderiv : ratFuncDerivation46 T0 =
      (-1 / 2 : RatFunc k) * A * ratFuncDerivation46 R0 -
        (1 / 4 : RatFunc k) * B * ratFuncDerivation46 Q0 +
        P0 * ratFuncDerivation46 C0 +
        (3 / 4 : RatFunc k) * Q0 * ratFuncDerivation46 B +
        (1 / 2 : RatFunc k) * R0 * ratFuncDerivation46 A := by
    linear_combination (-1 / 4 : RatFunc k) * h3
  have hgamma :
      ratFuncDerivation46 (gammaResidual46 L A B C0 P0 R0) = 0 := by
    simp only [gammaResidual46, map_sub, Derivation.leibniz,
      Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, h38, h54, h32, hL,
      halpha, zero_mul, zero_add, add_zero]
    rw [hRderiv, hPderiv]
    simp only [alphaResidual46]
    ring
  have hdelta :
      ratFuncDerivation46 (deltaResidual46 L A B C0 P0 Q0 S0) = 0 := by
    simp only [deltaResidual46, map_sub, Derivation.leibniz,
      Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, h532, h34, h54, hL,
      halpha, hbeta, zero_mul, zero_add, add_zero]
    rw [hSderiv, hQderiv, hPderiv]
    simp only [alphaResidual46, betaResidual46]
    ring
  have hepsilon :
      ratFuncDerivation46 (epsilonResidual46 L A B C0 P0 Q0 R0 T0) = 0 := by
    simp only [epsilonResidual46, map_sub, map_add, map_neg,
      Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul,
      smul_eq_mul, hn116, h516, h34, h12, h38, hL,
      hgamma, hbeta, halpha,
      zero_mul, zero_add, add_zero]
    rw [hTderiv, hRderiv, hQderiv, hPderiv]
    simp only [gammaResidual46, betaResidual46, alphaResidual46]
    ring
  exact ⟨halpha, hbeta, hgamma, hdelta, hepsilon⟩

/-- The five upper rows integrate over the ground field for every
ground-field value of `L`. -/
theorem depressedIntegratesOverGround46
    (l : k) (A B C0 P0 Q0 R0 S0 T0 terminal : RatFunc k)
    (hbracket : differentialJacobian ratFuncDerivation46
        (depressedQuartic46 A B C0)
        (depressedSextic46 (algebraMap k (RatFunc k) l)
          P0 Q0 R0 S0 T0) = C terminal) :
    ∃ alpha beta gamma delta epsilon : k,
      P0 = integratedP46 A (algebraMap k (RatFunc k) alpha) ∧
      Q0 = integratedQ46 (algebraMap k (RatFunc k) l) A B
        (algebraMap k (RatFunc k) beta) ∧
      R0 = integratedR46 (algebraMap k (RatFunc k) l) A B C0
        (algebraMap k (RatFunc k) alpha)
        (algebraMap k (RatFunc k) gamma) ∧
      S0 = integratedS46 (algebraMap k (RatFunc k) l) A B C0
        (algebraMap k (RatFunc k) alpha)
        (algebraMap k (RatFunc k) beta)
        (algebraMap k (RatFunc k) delta) ∧
      T0 = integratedT46 (algebraMap k (RatFunc k) l) A B C0
        (algebraMap k (RatFunc k) alpha)
        (algebraMap k (RatFunc k) beta)
        (algebraMap k (RatFunc k) gamma)
        (algebraMap k (RatFunc k) epsilon) := by
  have hL : ratFuncDerivation46 (algebraMap k (RatFunc k) l) = 0 := by
    have hp := ratFuncDerivation46_polynomial (C l : k[X])
    simpa [RatFunc.algebraMap_C] using hp
  rcases depressedResiduals_deriv_zero46
      (algebraMap k (RatFunc k) l) A B C0 P0 Q0 R0 S0 T0 terminal hL
      hbracket with ⟨halpha0, hbeta0, hgamma0, hdelta0, hepsilon0⟩
  have halphaD : Differential.deriv (alphaResidual46 A P0) = 0 := by
    simpa only [ratFuncDerivation46_apply] using halpha0
  have hbetaD : Differential.deriv
      (betaResidual46 (algebraMap k (RatFunc k) l) A B Q0) = 0 := by
    simpa only [ratFuncDerivation46_apply] using hbeta0
  have hgammaD : Differential.deriv
      (gammaResidual46 (algebraMap k (RatFunc k) l) A B C0 P0 R0) = 0 := by
    simpa only [ratFuncDerivation46_apply] using hgamma0
  have hdeltaD : Differential.deriv
      (deltaResidual46 (algebraMap k (RatFunc k) l) A B C0 P0 Q0 S0) = 0 := by
    simpa only [ratFuncDerivation46_apply] using hdelta0
  have hepsilonD : Differential.deriv
      (epsilonResidual46 (algebraMap k (RatFunc k) l)
        A B C0 P0 Q0 R0 T0) = 0 := by
    simpa only [ratFuncDerivation46_apply] using hepsilon0
  obtain ⟨alpha, halpha⟩ := GCD369RatFuncConstants
    (alphaResidual46 A P0) halphaD
  obtain ⟨beta, hbeta⟩ := GCD369RatFuncConstants
    (betaResidual46 (algebraMap k (RatFunc k) l) A B Q0) hbetaD
  obtain ⟨gamma, hgamma⟩ := GCD369RatFuncConstants
    (gammaResidual46 (algebraMap k (RatFunc k) l) A B C0 P0 R0) hgammaD
  obtain ⟨delta, hdelta⟩ := GCD369RatFuncConstants
    (deltaResidual46 (algebraMap k (RatFunc k) l) A B C0 P0 Q0 S0) hdeltaD
  obtain ⟨epsilon, hepsilon⟩ := GCD369RatFuncConstants
    (epsilonResidual46 (algebraMap k (RatFunc k) l)
      A B C0 P0 Q0 R0 T0) hepsilonD
  refine ⟨alpha, beta, gamma, delta, epsilon, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← halpha]
    simp only [integratedP46, alphaResidual46]
    ring
  · rw [← hbeta]
    simp only [integratedQ46, betaResidual46]
    ring
  · rw [← halpha, ← hgamma]
    simp only [integratedR46, alphaResidual46, gammaResidual46]
    ring
  · rw [← halpha, ← hbeta, ← hdelta]
    simp only [integratedS46, alphaResidual46, betaResidual46,
      deltaResidual46]
    ring
  · rw [← halpha, ← hbeta, ← hgamma, ← hepsilon]
    simp only [integratedT46, alphaResidual46, betaResidual46,
      gammaResidual46, epsilonResidual46]
    ring

/-- A constant depressed bracket lands on the complete reviewed coefficient
curve over ground-field parameters, for arbitrary ground-field `L`. -/
theorem depressedCoefficientCurveData46
    (l : k) (A B C0 P0 Q0 R0 S0 T0 terminal : RatFunc k)
    (hbracket : differentialJacobian ratFuncDerivation46
        (depressedQuartic46 A B C0)
        (depressedSextic46 (algebraMap k (RatFunc k) l)
          P0 Q0 R0 S0 T0) = C terminal) :
    ∃ alpha beta gamma delta epsilon k2 k1 : k,
      P0 = integratedP46 A (algebraMap k (RatFunc k) alpha) ∧
      Q0 = integratedQ46 (algebraMap k (RatFunc k) l) A B
        (algebraMap k (RatFunc k) beta) ∧
      R0 = integratedR46 (algebraMap k (RatFunc k) l) A B C0
        (algebraMap k (RatFunc k) alpha)
        (algebraMap k (RatFunc k) gamma) ∧
      S0 = integratedS46 (algebraMap k (RatFunc k) l) A B C0
        (algebraMap k (RatFunc k) alpha)
        (algebraMap k (RatFunc k) beta)
        (algebraMap k (RatFunc k) delta) ∧
      T0 = integratedT46 (algebraMap k (RatFunc k) l) A B C0
        (algebraMap k (RatFunc k) alpha)
        (algebraMap k (RatFunc k) beta)
        (algebraMap k (RatFunc k) gamma)
        (algebraMap k (RatFunc k) epsilon) ∧
      coefficientCurveTwo46 (algebraMap k (RatFunc k) l)
          A B (A ^ 2 - 4 * C0)
          (algebraMap k (RatFunc k) beta)
          (algebraMap k (RatFunc k) gamma)
          (algebraMap k (RatFunc k) delta) =
        algebraMap k (RatFunc k) k2 ∧
      coefficientCurveOne46 (algebraMap k (RatFunc k) l)
          A B (A ^ 2 - 4 * C0)
          (algebraMap k (RatFunc k) beta)
          (algebraMap k (RatFunc k) gamma)
          (algebraMap k (RatFunc k) delta) =
        algebraMap k (RatFunc k) k1 ∧
      eta46 (algebraMap k (RatFunc k) l) A B (A ^ 2 - 4 * C0)
          (algebraMap k (RatFunc k) beta)
          (algebraMap k (RatFunc k) gamma)
          (algebraMap k (RatFunc k) delta)
          (ratFuncDerivation46 A) (ratFuncDerivation46 B)
          (ratFuncDerivation46 (A ^ 2 - 4 * C0)) = terminal := by
  obtain ⟨alpha, beta, gamma, delta, epsilon,
      hP, hQ, hR, hS, hT⟩ :=
    depressedIntegratesOverGround46 l A B C0 P0 Q0 R0 S0 T0 terminal
      hbracket
  let U : RatFunc k := A ^ 2 - 4 * C0
  have hC : discriminantC46 A U = C0 := by
    simp only [discriminantC46, U]
    ring
  have hconst (c : k) : ratFuncDerivation46 (RatFunc.C c) = 0 := by
    have hp := ratFuncDerivation46_polynomial (C c : k[X])
    simpa [RatFunc.algebraMap_C] using hp
  have hshape := differentialJacobian_integratedDiscriminant46_eq
    ratFuncDerivation46 (algebraMap k (RatFunc k) l) A B U
      (algebraMap k (RatFunc k) alpha)
      (algebraMap k (RatFunc k) beta)
      (algebraMap k (RatFunc k) gamma)
      (algebraMap k (RatFunc k) delta)
      (algebraMap k (RatFunc k) epsilon)
      (by simpa [RatFunc.algebraMap_eq_C] using hconst l)
      (by simpa [RatFunc.algebraMap_eq_C] using hconst alpha)
      (by simpa [RatFunc.algebraMap_eq_C] using hconst beta)
      (by simpa [RatFunc.algebraMap_eq_C] using hconst gamma)
      (by simpa [RatFunc.algebraMap_eq_C] using hconst delta)
      (by simpa [RatFunc.algebraMap_eq_C] using hconst epsilon)
  dsimp only at hshape
  rw [hC] at hshape
  have hbracket' := hbracket
  rw [hP, hQ, hR, hS, hT, hshape] at hbracket'
  have h2 := congrArg (fun f : (RatFunc k)[X] => f.coeff 2) hbracket'
  have h1 := congrArg (fun f : (RatFunc k)[X] => f.coeff 1) hbracket'
  have h0 := congrArg (fun f : (RatFunc k)[X] => f.coeff 0) hbracket'
  norm_num [coeff_add, coeff_C, coeff_C_mul, coeff_mul_X_pow',
    coeff_X, coeff_X_pow] at h2 h1 h0
  have h2D : Differential.deriv
      (coefficientCurveTwo46 (algebraMap k (RatFunc k) l) A B U
        (algebraMap k (RatFunc k) beta)
        (algebraMap k (RatFunc k) gamma)
        (algebraMap k (RatFunc k) delta)) = 0 := by
    simpa only [ratFuncDerivation46_apply, RatFunc.algebraMap_eq_C] using h2
  have h1D : Differential.deriv
      (coefficientCurveOne46 (algebraMap k (RatFunc k) l) A B U
        (algebraMap k (RatFunc k) beta)
        (algebraMap k (RatFunc k) gamma)
        (algebraMap k (RatFunc k) delta)) = 0 := by
    simpa only [ratFuncDerivation46_apply, RatFunc.algebraMap_eq_C] using h1
  obtain ⟨k2, hk2⟩ := GCD369RatFuncConstants
    (coefficientCurveTwo46 (algebraMap k (RatFunc k) l) A B U
      (algebraMap k (RatFunc k) beta)
      (algebraMap k (RatFunc k) gamma)
      (algebraMap k (RatFunc k) delta)) h2D
  obtain ⟨k1, hk1⟩ := GCD369RatFuncConstants
    (coefficientCurveOne46 (algebraMap k (RatFunc k) l) A B U
      (algebraMap k (RatFunc k) beta)
      (algebraMap k (RatFunc k) gamma)
      (algebraMap k (RatFunc k) delta)) h1D
  refine ⟨alpha, beta, gamma, delta, epsilon, k2, k1,
    hP, hQ, hR, hS, hT, ?_, ?_, ?_⟩
  · simpa only [U]
  · simpa only [U]
  · simpa only [U, RatFunc.algebraMap_eq_C,
      ratFuncDerivation46_apply] using h0

section GeneralSourceBoundaries

/-- For arbitrary constant depressed quintic coefficient `L`, the two
reviewed boundary functions are still the images of literal coefficient
polynomials. -/
theorem constantLDepressedLiteralBoundaries46
    (p q : k[X][X]) (h r A B C0 : RatFunc k) (l : k)
    (alpha beta gamma delta epsilon : k)
    (hpDep : affineDepress46 h r (sourceToRatFunc46 p) =
      depressedQuartic46 A B C0)
    (hqDep : affineDepress46 h r (sourceToRatFunc46 q) =
      depressedSextic46 (algebraMap k (RatFunc k) l)
        (integratedP46 A (algebraMap k (RatFunc k) alpha))
        (integratedQ46 (algebraMap k (RatFunc k) l) A B
          (algebraMap k (RatFunc k) beta))
        (integratedR46 (algebraMap k (RatFunc k) l) A B C0
          (algebraMap k (RatFunc k) alpha)
          (algebraMap k (RatFunc k) gamma))
        (integratedS46 (algebraMap k (RatFunc k) l) A B C0
          (algebraMap k (RatFunc k) alpha)
          (algebraMap k (RatFunc k) beta)
          (algebraMap k (RatFunc k) delta))
        (integratedT46 (algebraMap k (RatFunc k) l) A B C0
          (algebraMap k (RatFunc k) alpha)
          (algebraMap k (RatFunc k) beta)
          (algebraMap k (RatFunc k) gamma)
          (algebraMap k (RatFunc k) epsilon))) :
    boundaryD46 r (translatedQ46 r A) B (A ^ 2 - 4 * C0) =
        algebraMap k[X] (RatFunc k) (p.coeff 0) ∧
    boundaryE46 (algebraMap k (RatFunc k) l) r
        (translatedQ46 r A) B (A ^ 2 - 4 * C0)
        (algebraMap k (RatFunc k) beta)
        (algebraMap k (RatFunc k) gamma)
        (algebraMap k (RatFunc k) delta) =
      algebraMap k[X] (RatFunc k)
        (q.coeff 0 - C alpha * p.coeff 0 - C epsilon) := by
  let U : RatFunc k := A ^ 2 - 4 * C0
  have hC : discriminantC46 A U = C0 := by
    simp only [discriminantC46, U]
    ring
  have hpCenter := congrArg (fun f : (RatFunc k)[X] => f.eval r) hpDep
  have hqCenter := congrArg (fun f : (RatFunc k)[X] => f.eval r) hqDep
  rw [eval_affineDepress46_center] at hpCenter hqCenter
  simp only [sourceToRatFunc46, coeff_map] at hpCenter hqCenter
  have hDcurve :=
    eval_depressedQuartic46_discriminant_eq_boundaryD46 r A B U
  have hEcurve := eval_integratedSextic46_discriminant_eq_boundaryE46
    (algebraMap k (RatFunc k) l) r A B U
      (algebraMap k (RatFunc k) alpha)
      (algebraMap k (RatFunc k) beta)
      (algebraMap k (RatFunc k) gamma)
      (algebraMap k (RatFunc k) delta)
      (algebraMap k (RatFunc k) epsilon)
  dsimp only at hEcurve
  rw [hC] at hDcurve hEcurve
  constructor
  · simpa only [U] using hDcurve.symm.trans hpCenter.symm
  · have hboundary : boundaryE46 (algebraMap k (RatFunc k) l) r
        (translatedQ46 r A) B U
        (algebraMap k (RatFunc k) beta)
        (algebraMap k (RatFunc k) gamma)
        (algebraMap k (RatFunc k) delta) =
        algebraMap k[X] (RatFunc k) (q.coeff 0) -
          algebraMap k (RatFunc k) alpha *
            algebraMap k[X] (RatFunc k) (p.coeff 0) -
          algebraMap k (RatFunc k) epsilon := by
      rw [← hEcurve, ← hqCenter, ← hpCenter]
    rw [hboundary]
    simp only [map_sub, map_mul, RatFunc.algebraMap_C,
      RatFunc.algebraMap_eq_C]

end GeneralSourceBoundaries

section SourcePackage

/-- The source-level coefficient-curve data common to aligned and mismatch
branches when the depressed quintic coefficient is a ground-field scalar. -/
structure SquareConstantLSourceCurveData46
    (p q : k[X][X]) (j : k) (h0 : k[X]) (l : k) where
  r : RatFunc k
  A : RatFunc k
  B : RatFunc k
  C0 : RatFunc k
  alpha : k
  beta : k
  gamma : k
  delta : k
  epsilon : k
  k2 : k
  k1 : k
  center_eq : r = quarticDepressionR46
    (algebraMap k[X] (RatFunc k) h0)
    (algebraMap k[X] (RatFunc k) (p.coeff 3))
  quartic_eq :
    affineDepress46 (algebraMap k[X] (RatFunc k) h0) r
        (sourceToRatFunc46 p) = depressedQuartic46 A B C0
  sextic_eq :
    affineDepress46 (algebraMap k[X] (RatFunc k) h0) r
        (sourceToRatFunc46 q) =
      depressedSextic46 (algebraMap k (RatFunc k) l)
        (integratedP46 A (algebraMap k (RatFunc k) alpha))
        (integratedQ46 (algebraMap k (RatFunc k) l) A B
          (algebraMap k (RatFunc k) beta))
        (integratedR46 (algebraMap k (RatFunc k) l) A B C0
          (algebraMap k (RatFunc k) alpha)
          (algebraMap k (RatFunc k) gamma))
        (integratedS46 (algebraMap k (RatFunc k) l) A B C0
          (algebraMap k (RatFunc k) alpha)
          (algebraMap k (RatFunc k) beta)
          (algebraMap k (RatFunc k) delta))
        (integratedT46 (algebraMap k (RatFunc k) l) A B C0
          (algebraMap k (RatFunc k) alpha)
          (algebraMap k (RatFunc k) beta)
          (algebraMap k (RatFunc k) gamma)
          (algebraMap k (RatFunc k) epsilon))
  curveTwo : coefficientCurveTwo46 (algebraMap k (RatFunc k) l)
      A B (A ^ 2 - 4 * C0)
      (algebraMap k (RatFunc k) beta)
      (algebraMap k (RatFunc k) gamma)
      (algebraMap k (RatFunc k) delta) =
    algebraMap k (RatFunc k) k2
  curveOne : coefficientCurveOne46 (algebraMap k (RatFunc k) l)
      A B (A ^ 2 - 4 * C0)
      (algebraMap k (RatFunc k) beta)
      (algebraMap k (RatFunc k) gamma)
      (algebraMap k (RatFunc k) delta) =
    algebraMap k (RatFunc k) k1
  boundaryD : boundaryD46 r (translatedQ46 r A) B (A ^ 2 - 4 * C0) =
    algebraMap k[X] (RatFunc k) (p.coeff 0)
  boundaryE : boundaryE46 (algebraMap k (RatFunc k) l) r
      (translatedQ46 r A) B (A ^ 2 - 4 * C0)
      (algebraMap k (RatFunc k) beta)
      (algebraMap k (RatFunc k) gamma)
      (algebraMap k (RatFunc k) delta) =
    algebraMap k[X] (RatFunc k)
      (q.coeff 0 - C alpha * p.coeff 0 - C epsilon)
  lastRow : algebraMap k[X] (RatFunc k) h0 *
      eta46 (algebraMap k (RatFunc k) l) A B (A ^ 2 - 4 * C0)
        (algebraMap k (RatFunc k) beta)
        (algebraMap k (RatFunc k) gamma)
        (algebraMap k (RatFunc k) delta)
        (ratFuncDerivation46 A) (ratFuncDerivation46 B)
        (ratFuncDerivation46 (A ^ 2 - 4 * C0)) = RatFunc.C j

/-- A literal square-core source whose depressed quintic coefficient equals
a selected ground-field scalar supplies the complete general curve package. -/
theorem squareConstantLSourceCurveData46
    (p q : k[X][X]) (H h0 : k[X]) (j l : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 6)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq6 : q.coeff 6 = H ^ 3)
    (hL : depressedL46
        (algebraMap k[X] (RatFunc k) h0)
        (quarticDepressionR46 (algebraMap k[X] (RatFunc k) h0)
          (algebraMap k[X] (RatFunc k) (p.coeff 3)))
        (algebraMap k[X] (RatFunc k) (q.coeff 5)) =
      algebraMap k (RatFunc k) l)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j)) :
    Nonempty (SquareConstantLSourceCurveData46 p q j h0 l) := by
  let h : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let a1 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 1)
  let a0 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 0)
  let b5 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 5)
  let b4 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 4)
  let b3 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 3)
  let b2 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 2)
  let b1 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 1)
  let b0 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 0)
  let r : RatFunc k := quarticDepressionR46 h a3
  let A := depressedA46 h r a3 a2
  let B := depressedB46 h r a3 a2 a1
  let C0 := depressedC46 h r a3 a2 a1 a0
  let L := depressedL46 h r b5
  let P0 := depressedP46 h r b5 b4
  let Q0 := depressedQ46 h r b5 b4 b3
  let R0 := depressedR46 h r b5 b4 b3 b2
  let S0 := depressedS46 h r b5 b4 b3 b2 b1
  let T0 := depressedT46 h r b5 b4 b3 b2 b1 b0
  have hh : h ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 4) = h ^ 4 := by
    simp only [hp4, hH, h, map_pow]
    ring
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 6) = h ^ 6 := by
    simp only [hq6, hH, h, map_pow]
    ring
  have hpDep : affineDepress46 h r (sourceToRatFunc46 p) =
      depressedQuartic46 A B C0 := by
    exact affineDepress_sourceQuartic46 p h r hp hh hpTop rfl
  have hqDep : affineDepress46 h r (sourceToRatFunc46 q) =
      depressedSextic46 L P0 Q0 R0 S0 T0 := by
    exact affineDepress_sourceSextic46 q h r hq hh hqTop
  have hL' : L = algebraMap k (RatFunc k) l := by
    simpa only [L, h, r, a3, b5] using hL
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc46
    p q j h r hh hD
  rw [hpDep, hqDep, hL'] at hbracket
  obtain ⟨alpha, beta, gamma, delta, epsilon, k2, k1,
      hP, hQ, hR, hS, hT, hcurve2, hcurve1, heta⟩ :=
    depressedCoefficientCurveData46 l A B C0 P0 Q0 R0 S0 T0
      (RatFunc.C j / h) hbracket
  have hqIntegrated :
      affineDepress46 (algebraMap k[X] (RatFunc k) h0) r
          (sourceToRatFunc46 q) =
        depressedSextic46 (algebraMap k (RatFunc k) l)
          (integratedP46 A (algebraMap k (RatFunc k) alpha))
          (integratedQ46 (algebraMap k (RatFunc k) l) A B
            (algebraMap k (RatFunc k) beta))
          (integratedR46 (algebraMap k (RatFunc k) l) A B C0
            (algebraMap k (RatFunc k) alpha)
            (algebraMap k (RatFunc k) gamma))
          (integratedS46 (algebraMap k (RatFunc k) l) A B C0
            (algebraMap k (RatFunc k) alpha)
            (algebraMap k (RatFunc k) beta)
            (algebraMap k (RatFunc k) delta))
          (integratedT46 (algebraMap k (RatFunc k) l) A B C0
            (algebraMap k (RatFunc k) alpha)
            (algebraMap k (RatFunc k) beta)
            (algebraMap k (RatFunc k) gamma)
            (algebraMap k (RatFunc k) epsilon)) := by
    rw [hqDep, hL', hP, hQ, hR, hS, hT]
  have hboundaries := constantLDepressedLiteralBoundaries46
    p q (algebraMap k[X] (RatFunc k) h0) r A B C0 l
      alpha beta gamma delta epsilon hpDep hqIntegrated
  have hlast : h *
      eta46 (algebraMap k (RatFunc k) l) A B (A ^ 2 - 4 * C0)
        (algebraMap k (RatFunc k) beta)
        (algebraMap k (RatFunc k) gamma)
        (algebraMap k (RatFunc k) delta)
        (ratFuncDerivation46 A) (ratFuncDerivation46 B)
        (ratFuncDerivation46 (A ^ 2 - 4 * C0)) = RatFunc.C j := by
    rw [heta]
    field_simp
  exact ⟨{
    r := r
    A := A
    B := B
    C0 := C0
    alpha := alpha
    beta := beta
    gamma := gamma
    delta := delta
    epsilon := epsilon
    k2 := k2
    k1 := k1
    center_eq := rfl
    quartic_eq := hpDep
    sextic_eq := hqIntegrated
    curveTwo := hcurve2
    curveOne := hcurve1
    boundaryD := hboundaries.1
    boundaryE := hboundaries.2
    lastRow := hlast
  }⟩

end SourcePackage

end GeneralIntegration

end Max11DegreeRoutes
