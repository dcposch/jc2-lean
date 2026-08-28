import LowScale46QuadraticField
import LowScale46SourceBridge

/-! # The aligned nonsquare source bridge for `(4,6)`

This module maps a literal aligned source into `k(x)(√H)`.  The quadratic
deck involution commutes with the affine depression up to `z ↦ -z`; hence
the depressed quartic and sextic coefficients acquire their expected even
and odd parities.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section GenericAlignedIntegration

variable {k F : Type*} [Field k] [Field F] [CharZero F] [Algebra k F]

/-- The five residuals are stated over an arbitrary differential field so
the same algebra serves both `k(x)` and its quadratic extension. -/
def alignedAlphaResidualField46 (A P0 : F) : F :=
  P0 - (3 / 2 : F) * A

def alignedBetaResidualField46 (B Q0 : F) : F :=
  Q0 - (3 / 2 : F) * B

def alignedGammaResidualField46 (A C0 P0 R0 : F) : F :=
  R0 - (3 / 8 : F) * A ^ 2 -
    alignedAlphaResidualField46 A P0 * A - (3 / 2 : F) * C0

def alignedDeltaResidualField46 (A B P0 Q0 S0 : F) : F :=
  S0 - (3 / 4 : F) * A * B -
    (3 / 4 : F) * alignedBetaResidualField46 B Q0 * A -
    alignedAlphaResidualField46 A P0 * B

def alignedEpsilonResidualField46
    (A B C0 P0 Q0 R0 T0 : F) : F :=
  T0 - ((-1 / 16 : F) * A ^ 3 + (3 / 4 : F) * A * C0 +
    (1 / 2 : F) * alignedGammaResidualField46 A C0 P0 R0 * A +
    (3 / 8 : F) * B ^ 2 +
    (3 / 4 : F) * alignedBetaResidualField46 B Q0 * B +
    alignedAlphaResidualField46 A P0 * C0)

/-- The five upper coefficient rows of an aligned depressed bracket. -/
theorem alignedDepressedUpperRowsField46
    (d : Derivation k F F)
    (A B C0 P0 Q0 R0 S0 T0 terminal : F)
    (hbracket : differentialJacobian d
        (depressedQuartic46 A B C0)
        (depressedSextic46 0 P0 Q0 R0 S0 T0) = C terminal) :
    (6 * d A - 4 * d P0 = 0) ∧
    (6 * d B - 4 * d Q0 = 0) ∧
    (-2 * A * d P0 + 4 * P0 * d A + 6 * d C0 - 4 * d R0 = 0) ∧
    (-2 * A * d Q0 - B * d P0 + 4 * P0 * d B +
        3 * Q0 * d A - 4 * d S0 = 0) ∧
    (-2 * A * d R0 - B * d Q0 + 4 * P0 * d C0 +
        3 * Q0 * d B + 2 * R0 * d A - 4 * d T0 = 0) := by
  have hfull := hbracket
  rw [differentialJacobian_depressed46_eq d
    0 P0 Q0 R0 S0 T0 A B C0 (by simp)] at hfull
  have h7 := congrArg (fun f : F[X] => f.coeff 7) hfull
  have h6 := congrArg (fun f : F[X] => f.coeff 6) hfull
  have h5 := congrArg (fun f : F[X] => f.coeff 5) hfull
  have h4 := congrArg (fun f : F[X] => f.coeff 4) hfull
  have h3 := congrArg (fun f : F[X] => f.coeff 3) hfull
  norm_num [coeff_add, coeff_C, coeff_C_mul, coeff_mul_X_pow',
    coeff_X, coeff_X_pow] at h7 h6 h5 h4 h3
  refine ⟨h7, h6, ?_, ?_, ?_⟩
  · linear_combination h5
  · linear_combination h4
  · linear_combination h3

/-- The five residuals have zero derivative over every characteristic-zero
differential field. -/
theorem alignedDepressedResiduals_deriv_zeroField46
    (d : Derivation k F F)
    (A B C0 P0 Q0 R0 S0 T0 terminal : F)
    (hbracket : differentialJacobian d
        (depressedQuartic46 A B C0)
        (depressedSextic46 0 P0 Q0 R0 S0 T0) = C terminal) :
    d (alignedAlphaResidualField46 A P0) = 0 ∧
    d (alignedBetaResidualField46 B Q0) = 0 ∧
    d (alignedGammaResidualField46 A C0 P0 R0) = 0 ∧
    d (alignedDeltaResidualField46 A B P0 Q0 S0) = 0 ∧
    d (alignedEpsilonResidualField46 A B C0 P0 Q0 R0 T0) = 0 := by
  rcases alignedDepressedUpperRowsField46 d
      A B C0 P0 Q0 R0 S0 T0 terminal hbracket with
    ⟨h7, h6, h5, h4, h3⟩
  have h2c : d (2 : F) = 0 := d.map_natCast 2
  have h3c : d (3 : F) = 0 := d.map_natCast 3
  have h4c : d (4 : F) = 0 := d.map_natCast 4
  have h8c : d (8 : F) = 0 := d.map_natCast 8
  have h16c : d (16 : F) = 0 := d.map_natCast 16
  have h12 : d (1 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h2c]
  have h32 : d (3 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2c, h3c]
  have h34 : d (3 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h3c, h4c]
  have h38 : d (3 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h3c, h8c]
  have h116 : d (1 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h16c]
  have hn116 : d (-1 / 16 : F) = 0 := by
    rw [show (-1 / 16 : F) = -(1 / 16) by ring, map_neg, h116, neg_zero]
  have halpha : d (alignedAlphaResidualField46 A P0) = 0 := by
    simp only [alignedAlphaResidualField46, map_sub, Derivation.leibniz,
      h32, zero_mul, add_zero]
    linear_combination (-1 / 4 : F) * h7
  have hbeta : d (alignedBetaResidualField46 B Q0) = 0 := by
    simp only [alignedBetaResidualField46, map_sub, Derivation.leibniz,
      h32, zero_mul, add_zero]
    linear_combination (-1 / 4 : F) * h6
  have hPderiv : d P0 = (3 / 2 : F) * d A := by
    linear_combination (-1 / 4 : F) * h7
  have hQderiv : d Q0 = (3 / 2 : F) * d B := by
    linear_combination (-1 / 4 : F) * h6
  have hRderiv : d R0 = (-3 / 4 : F) * A * d A +
      P0 * d A + (3 / 2 : F) * d C0 := by
    linear_combination (-1 / 4 : F) * h5 - (A / 2 : F) * hPderiv
  have hSderiv : d S0 = (-3 / 4 : F) * A * d B -
      (3 / 8 : F) * B * d A + P0 * d B +
      (3 / 4 : F) * Q0 * d A := by
    linear_combination (-1 / 4 : F) * h4 - (A / 2 : F) * hQderiv -
      (B / 4 : F) * hPderiv
  have hTderiv : d T0 = (-1 / 2 : F) * A * d R0 -
      (1 / 4 : F) * B * d Q0 + P0 * d C0 +
      (3 / 4 : F) * Q0 * d B + (1 / 2 : F) * R0 * d A := by
    linear_combination (-1 / 4 : F) * h3
  have hgamma : d (alignedGammaResidualField46 A C0 P0 R0) = 0 := by
    simp only [alignedGammaResidualField46, map_sub, Derivation.leibniz,
      Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, h38, h32,
      halpha, zero_mul, zero_add, add_zero]
    rw [hRderiv]
    simp only [alignedAlphaResidualField46]
    ring
  have hdelta : d (alignedDeltaResidualField46 A B P0 Q0 S0) = 0 := by
    simp only [alignedDeltaResidualField46, map_sub, Derivation.leibniz,
      h34, halpha, hbeta, zero_mul, zero_add, add_zero]
    rw [hSderiv]
    simp only [alignedAlphaResidualField46, alignedBetaResidualField46]
    ring
  have hepsilon :
      d (alignedEpsilonResidualField46 A B C0 P0 Q0 R0 T0) = 0 := by
    simp only [alignedEpsilonResidualField46, map_sub, map_add, map_neg,
      Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul,
      smul_eq_mul, hn116, h34, h12, h38, hgamma, hbeta, halpha,
      zero_mul, zero_add, add_zero]
    rw [hTderiv, hRderiv, hQderiv]
    simp only [alignedGammaResidualField46, alignedBetaResidualField46,
      alignedAlphaResidualField46]
    ring
  exact ⟨halpha, hbeta, hgamma, hdelta, hepsilon⟩

end GenericAlignedIntegration

section QuadraticSource

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

local notation "F46" => AdjoinRoot (alignedQuadraticPolynomial46 H)

local instance quadraticCharZero46 : CharZero F46 :=
  charZero_of_injective_ringHom (algebraMap (RatFunc k) F46).injective

/-- The composite coefficient embedding `k[x] → k(x) → k(x)(√H)`. -/
def quadraticCoefficientMap46 : k[X] →+* F46 :=
  (algebraMap (RatFunc k) F46).comp (algebraMap k[X] (RatFunc k))

theorem quadraticCoefficientMap46_eq_algebraMap (P : k[X]) :
    quadraticCoefficientMap46 H P = algebraMap k[X] F46 P := by
  exact IsScalarTower.algebraMap_apply k[X] (RatFunc k) F46 P

/-- Map an outer polynomial in `y` from `k[x][y]` into the quadratic
working field. -/
def sourceToQuadratic46 (p : k[X][X]) : F46[X] :=
  p.map (quadraticCoefficientMap46 H)

/-- Every embedded source coefficient is fixed by the deck involution. -/
theorem alignedQuadraticDeck46_coefficient (P : k[X]) :
    alignedQuadraticDeck46 H (quadraticCoefficientMap46 H P) =
      quadraticCoefficientMap46 H P := by
  exact alignedQuadraticDeck46_base H
    (algebraMap k[X] (RatFunc k) P)

@[simp]
theorem alignedQuadraticDeck46_ground (c : k) :
    alignedQuadraticDeck46 H (algebraMap k F46 c) =
      algebraMap k F46 c := by
  rw [IsScalarTower.algebraMap_apply k (RatFunc k) F46]
  exact alignedQuadraticDeck46_base H (algebraMap k (RatFunc k) c)

theorem sourceToQuadratic46_map_deck (p : k[X][X]) :
    (sourceToQuadratic46 H p).map (alignedQuadraticDeck46 H) =
      sourceToQuadratic46 H p := by
  ext n
  simp [sourceToQuadratic46, alignedQuadraticDeck46_coefficient]

/-- The differential on the quadratic field, made explicitly `k`-linear. -/
noncomputable def quadraticDerivativeLinear46 : F46 →ₗ[k] F46 where
  toFun := fun x => Differential.deriv x
  map_add' x y := by
    letI : Algebra ℤ F46 := Ring.toIntAlgebra F46
    exact Differential.deriv.map_add x y
  map_smul' c x := by
    letI : Algebra ℤ F46 := Ring.toIntAlgebra F46
    have hc : Differential.deriv (algebraMap k F46 c) = 0 :=
      GCD369BaseConstants c
    rw [Algebra.smul_def, Algebra.smul_def, Derivation.leibniz, hc]
    simp

/-- The selected `k`-derivation on `k(x)(√H)`. -/
noncomputable def quadraticDerivation46 : Derivation k F46 F46 := by
  letI : Algebra ℤ F46 := Ring.toIntAlgebra F46
  exact Derivation.mk' (quadraticDerivativeLinear46 H) (by
    intro x y
    exact Differential.deriv.leibniz x y)

@[simp]
theorem quadraticDerivation46_apply (x : F46) :
    quadraticDerivation46 H x = Differential.deriv x := rfl

theorem coefficientDeriv_quadraticDerivation46 (p : F46[X]) :
    coefficientDeriv (quadraticDerivation46 H) p =
      Differential.mapCoeffs p := by
  ext n
  simp [coeff_coefficientDeriv, quadraticDerivation46_apply,
    Differential.coeff_mapCoeffs]

/-- The literal source bracket maps to the selected quadratic differential
field without changing its constant value. -/
theorem differentialJacobian_sourceToQuadratic46
    (p q : k[X][X]) (j : k)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j)) :
    differentialJacobian (quadraticDerivation46 H)
        (sourceToQuadratic46 H p)
        (sourceToQuadratic46 H q) =
      C (algebraMap k F46 j) := by
  have hmap := GCD369MapSourceBracket
    (L := F46) p q (C j) hD
  rw [differentialJacobian,
    coefficientDeriv_quadraticDerivation46,
    coefficientDeriv_quadraticDerivation46]
  simpa [sourceToQuadratic46, quadraticCoefficientMap46,
    IsScalarTower.algebraMap_apply k (RatFunc k) F46] using hmap

/-- After `y=(z-r)/h`, the quadratic-field source bracket is divided by
`h`, exactly as in the rational square branch. -/
theorem differentialJacobian_affineDepress_sourceToQuadratic46
    (p q : k[X][X]) (j : k) (h r : F46) (hh : h ≠ 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j)) :
    differentialJacobian (quadraticDerivation46 H)
        (affineDepress46 h r (sourceToQuadratic46 H p))
        (affineDepress46 h r (sourceToQuadratic46 H q)) =
      C (algebraMap k F46 j / h) := by
  have hsource := differentialJacobian_sourceToQuadratic46
    H p q j hD
  have haffine := GCD369AffineBracket
    (sourceToQuadratic46 H p)
    (sourceToQuadratic46 H q) h r (algebraMap k F46 j) hh (by
      rw [differentialJacobian,
        coefficientDeriv_quadraticDerivation46,
        coefficientDeriv_quadraticDerivation46] at hsource
      exact hsource)
  have ht : (X - C r) * C h⁻¹ = C h⁻¹ * (X - C r) := by ring
  change Differential.mapCoeffs
        ((sourceToQuadratic46 H p).comp ((X - C r) * C h⁻¹)) *
      derivative
        ((sourceToQuadratic46 H q).comp ((X - C r) * C h⁻¹)) -
      derivative
        ((sourceToQuadratic46 H p).comp ((X - C r) * C h⁻¹)) *
      Differential.mapCoeffs
        ((sourceToQuadratic46 H q).comp ((X - C r) * C h⁻¹)) = _
  rw [ht]
  exact haffine

/-- A mapped literal quartic with leading coefficient `h⁴` is the raw
quartic used by the generic depression identity. -/
theorem sourceToQuadratic46_eq_rawQuartic
    (p : k[X][X]) (h : F46) (hp : p.natDegree = 4)
    (htop : quadraticCoefficientMap46 H (p.coeff 4) = h ^ 4) :
    sourceToQuadratic46 H p = rawQuartic46 h
      (quadraticCoefficientMap46 H (p.coeff 3))
      (quadraticCoefficientMap46 H (p.coeff 2))
      (quadraticCoefficientMap46 H (p.coeff 1))
      (quadraticCoefficientMap46 H (p.coeff 0)) := by
  ext n
  by_cases hn : n ≤ 4
  · interval_cases n <;>
      simp [sourceToQuadratic46, rawQuartic46, htop, coeff_add, coeff_C,
        coeff_C_mul, coeff_mul_X_pow', coeff_X, coeff_X_pow] <;>
      rw [← Polynomial.C_pow, coeff_C] <;> simp
  · have hn4 : 4 < n := by omega
    have hz : p.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [sourceToQuadratic46, rawQuartic46, hz, coeff_add, coeff_C,
      coeff_C_mul, coeff_mul_X_pow', coeff_X, coeff_X_pow,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega,
      show n ≠ 3 by omega, show n ≠ 4 by omega,
      show n - 3 ≠ 0 by omega, show n - 2 ≠ 0 by omega,
      show 1 ≠ n by omega] <;>
      rw [← Polynomial.C_pow, coeff_C] <;>
      simp [show n - 4 ≠ 0 by omega]

/-- The analogous raw sextic expansion. -/
theorem sourceToQuadratic46_eq_rawSextic
    (q : k[X][X]) (h : F46) (hq : q.natDegree = 6)
    (htop : quadraticCoefficientMap46 H (q.coeff 6) = h ^ 6) :
    sourceToQuadratic46 H q = rawSextic46 h
      (quadraticCoefficientMap46 H (q.coeff 5))
      (quadraticCoefficientMap46 H (q.coeff 4))
      (quadraticCoefficientMap46 H (q.coeff 3))
      (quadraticCoefficientMap46 H (q.coeff 2))
      (quadraticCoefficientMap46 H (q.coeff 1))
      (quadraticCoefficientMap46 H (q.coeff 0)) := by
  ext n
  by_cases hn : n ≤ 6
  · interval_cases n <;>
      simp [sourceToQuadratic46, rawSextic46, htop, coeff_add, coeff_C,
        coeff_C_mul, coeff_mul_X_pow', coeff_X, coeff_X_pow] <;>
      rw [← Polynomial.C_pow, coeff_C] <;> simp
  · have hn6 : 6 < n := by omega
    have hz : q.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [sourceToQuadratic46, rawSextic46, hz, coeff_add, coeff_C,
      coeff_C_mul, coeff_mul_X_pow', coeff_X, coeff_X_pow,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega,
      show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega,
      show n ≠ 6 by omega, show n - 5 ≠ 0 by omega,
      show n - 4 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
      show n - 2 ≠ 0 by omega, show 1 ≠ n by omega] <;>
      rw [← Polynomial.C_pow, coeff_C] <;>
      simp [show n - 6 ≠ 0 by omega]

/-- Deck equivariance of the affine depression: changing the sign of the
quadratic root is the same as changing `z` to `-z`. -/
theorem sourceAffineDepress_map_deck46
    (p : k[X][X]) (h r : F46)
    (hh : alignedQuadraticDeck46 H h = -h)
    (hr : alignedQuadraticDeck46 H r = -r) :
    (affineDepress46 h r (sourceToQuadratic46 H p)).map
        (alignedQuadraticDeck46 H) =
      (affineDepress46 h r (sourceToQuadratic46 H p)).comp (-X) := by
  rw [affineDepress46, Polynomial.map_comp,
    sourceToQuadratic46_map_deck]
  rw [Polynomial.comp_assoc]
  congr 1
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, map_inv₀,
    C_comp, X_comp, sub_comp, mul_comp, neg_comp]
  change (X - C (alignedQuadraticDeck46 H r)) *
      C (alignedQuadraticDeck46 H h)⁻¹ = (-X - C r) * C h⁻¹
  rw [hh, hr]
  simp only [inv_neg, C_neg]
  ring

/-- Coefficientwise form of deck equivariance for a depressed quartic. -/
theorem depressedQuartic_deckParity46 (A B C0 : F46)
    (hmap : (depressedQuartic46 A B C0).map
        (alignedQuadraticDeck46 H) =
      (depressedQuartic46 A B C0).comp (-X)) :
    alignedQuadraticDeck46 H A = A ∧
    alignedQuadraticDeck46 H B = -B ∧
    alignedQuadraticDeck46 H C0 = C0 := by
  have hshape : (depressedQuartic46 A B C0).comp (-X) =
      depressedQuartic46 A (-B) C0 := by
    simp [depressedQuartic46]
    ring
  rw [hshape] at hmap
  have h2 := congrArg (fun f : F46[X] => f.coeff 2) hmap
  have h1 := congrArg (fun f : F46[X] => f.coeff 1) hmap
  have h0 := congrArg (fun f : F46[X] => f.coeff 0) hmap
  norm_num [depressedQuartic46, coeff_add, coeff_C, coeff_C_mul,
    coeff_mul_X_pow', coeff_X, coeff_X_pow] at h2 h1 h0
  exact ⟨h2, h1, h0⟩

/-- The sextic coefficients have alternating parity under the same deck
involution. -/
theorem depressedSextic_deckParity46 (L P0 Q0 R0 S0 T0 : F46)
    (hmap : (depressedSextic46 L P0 Q0 R0 S0 T0).map
        (alignedQuadraticDeck46 H) =
      (depressedSextic46 L P0 Q0 R0 S0 T0).comp (-X)) :
    alignedQuadraticDeck46 H L = -L ∧
    alignedQuadraticDeck46 H P0 = P0 ∧
    alignedQuadraticDeck46 H Q0 = -Q0 ∧
    alignedQuadraticDeck46 H R0 = R0 ∧
    alignedQuadraticDeck46 H S0 = -S0 ∧
    alignedQuadraticDeck46 H T0 = T0 := by
  have hshape : (depressedSextic46 L P0 Q0 R0 S0 T0).comp (-X) =
      depressedSextic46 (-L) P0 (-Q0) R0 (-S0) T0 := by
    simp [depressedSextic46]
    ring
  rw [hshape] at hmap
  have h5 := congrArg (fun f : F46[X] => f.coeff 5) hmap
  have h4 := congrArg (fun f : F46[X] => f.coeff 4) hmap
  have h3 := congrArg (fun f : F46[X] => f.coeff 3) hmap
  have h2 := congrArg (fun f : F46[X] => f.coeff 2) hmap
  have h1 := congrArg (fun f : F46[X] => f.coeff 1) hmap
  have h0 := congrArg (fun f : F46[X] => f.coeff 0) hmap
  norm_num [depressedSextic46, coeff_add, coeff_C, coeff_C_mul,
    coeff_mul_X_pow', coeff_X, coeff_X_pow] at h5 h4 h3 h2 h1 h0
  exact ⟨h5, h4, h3, h2, h1, h0⟩

theorem eval_affineDepress46_centerField
    (h r : F46) (f : F46[X]) :
    (affineDepress46 h r f).eval r = f.coeff 0 := by
  simpa [affineDepress46] using (coeff_zero_eq_eval_zero f).symm

/-- The two boundary values of a literal quadratic-field source remain
images of explicit polynomials in `k[x]`. -/
theorem alignedDepressedLiteralBoundariesQuadratic46
    (p q : k[X][X]) (h r A B C0 : F46)
    (alpha beta gamma delta epsilon : k)
    (hpDep : affineDepress46 h r (sourceToQuadratic46 H p) =
      depressedQuartic46 A B C0)
    (hqDep : affineDepress46 h r (sourceToQuadratic46 H q) =
      depressedSextic46 0
        (integratedP46 A (algebraMap k F46 alpha))
        (integratedQ46 0 A B (algebraMap k F46 beta))
        (integratedR46 0 A B C0 (algebraMap k F46 alpha)
          (algebraMap k F46 gamma))
        (integratedS46 0 A B C0 (algebraMap k F46 alpha)
          (algebraMap k F46 beta) (algebraMap k F46 delta))
        (integratedT46 0 A B C0 (algebraMap k F46 alpha)
          (algebraMap k F46 beta) (algebraMap k F46 gamma)
          (algebraMap k F46 epsilon))) :
    boundaryD46 r (translatedQ46 r A) B (A ^ 2 - 4 * C0) =
        quadraticCoefficientMap46 H (p.coeff 0) ∧
    boundaryE46 0 r (translatedQ46 r A) B (A ^ 2 - 4 * C0)
        (algebraMap k F46 beta) (algebraMap k F46 gamma)
        (algebraMap k F46 delta) =
      quadraticCoefficientMap46 H
        (q.coeff 0 - C alpha * p.coeff 0 - C epsilon) := by
  let U : F46 := A ^ 2 - 4 * C0
  have hC : discriminantC46 A U = C0 := by
    simp only [discriminantC46, U]
    ring
  have hpCenter := congrArg (fun f : F46[X] => f.eval r) hpDep
  have hqCenter := congrArg (fun f : F46[X] => f.eval r) hqDep
  rw [eval_affineDepress46_centerField] at hpCenter hqCenter
  simp only [sourceToQuadratic46, coeff_map] at hpCenter hqCenter
  have hDcurve :=
    eval_depressedQuartic46_discriminant_eq_boundaryD46 r A B U
  have hEcurve := eval_integratedSextic46_discriminant_eq_boundaryE46
    0 r A B U (algebraMap k F46 alpha) (algebraMap k F46 beta)
      (algebraMap k F46 gamma) (algebraMap k F46 delta)
      (algebraMap k F46 epsilon)
  dsimp only at hEcurve
  rw [hC] at hDcurve hEcurve
  constructor
  · simpa only [U] using hDcurve.symm.trans hpCenter.symm
  · have hboundary : boundaryE46 0 r (translatedQ46 r A) B U
        (algebraMap k F46 beta) (algebraMap k F46 gamma)
        (algebraMap k F46 delta) =
        quadraticCoefficientMap46 H (q.coeff 0) -
          algebraMap k F46 alpha * quadraticCoefficientMap46 H (p.coeff 0) -
          algebraMap k F46 epsilon := by
      rw [← hEcurve, ← hqCenter, ← hpCenter]
    rw [hboundary]
    simp only [map_sub, map_mul, map_C, quadraticCoefficientMap46]
    simp [IsScalarTower.algebraMap_apply k (RatFunc k) F46]

/-- The five upper rows integrate over the original algebraically closed
ground field, even though the trajectory itself lives in the quadratic
function field. -/
theorem alignedDepressedIntegratesQuadratic46
    (A B C0 P0 Q0 R0 S0 T0 terminal : F46)
    (hbracket : differentialJacobian (quadraticDerivation46 H)
        (depressedQuartic46 A B C0)
        (depressedSextic46 0 P0 Q0 R0 S0 T0) = C terminal) :
    ∃ alpha beta gamma delta epsilon : k,
      P0 = integratedP46 A (algebraMap k F46 alpha) ∧
      Q0 = integratedQ46 0 A B (algebraMap k F46 beta) ∧
      R0 = integratedR46 0 A B C0 (algebraMap k F46 alpha)
        (algebraMap k F46 gamma) ∧
      S0 = integratedS46 0 A B C0 (algebraMap k F46 alpha)
        (algebraMap k F46 beta) (algebraMap k F46 delta) ∧
      T0 = integratedT46 0 A B C0 (algebraMap k F46 alpha)
        (algebraMap k F46 beta) (algebraMap k F46 gamma)
        (algebraMap k F46 epsilon) := by
  rcases alignedDepressedResiduals_deriv_zeroField46
      (quadraticDerivation46 H) A B C0 P0 Q0 R0 S0 T0 terminal
      hbracket with ⟨halpha0, hbeta0, hgamma0, hdelta0, hepsilon0⟩
  have halphaD : Differential.deriv
      (alignedAlphaResidualField46 A P0) = 0 := by
    simpa only [quadraticDerivation46_apply] using halpha0
  have hbetaD : Differential.deriv
      (alignedBetaResidualField46 B Q0) = 0 := by
    simpa only [quadraticDerivation46_apply] using hbeta0
  have hgammaD : Differential.deriv
      (alignedGammaResidualField46 A C0 P0 R0) = 0 := by
    simpa only [quadraticDerivation46_apply] using hgamma0
  have hdeltaD : Differential.deriv
      (alignedDeltaResidualField46 A B P0 Q0 S0) = 0 := by
    simpa only [quadraticDerivation46_apply] using hdelta0
  have hepsilonD : Differential.deriv
      (alignedEpsilonResidualField46 A B C0 P0 Q0 R0 T0) = 0 := by
    simpa only [quadraticDerivation46_apply] using hepsilon0
  obtain ⟨alpha, halpha⟩ := alignedQuadraticConstants46 H
    NonsquarePolynomial46.not_sq _ halphaD
  obtain ⟨beta, hbeta⟩ := alignedQuadraticConstants46 H
    NonsquarePolynomial46.not_sq _ hbetaD
  obtain ⟨gamma, hgamma⟩ := alignedQuadraticConstants46 H
    NonsquarePolynomial46.not_sq _ hgammaD
  obtain ⟨delta, hdelta⟩ := alignedQuadraticConstants46 H
    NonsquarePolynomial46.not_sq _ hdeltaD
  obtain ⟨epsilon, hepsilon⟩ := alignedQuadraticConstants46 H
    NonsquarePolynomial46.not_sq _ hepsilonD
  refine ⟨alpha, beta, gamma, delta, epsilon, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← halpha]
    simp only [integratedP46, alignedAlphaResidualField46]
    ring
  · rw [← hbeta]
    simp only [integratedQ46, alignedBetaResidualField46]
    ring
  · rw [← halpha, ← hgamma]
    simp only [integratedR46, alignedAlphaResidualField46,
      alignedGammaResidualField46]
    ring
  · rw [← halpha, ← hbeta, ← hdelta]
    simp only [integratedS46, alignedAlphaResidualField46,
      alignedBetaResidualField46, alignedDeltaResidualField46]
    ring
  · rw [← halpha, ← hbeta, ← hgamma, ← hepsilon]
    simp only [integratedT46, alignedAlphaResidualField46,
      alignedBetaResidualField46, alignedGammaResidualField46,
      alignedEpsilonResidualField46]
    ring

/-- The entire aligned bracket lands on the reviewed coefficient curve with
all seven integration constants in `k`. -/
theorem alignedDepressedCoefficientCurveQuadratic46
    (A B C0 P0 Q0 R0 S0 T0 terminal : F46)
    (hbracket : differentialJacobian (quadraticDerivation46 H)
        (depressedQuartic46 A B C0)
        (depressedSextic46 0 P0 Q0 R0 S0 T0) = C terminal) :
    ∃ alpha beta gamma delta epsilon k2 k1 : k,
      P0 = integratedP46 A (algebraMap k F46 alpha) ∧
      Q0 = integratedQ46 0 A B (algebraMap k F46 beta) ∧
      R0 = integratedR46 0 A B C0 (algebraMap k F46 alpha)
        (algebraMap k F46 gamma) ∧
      S0 = integratedS46 0 A B C0 (algebraMap k F46 alpha)
        (algebraMap k F46 beta) (algebraMap k F46 delta) ∧
      T0 = integratedT46 0 A B C0 (algebraMap k F46 alpha)
        (algebraMap k F46 beta) (algebraMap k F46 gamma)
        (algebraMap k F46 epsilon) ∧
      coefficientCurveTwo46 0 A B (A ^ 2 - 4 * C0)
          (algebraMap k F46 beta) (algebraMap k F46 gamma)
          (algebraMap k F46 delta) = algebraMap k F46 k2 ∧
      coefficientCurveOne46 0 A B (A ^ 2 - 4 * C0)
          (algebraMap k F46 beta) (algebraMap k F46 gamma)
          (algebraMap k F46 delta) = algebraMap k F46 k1 ∧
      eta46 0 A B (A ^ 2 - 4 * C0)
          (algebraMap k F46 beta) (algebraMap k F46 gamma)
          (algebraMap k F46 delta)
          (quadraticDerivation46 H A) (quadraticDerivation46 H B)
          (quadraticDerivation46 H (A ^ 2 - 4 * C0)) = terminal := by
  obtain ⟨alpha, beta, gamma, delta, epsilon,
      hP, hQ, hR, hS, hT⟩ :=
    alignedDepressedIntegratesQuadratic46 H
      A B C0 P0 Q0 R0 S0 T0 terminal hbracket
  let U : F46 := A ^ 2 - 4 * C0
  have hC : discriminantC46 A U = C0 := by
    simp only [discriminantC46, U]
    ring
  have hconst (c : k) :
      quadraticDerivation46 H (algebraMap k F46 c) = 0 := by
    simp only [quadraticDerivation46_apply]
    exact GCD369BaseConstants c
  have hshape := differentialJacobian_integratedDiscriminant46_eq
    (quadraticDerivation46 H) 0 A B U
      (algebraMap k F46 alpha) (algebraMap k F46 beta)
      (algebraMap k F46 gamma) (algebraMap k F46 delta)
      (algebraMap k F46 epsilon)
      (by simp) (hconst alpha) (hconst beta) (hconst gamma)
      (hconst delta) (hconst epsilon)
  dsimp only at hshape
  rw [hC] at hshape
  have hbracket' := hbracket
  rw [hP, hQ, hR, hS, hT, hshape] at hbracket'
  have h2 := congrArg (fun f : F46[X] => f.coeff 2) hbracket'
  have h1 := congrArg (fun f : F46[X] => f.coeff 1) hbracket'
  have h0 := congrArg (fun f : F46[X] => f.coeff 0) hbracket'
  norm_num [coeff_add, coeff_C, coeff_C_mul, coeff_mul_X_pow',
    coeff_X, coeff_X_pow] at h2 h1 h0
  have h2D : Differential.deriv
      (coefficientCurveTwo46 0 A B U (algebraMap k F46 beta)
        (algebraMap k F46 gamma) (algebraMap k F46 delta)) = 0 := by
    simpa only [quadraticDerivation46_apply] using h2
  have h1D : Differential.deriv
      (coefficientCurveOne46 0 A B U (algebraMap k F46 beta)
        (algebraMap k F46 gamma) (algebraMap k F46 delta)) = 0 := by
    simpa only [quadraticDerivation46_apply] using h1
  obtain ⟨k2, hk2⟩ := alignedQuadraticConstants46 H
    NonsquarePolynomial46.not_sq _ h2D
  obtain ⟨k1, hk1⟩ := alignedQuadraticConstants46 H
    NonsquarePolynomial46.not_sq _ h1D
  refine ⟨alpha, beta, gamma, delta, epsilon, k2, k1,
    hP, hQ, hR, hS, hT, ?_, ?_, ?_⟩
  · simpa only [U] using hk2
  · simpa only [U] using hk1
  · simpa only [U, quadraticDerivation46_apply] using h0

/-- Source-facing data for the aligned nonsquare branch after deck parity
has collapsed it to `beta = delta = k₂ = 0`. -/
structure NonsquareAlignedSourceCurveData46
    (p q : k[X][X]) (j : k) where
  r : F46
  A : F46
  B : F46
  C0 : F46
  alpha : k
  gamma : k
  epsilon : k
  k1 : k
  r_odd : alignedQuadraticDeck46 H r = -r
  A_even : alignedQuadraticDeck46 H A = A
  B_odd : alignedQuadraticDeck46 H B = -B
  C_even : alignedQuadraticDeck46 H C0 = C0
  quartic_eq :
    affineDepress46 (AdjoinRoot.root (alignedQuadraticPolynomial46 H)) r
        (sourceToQuadratic46 H p) = depressedQuartic46 A B C0
  sextic_eq :
    affineDepress46 (AdjoinRoot.root (alignedQuadraticPolynomial46 H)) r
        (sourceToQuadratic46 H q) =
      depressedSextic46 0
        (integratedP46 A (algebraMap k F46 alpha))
        (integratedQ46 0 A B 0)
        (integratedR46 0 A B C0 (algebraMap k F46 alpha)
          (algebraMap k F46 gamma))
        (integratedS46 0 A B C0 (algebraMap k F46 alpha) 0 0)
        (integratedT46 0 A B C0 (algebraMap k F46 alpha) 0
          (algebraMap k F46 gamma) (algebraMap k F46 epsilon))
  curveTwo : coefficientCurveTwo46 0 A B (A ^ 2 - 4 * C0)
      0 (algebraMap k F46 gamma) 0 = 0
  curveOne : coefficientCurveOne46 0 A B (A ^ 2 - 4 * C0)
      0 (algebraMap k F46 gamma) 0 = algebraMap k F46 k1
  boundaryD : boundaryD46 r (translatedQ46 r A) B (A ^ 2 - 4 * C0) =
    quadraticCoefficientMap46 H (p.coeff 0)
  boundaryE : boundaryE46 0 r (translatedQ46 r A) B (A ^ 2 - 4 * C0)
      0 (algebraMap k F46 gamma) 0 =
    quadraticCoefficientMap46 H
      (q.coeff 0 - C alpha * p.coeff 0 - C epsilon)
  lastRow : AdjoinRoot.root (alignedQuadraticPolynomial46 H) *
      eta46 0 A B (A ^ 2 - 4 * C0) 0 (algebraMap k F46 gamma) 0
        (quadraticDerivation46 H A) (quadraticDerivation46 H B)
        (quadraticDerivation46 H (A ^ 2 - 4 * C0)) =
      algebraMap k F46 j

/-- A literal aligned source in the nonsquare branch produces the complete
final-component package. -/
theorem nonsquareAlignedSourceCurveData46
    (p q : k[X][X]) (j : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 6)
    (hp4 : p.coeff 4 = H ^ 2) (hq6 : q.coeff 6 = H ^ 3)
    (haligned : (3 : k[X]) * p.coeff 3 * H -
      (2 : k[X]) * q.coeff 5 = 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j)) :
    Nonempty (NonsquareAlignedSourceCurveData46 H p q j) := by
  let h : F46 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  let a3 : F46 := quadraticCoefficientMap46 H (p.coeff 3)
  let a2 : F46 := quadraticCoefficientMap46 H (p.coeff 2)
  let a1 : F46 := quadraticCoefficientMap46 H (p.coeff 1)
  let a0 : F46 := quadraticCoefficientMap46 H (p.coeff 0)
  let b5 : F46 := quadraticCoefficientMap46 H (q.coeff 5)
  let b4 : F46 := quadraticCoefficientMap46 H (q.coeff 4)
  let b3 : F46 := quadraticCoefficientMap46 H (q.coeff 3)
  let b2 : F46 := quadraticCoefficientMap46 H (q.coeff 2)
  let b1 : F46 := quadraticCoefficientMap46 H (q.coeff 1)
  let b0 : F46 := quadraticCoefficientMap46 H (q.coeff 0)
  let r : F46 := quarticDepressionR46 h a3
  let A : F46 := depressedA46 h r a3 a2
  let B : F46 := depressedB46 h r a3 a2 a1
  let C0 : F46 := depressedC46 h r a3 a2 a1 a0
  let L : F46 := depressedL46 h r b5
  let P0 : F46 := depressedP46 h r b5 b4
  let Q0 : F46 := depressedQ46 h r b5 b4 b3
  let R0 : F46 := depressedR46 h r b5 b4 b3 b2
  let S0 : F46 := depressedS46 h r b5 b4 b3 b2 b1
  let T0 : F46 := depressedT46 h r b5 b4 b3 b2 b1 b0
  have hHne : H ≠ 0 := by
    intro hzero
    exact NonsquarePolynomial46.not_sq (H := H) (0 : k[X]) (by
      simp [hzero])
  have hrootSq : h ^ 2 = quadraticCoefficientMap46 H H := by
    exact alignedQuadraticRoot_sq46 H
  have hphi : Function.Injective (quadraticCoefficientMap46 H) :=
    (algebraMap (RatFunc k) F46).injective.comp
      (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  have hh : h ≠ 0 := by
    intro hz
    have : quadraticCoefficientMap46 H H = 0 := by
      rw [← hrootSq, hz]
      simp
    exact hHne (hphi (this.trans (map_zero _).symm))
  have hpTop : quadraticCoefficientMap46 H (p.coeff 4) = h ^ 4 := by
    rw [hp4, map_pow, ← hrootSq]
    ring
  have hqTop : quadraticCoefficientMap46 H (q.coeff 6) = h ^ 6 := by
    rw [hq6, map_pow, ← hrootSq]
    ring
  have hpDep : affineDepress46 h r (sourceToQuadratic46 H p) =
      depressedQuartic46 A B C0 := by
    rw [sourceToQuadratic46_eq_rawQuartic H p h hp hpTop]
    exact affineDepress_rawQuartic46 h r a3 a2 a1 a0 hh rfl
  have hqDep : affineDepress46 h r (sourceToQuadratic46 H q) =
      depressedSextic46 L P0 Q0 R0 S0 T0 := by
    rw [sourceToQuadratic46_eq_rawSextic H q h hq hqTop]
    exact affineDepress_rawSextic46 h r b5 b4 b3 b2 b1 b0 hh
  have halignedF : 3 * a3 * h ^ 2 - 2 * b5 = 0 := by
    have hmapped := congrArg (quadraticCoefficientMap46 H) haligned
    simp only [map_sub, map_mul, map_ofNat, map_zero] at hmapped
    rw [hrootSq]
    simpa only [a3, b5] using hmapped
  have hL : L = 0 :=
    depressedL46_eq_zero_of_aligned h a3 b5 hh halignedF
  have hbracket := differentialJacobian_affineDepress_sourceToQuadratic46
    H p q j h r hh hD
  rw [hpDep, hqDep, hL] at hbracket
  obtain ⟨alpha, beta, gamma, delta, epsilon, k2, k1,
      hP, hQ, hR, hS, hT, hcurve2, hcurve1, heta⟩ :=
    alignedDepressedCoefficientCurveQuadratic46 H
      A B C0 P0 Q0 R0 S0 T0 (algebraMap k F46 j / h) hbracket
  have hrOdd : alignedQuadraticDeck46 H r = -r := by
    simp only [r, h, quarticDepressionR46, map_div₀, map_mul, map_ofNat,
      map_pow, alignedQuadraticDeck46_root,
      alignedQuadraticDeck46_coefficient, a3]
    field_simp [hh]
  have hpMap := sourceAffineDepress_map_deck46 H p h r
    (alignedQuadraticDeck46_root H) hrOdd
  rw [hpDep] at hpMap
  obtain ⟨hAEven, hBOdd, hCEven⟩ :=
    depressedQuartic_deckParity46 H A B C0 hpMap
  have hqMap := sourceAffineDepress_map_deck46 H q h r
    (alignedQuadraticDeck46_root H) hrOdd
  rw [hqDep] at hqMap
  obtain ⟨_hLOdd, _hPEven, hQOdd, _hREven, hSOdd, _hTEven⟩ :=
    depressedSextic_deckParity46 H L P0 Q0 R0 S0 T0 hqMap
  have hQmap := congrArg (alignedQuadraticDeck46 H) hQ
  simp only [integratedQ46, map_add, map_mul, map_div₀, map_ofNat,
    map_zero, hQOdd, hBOdd, alignedQuadraticDeck46_ground] at hQmap
  have hbetaF : algebraMap k F46 beta = 0 := by
    have hQ' : Q0 = (3 / 2 : F46) * B + algebraMap k F46 beta := by
      simpa [integratedQ46] using hQ
    rw [hQ'] at hQmap
    linear_combination (-1 / 2 : F46) * hQmap
  have hbeta : beta = 0 := (algebraMap k F46).injective (by
    simpa using hbetaF)
  have hSmap := congrArg (alignedQuadraticDeck46 H) hS
  simp only [integratedS46, map_add, map_mul, map_div₀, map_pow,
    map_ofNat, map_zero, hAEven, hBOdd, hSOdd,
    alignedQuadraticDeck46_ground, hbeta] at hSmap
  have hdeltaF : algebraMap k F46 delta = 0 := by
    have hS' := hS
    simp only [integratedS46, hbeta, map_zero, mul_zero, add_zero] at hS'
    linear_combination (-1 / 2 : F46) * hSmap - (1 / 2 : F46) * hS'
  have hdelta : delta = 0 := (algebraMap k F46).injective (by
    simpa using hdeltaF)
  have hcurve2map := congrArg (alignedQuadraticDeck46 H) hcurve2
  simp only [coefficientCurveTwo46, hbeta, hdelta, map_zero, mul_zero,
    zero_mul, add_zero, sub_zero, map_add, map_sub, map_mul, map_pow,
    map_div₀, map_ofNat, hAEven, hBOdd, hCEven,
    alignedQuadraticDeck46_ground] at hcurve2map
  have hk2F : algebraMap k F46 k2 = 0 := by
    have hcurve2' := hcurve2
    simp only [hbeta, hdelta, map_zero, coefficientCurveTwo46] at hcurve2'
    linear_combination (-1 / 2 : F46) * hcurve2map -
      (1 / 2 : F46) * hcurve2'
  have hk2 : k2 = 0 := (algebraMap k F46).injective (by simpa using hk2F)
  have hqIntegrated : affineDepress46 h r (sourceToQuadratic46 H q) =
      depressedSextic46 0
        (integratedP46 A (algebraMap k F46 alpha))
        (integratedQ46 0 A B 0)
        (integratedR46 0 A B C0 (algebraMap k F46 alpha)
          (algebraMap k F46 gamma))
        (integratedS46 0 A B C0 (algebraMap k F46 alpha) 0 0)
        (integratedT46 0 A B C0 (algebraMap k F46 alpha) 0
          (algebraMap k F46 gamma) (algebraMap k F46 epsilon)) := by
    rw [hqDep, hL, hP, hQ, hR, hS, hT, hbeta, hdelta]
    simp
  have hboundaries := alignedDepressedLiteralBoundariesQuadratic46 H
    p q h r A B C0 alpha beta gamma delta epsilon hpDep (by
      rw [hqDep, hL, hP, hQ, hR, hS, hT])
  have hlast : h * eta46 0 A B (A ^ 2 - 4 * C0) 0
      (algebraMap k F46 gamma) 0
      (quadraticDerivation46 H A) (quadraticDerivation46 H B)
      (quadraticDerivation46 H (A ^ 2 - 4 * C0)) =
      algebraMap k F46 j := by
    rw [hbeta, hdelta] at heta
    simp only [map_zero] at heta
    rw [heta]
    field_simp [hh]
  exact ⟨{
    r := r
    A := A
    B := B
    C0 := C0
    alpha := alpha
    gamma := gamma
    epsilon := epsilon
    k1 := k1
    r_odd := hrOdd
    A_even := hAEven
    B_odd := hBOdd
    C_even := hCEven
    quartic_eq := hpDep
    sextic_eq := hqIntegrated
    curveTwo := by simpa [hbeta, hdelta, hk2] using hcurve2
    curveOne := by simpa [hbeta, hdelta] using hcurve1
    boundaryD := hboundaries.1
    boundaryE := by simpa [hbeta, hdelta] using hboundaries.2
    lastRow := hlast
  }⟩

end QuadraticSource

end Max11DegreeRoutes
