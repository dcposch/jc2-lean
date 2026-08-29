import LowScaleOtherLeaves
import LowScale810ScaleTwoSecondFace

/-! # Scale-zero source packet for the normalized `(8,10)`, `H = 0` leaf

The constant-scale consecutive adapter in `LowScaleOtherLeaves` already gives
polynomial representatives of every affine-depressed coefficient, uniformly
in the polynomial center.  This file specializes that adapter to the
octic-decic pair and extracts the first Keller-integral/Newton degree
`10` constraints that actually cut the route: the source discriminator `N`
is a ground-field constant, and after adjoining a square root of the core
the cleared first octic/decic defect is likewise a ground-field constant.

No total-degree or twice-prime theorem is used.  The packet does not close
the leaf: the next missing input is the degree-`14` residual of the same
monic depression.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

section ScaleZeroSource810

variable {k : Type*} [Field k] [CharZero k]

/-! ## Reusable constant-scale source bridge -/

/-- Polynomial coefficient packet of a constant-scale affine depression of
a normalized `(8,10)` source.  Every coefficient of both transformed
source polynomials has a literal representative in `k[x]`. -/
def ScaleZero810AffineDepressPolynomialPacket
    (P Q : MvPolynomial (Fin 2) k) (h : k[X]) : Prop :=
  ∃ t : k, t ≠ 0 ∧ h = Polynomial.C t ∧
    ∀ (r0 : k[X]) (n : ℕ), ∃ pn qn : k[X],
      algebraMap k[X] (RatFunc k) pn =
          (affineDepress46 (RatFunc.C t)
            (algebraMap k[X] (RatFunc k) r0)
            (sourceToRatFunc46
              ((Polynomial.Bivariate.equivMvPolynomial k).symm P))).coeff n ∧
        algebraMap k[X] (RatFunc k) qn =
          (affineDepress46 (RatFunc.C t)
            (algebraMap k[X] (RatFunc k) r0)
            (sourceToRatFunc46
              ((Polynomial.Bivariate.equivMvPolynomial k).symm Q))).coeff n

/-- Degree-independent constant-scale adapter, specialized to the
normalized `(8,10)` leaf. -/
theorem normalized810ScaleZero_affineDepress_polynomialRepresentatives
    {P Q : MvPolynomial (Fin 2) k} {h : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q h 0) :
    ScaleZero810AffineDepressPolynomialPacket P Q h :=
  normalizedConsecutiveScaleZero_affineDepress_polynomialRepresentatives
    hsource

/-- The same packet, evaluated at the canonical octic-style polynomial
center `r0 = ((8 t⁷)⁻¹) p₇` of the constant core. -/
theorem normalized810ScaleZero_exists_octicCenterPolynomialPacket
    {P Q : MvPolynomial (Fin 2) k} {h : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q h 0) :
    ∃ (t : k) (r0 : k[X]),
      t ≠ 0 ∧ h = Polynomial.C t ∧
      r0 = Polynomial.C ((8 * t ^ 7)⁻¹) *
        ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 ∧
      ∀ n : ℕ, ∃ pn qn : k[X],
        algebraMap k[X] (RatFunc k) pn =
            (affineDepress46 (RatFunc.C t)
              (algebraMap k[X] (RatFunc k) r0)
              (sourceToRatFunc46
                ((Polynomial.Bivariate.equivMvPolynomial k).symm P))).coeff n ∧
          algebraMap k[X] (RatFunc k) qn =
            (affineDepress46 (RatFunc.C t)
              (algebraMap k[X] (RatFunc k) r0)
              (sourceToRatFunc46
                ((Polynomial.Bivariate.equivMvPolynomial k).symm Q))).coeff n := by
  obtain ⟨t, ht, hC, hcoeff⟩ :=
    normalized810ScaleZero_affineDepress_polynomialRepresentatives hsource
  let r0 : k[X] :=
    Polynomial.C ((8 * t ^ 7)⁻¹) *
      ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7
  exact ⟨t, r0, ht, hC, rfl, hcoeff r0⟩

/-! ## First Keller integral: the discriminator is a ground constant -/

/-- At scale zero the common core is constant, so the `(8,10)`
discriminator row collapses to `N' = 0`. -/
theorem scaleZero_discriminator_exists_C_810
    {p q : k[X][X]} {j : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0) (hHdegree : H.natDegree = 0)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5) :
    ∃ lambda : k,
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
        Polynomial.C lambda := by
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hHdegree
  have hHder : H.derivative = 0 := by
    rw [← hc, derivative_C]
  let N : k[X] :=
    (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9
  have hrow :
      (2 : k[X]) * H * N.derivative -
          (9 : k[X]) * N * H.derivative = 0 := by
    simpa only [N] using
      imprimitiveDiscriminatorRow_eq_zero_810 hp hq hjac hH hp8 hq10
  have hrow0 : (2 : k[X]) * H * N.derivative = 0 := by
    simpa [hHder] using hrow
  have h2 : (2 : k[X]) ≠ 0 := two_ne_zero
  have hNder : N.derivative = 0 :=
    (mul_eq_zero.mp hrow0).resolve_left (mul_ne_zero h2 hH)
  refine ⟨N.coeff 0, ?_⟩
  simpa only [N] using Polynomial.eq_C_of_derivative_eq_zero hNder

/-- Source-facing first integral for a normalized scale-zero `(8,10)`
pair: the discriminator is a literal ground-field constant. -/
theorem normalized810ScaleZero_discriminator_exists_C
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ lambda : k,
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda := by
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  simpa only [p, q] using
    scaleZero_discriminator_exists_C_810 hp hq hjac hH hHdegree
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)

/-- Newton degree of the scale-zero discriminator: `natDegree N ≤ 0`. -/
theorem normalized810ScaleZero_discriminator_natDegree_le_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ((5 : k[X]) *
        ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
          H -
      (4 : k[X]) *
        ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9).natDegree
      ≤ 0 := by
  obtain ⟨lambda, hN⟩ :=
    normalized810ScaleZero_discriminator_exists_C hsource
  simp [hN, natDegree_C]

/-- Exact first residual selector: `4 q₉` is an affine function of `p₇`
with constant remainder. -/
theorem normalized810ScaleZero_firstSourceResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ lambda : k,
      (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        (5 : k[X]) *
            ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
              H -
          Polynomial.C lambda := by
  obtain ⟨lambda, hN⟩ :=
    normalized810ScaleZero_discriminator_exists_C hsource
  refine ⟨lambda, ?_⟩
  linear_combination -hN

/-- Aligned/nonzero split of the scale-zero discriminator: it vanishes, or
it is a nonzero ground-field constant. -/
theorem normalized810ScaleZero_discriminatorFirstFace
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let N :=
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9
    N = 0 ∨ ∃ lambda : k, lambda ≠ 0 ∧ N = Polynomial.C lambda := by
  dsimp only
  obtain ⟨lambda, hN⟩ :=
    normalized810ScaleZero_discriminator_exists_C hsource
  by_cases hlambda : lambda = 0
  · left
    simpa only [hlambda, Polynomial.C_0] using hN
  · exact Or.inr ⟨lambda, hlambda, hN⟩

/-! ## Monic first octic/decic residual after a square root of the core -/

/-- On a constant square core the source discriminator is a scalar times
`h⁹`, so the existing ninth-power identities apply with a constant
square root. -/
theorem scaleZero_discriminator_eq_C_mul_ninthPower_810
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5) :
    ∃ lambda : k,
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 := by
  have hHne : H ≠ 0 := by
    rw [hH]
    exact pow_ne_zero 2 (Polynomial.C_ne_zero.mpr ht)
  have hHdegree : H.natDegree = 0 := by
    rw [hH, natDegree_pow, natDegree_C, mul_zero]
  obtain ⟨mu, hmu⟩ :=
    scaleZero_discriminator_exists_C_810 hp hq hjac hHne hHdegree hp8 hq10
  have ht9 : t ^ 9 ≠ 0 := pow_ne_zero 9 ht
  let lambda : k := mu / t ^ 9
  refine ⟨lambda, ?_⟩
  calc
    (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
        Polynomial.C mu := hmu
    _ = Polynomial.C (lambda * t ^ 9) := by
        simp only [lambda, div_mul_cancel₀ mu ht9]
    _ = Polynomial.C lambda * Polynomial.C (t ^ 9) :=
      Polynomial.C_mul
    _ = Polynomial.C lambda * (Polynomial.C t) ^ 9 := by
        simp only [← Polynomial.C_pow]

/-- Strongest exact first residual after the constant-scale source bridge:
the cleared first octic/decic defect is a ground-field constant. -/
theorem scaleZero_firstClearedDefect_exists_C_810
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5) :
    ∃ (lambda alpha : k),
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
          Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedSecondDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (q.coeff 8) lambda =
        Polynomial.C alpha * (Polynomial.C t) ^ 14 := by
  have hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hD
  obtain ⟨lambda, hN⟩ :=
    scaleZero_discriminator_eq_C_mul_ninthPower_810 hp hq hjac ht hH hp8 hq10
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨alpha, halpha⟩ :=
    nonzeroFace810_secondDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  exact ⟨lambda, alpha, hN, halpha⟩

variable [IsAlgClosed k]

/-- Square root of a degree-zero core, written as a constant polynomial. -/
theorem scaleZero_exists_constantSquareRoot_810 {H : k[X]}
    (hH : H ≠ 0) (hHdegree : H.natDegree = 0) :
    ∃ t : k, t ≠ 0 ∧ H = (Polynomial.C t) ^ 2 := by
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hHdegree
  have hcne : c ≠ 0 := by
    intro hzero
    apply hH
    rw [← hc, hzero, Polynomial.C_0]
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq c
    (by norm_num : 0 < 2)
  have htne : t ≠ 0 := by
    intro hzero
    apply hcne
    rw [← ht, hzero, zero_pow (by norm_num : 2 ≠ 0)]
  refine ⟨t, htne, ?_⟩
  rw [← hc, ← Polynomial.C_pow, ht]

/-- Source-facing first residual packet for a normalized scale-zero
`(8,10)` pair. -/
theorem normalized810ScaleZero_exists_firstClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda alpha : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedSecondDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          lambda =
        Polynomial.C alpha * (Polynomial.C t) ^ 14 := by
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  obtain ⟨t, ht, hHsq⟩ :=
    scaleZero_exists_constantSquareRoot_810 hH hHdegree
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨lambda, alpha, hN, halpha⟩ :=
    scaleZero_firstClearedDefect_exists_C_810 hp hq hD ht hHsq
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)
  exact ⟨t, lambda, alpha, ht, hHsq, by simpa only [p, q] using hN,
    by simpa only [p, q] using halpha⟩

/-- Newton degree of the first cleared octic/decic defect at scale zero. -/
theorem normalized810ScaleZero_firstClearedDefect_natDegree_le_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (localClearedSecondDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          lambda).natDegree ≤ 0 := by
  obtain ⟨t, lambda, alpha, ht, hHsq, _hN, halpha⟩ :=
    normalized810ScaleZero_exists_firstClearedDefect hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  have hconst :
      localClearedSecondDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          lambda =
        Polynomial.C (alpha * t ^ 14) := by
    rw [halpha, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) alpha (t ^ 14)).symm
  rw [hconst]
  exact (natDegree_C (alpha * t ^ 14)).le

end ScaleZeroSource810

#print axioms normalized810ScaleZero_affineDepress_polynomialRepresentatives
#print axioms normalized810ScaleZero_exists_octicCenterPolynomialPacket
#print axioms scaleZero_discriminator_exists_C_810
#print axioms normalized810ScaleZero_discriminator_exists_C
#print axioms normalized810ScaleZero_discriminator_natDegree_le_zero
#print axioms normalized810ScaleZero_firstSourceResidual
#print axioms normalized810ScaleZero_discriminatorFirstFace
#print axioms scaleZero_exists_constantSquareRoot_810
#print axioms scaleZero_discriminator_eq_C_mul_ninthPower_810
#print axioms scaleZero_firstClearedDefect_exists_C_810
#print axioms normalized810ScaleZero_exists_firstClearedDefect
#print axioms normalized810ScaleZero_firstClearedDefect_natDegree_le_zero

end Max11DegreeRoutes
