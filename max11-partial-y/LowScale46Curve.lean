import LowScale46NormalForm

/-! # The coefficient curve and boundary cover for the `(4,6)` leaf

This module makes the change of variable `U = A^2 - 4 C` in the integrated
depressed normal form.  It identifies the two first integrals with the
reviewed affine coefficient curve, rewrites the last Jacobian row as the
reviewed one-form `eta`, and derives both translated-origin boundary
equations by direct polynomial evaluation.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section CoefficientCurve

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- Recover the depressed quartic constant coefficient from
`U = A^2 - 4 C`. -/
def discriminantC46 (A U : F) : F := (A ^ 2 - U) / 4

/-- The first reviewed equation of the affine `(A,B,U)` coefficient curve. -/
def coefficientCurveTwo46 (L A B U beta gamma delta : F) : F :=
  (5 / 32 : F) * L * A ^ 3 + (3 / 8 : F) * beta * A ^ 2 -
    (5 / 16 : F) * L * A * U + delta * A +
    (5 / 8 : F) * L * B ^ 2 - (3 / 4 : F) * B * U +
    2 * gamma * B - (3 / 4 : F) * beta * U

/-- The second reviewed equation of the affine `(A,B,U)` coefficient curve. -/
def coefficientCurveOne46 (L A B U beta gamma delta : F) : F :=
  (-5 / 32 : F) * L * A ^ 2 * B - (3 / 4 : F) * A * B ^ 2 -
    (3 / 4 : F) * beta * A * B - (5 / 16 : F) * L * B * U +
    delta * B + (3 / 32 : F) * U ^ 2 - (1 / 2 : F) * gamma * U

/-- The first integrated row is exactly the first coefficient-curve
function after `C = (A^2-U)/4`. -/
theorem firstIntegralTwo46_discriminantC46 (L A B U beta gamma delta : F) :
    firstIntegralTwo46 L A B (discriminantC46 A U) beta gamma delta =
      coefficientCurveTwo46 L A B U beta gamma delta := by
  simp only [firstIntegralTwo46, discriminantC46, coefficientCurveTwo46]
  ring

/-- The second integrated row is exactly the second coefficient-curve
function after `C = (A^2-U)/4`. -/
theorem firstIntegralOne46_discriminantC46 (L A B U beta gamma delta : F) :
    firstIntegralOne46 L A B (discriminantC46 A U) beta gamma delta =
      coefficientCurveOne46 L A B U beta gamma delta := by
  simp only [firstIntegralOne46, discriminantC46, coefficientCurveOne46]
  ring

/-- Coefficient of `dA` in the reviewed final-row one-form. -/
def etaA46 (L A B U beta gamma delta : F) : F :=
  (15 / 64 : F) * L * A ^ 3 - (5 / 16 : F) * L * B ^ 2 -
    (5 / 32 : F) * L * A * U + (3 / 8 : F) * beta * A ^ 2 +
    (3 / 16 : F) * B * U - (1 / 2 : F) * gamma * B +
    (1 / 2 : F) * delta * A

/-- Coefficient of `dB` in the reviewed final-row one-form. -/
def etaB46 (L A B beta : F) : F :=
  (-5 / 16 : F) * L * A * B - (3 / 4 : F) * B ^ 2 -
    (3 / 4 : F) * beta * B

/-- Coefficient of `dU` in the reviewed final-row one-form. -/
def etaU46 (L A U beta delta : F) : F :=
  (-15 / 128 : F) * L * A ^ 2 + (5 / 64 : F) * L * U -
    (3 / 16 : F) * beta * A - (1 / 4 : F) * delta

/-- Evaluation of the reviewed final-row one-form on a tangent vector. -/
def eta46 (L A B U beta gamma delta dA dB dU : F) : F :=
  etaA46 L A B U beta gamma delta * dA +
    etaB46 L A B beta * dB + etaU46 L A U beta delta * dU

/-- After the discriminant-coordinate substitution, the literal last
Jacobian row is precisely the reviewed one-form `eta`. -/
theorem lastIntegratedRow_discriminantC46 (d : Derivation k F F)
    (L A B U alpha beta gamma delta epsilon : F)
    (hL : d L = 0) (halpha : d alpha = 0) (hbeta : d beta = 0)
    (hgamma : d gamma = 0) (hepsilon : d epsilon = 0) :
    let C0 := discriminantC46 A U
    (-B * d (integratedT46 L A B C0 alpha beta gamma epsilon) +
        integratedS46 L A B C0 alpha beta delta * d C0 =
      eta46 L A B U beta gamma delta (d A) (d B) (d U)) := by
  dsimp only
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h3 : d (3 : F) = 0 := d.map_natCast 3
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h16 : d (16 : F) = 0 := d.map_natCast 16
  have h12 : d (1 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h2]
  have h14 : d (1 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h4]
  have h34 : d (3 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h3, h4]
  have h38 : d (3 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h3, h8]
  have h116 : d (1 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h16]
  have h516 : d (5 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, Derivation.leibniz_inv, h5, h16]
  have hC : d (discriminantC46 A U) =
      (1 / 2 : F) * A * d A - (1 / 4 : F) * d U := by
    simp only [discriminantC46, Derivation.leibniz_div,
      Derivation.leibniz_inv, Derivation.leibniz_pow, map_sub, nsmul_eq_mul,
      smul_eq_mul, h4, mul_zero, add_zero]
    ring
  simp only [integratedT46, integratedS46, eta46,
    etaA46, etaB46, etaU46, map_add, map_sub, map_neg,
    Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul,
    hL, halpha, hbeta, hgamma, hepsilon, h12, h14, h34, h38, h116,
    h516, hC, mul_zero, zero_mul, add_zero, zero_add]
  norm_num
  simp only [h116, mul_zero, add_zero]
  simp only [discriminantC46]
  ring

/-- The complete integrated Jacobian in discriminant coordinates: the two
exact curve rows followed by the single one-form row. -/
theorem differentialJacobian_integratedDiscriminant46_eq
    (d : Derivation k F F)
    (L A B U alpha beta gamma delta epsilon : F)
    (hL : d L = 0) (halpha : d alpha = 0) (hbeta : d beta = 0)
    (hgamma : d gamma = 0) (hdelta : d delta = 0)
    (hepsilon : d epsilon = 0) :
    let C0 := discriminantC46 A U
    let P := integratedP46 A alpha
    let Q := integratedQ46 L A B beta
    let R := integratedR46 L A B C0 alpha gamma
    let S := integratedS46 L A B C0 alpha beta delta
    let T := integratedT46 L A B C0 alpha beta gamma epsilon
    differentialJacobian d (depressedQuartic46 A B C0)
        (depressedSextic46 L P Q R S T) =
      Polynomial.C (d (coefficientCurveTwo46 L A B U beta gamma delta)) *
          X ^ 2 +
        Polynomial.C (d (coefficientCurveOne46 L A B U beta gamma delta)) *
          X +
        Polynomial.C
          (eta46 L A B U beta gamma delta (d A) (d B) (d U)) := by
  dsimp only
  rw [differentialJacobian_integrated46_eq d L A B
    (discriminantC46 A U) alpha beta gamma delta epsilon hL halpha hbeta
    hgamma hdelta hepsilon]
  rw [firstIntegralTwo46_discriminantC46,
    firstIntegralOne46_discriminantC46,
    lastIntegratedRow_discriminantC46 d L A B U alpha beta gamma delta
      epsilon hL halpha hbeta hgamma hepsilon]

section BoundaryCover

/-- The translated square coordinate `q = r^2 + A/2`. -/
def translatedQ46 (r A : F) : F := r ^ 2 + (1 / 2 : F) * A

/-- The first polynomial boundary function. -/
def boundaryD46 (r q B U : F) : F :=
  r * B + q ^ 2 - (1 / 4 : F) * U

/-- The second polynomial boundary function, after removing the harmless
target constants `alpha * D + epsilon`. -/
def boundaryE46 (L r q B U beta gamma delta : F) : F :=
  (3 / 8 : F) * L * r ^ 5 - (5 / 4 : F) * L * r ^ 3 * q -
    (1 / 2 : F) * beta * r ^ 3 + (5 / 8 : F) * L * r ^ 2 * B +
    (15 / 8 : F) * L * r * q ^ 2 + (3 / 2 : F) * r * q * B +
    (3 / 2 : F) * beta * r * q - (5 / 16 : F) * L * r * U +
    delta * r + q ^ 3 + (5 / 8 : F) * L * q * B -
    (3 / 8 : F) * q * U + gamma * q + (3 / 8 : F) * B ^ 2 +
    (3 / 4 : F) * beta * B

/-- Evaluating the depressed quartic at the translated origin gives the
first reviewed boundary equation. -/
theorem eval_depressedQuartic46_discriminant_eq_boundaryD46
    (r A B U : F) :
    (depressedQuartic46 A B (discriminantC46 A U)).eval r =
      boundaryD46 r (translatedQ46 r A) B U := by
  simp [depressedQuartic46, discriminantC46, translatedQ46, boundaryD46]
  ring

/-- Evaluating the integrated depressed sextic at the translated origin,
and subtracting `alpha` times the quartic plus `epsilon`, gives exactly the
second reviewed boundary equation. -/
theorem eval_integratedSextic46_discriminant_eq_boundaryE46
    (L r A B U alpha beta gamma delta epsilon : F) :
    let C0 := discriminantC46 A U
    let P := integratedP46 A alpha
    let Q := integratedQ46 L A B beta
    let R := integratedR46 L A B C0 alpha gamma
    let S := integratedS46 L A B C0 alpha beta delta
    let T := integratedT46 L A B C0 alpha beta gamma epsilon
    let q := translatedQ46 r A
    (depressedSextic46 L P Q R S T).eval r -
          alpha * (depressedQuartic46 A B C0).eval r - epsilon =
      boundaryE46 L r q B U beta gamma delta := by
  dsimp only
  simp only [depressedSextic46, depressedQuartic46, integratedP46,
    integratedQ46, integratedR46, integratedS46, integratedT46,
    discriminantC46, translatedQ46, boundaryE46, eval_add, eval_pow,
    eval_mul, eval_X, eval_C]
  ring

end BoundaryCover

section WeightedInfinity

/-- Weight-four leading boundary form at infinity. -/
def weightedInfinityF46 (r q B U : F) : F :=
  r * B + q ^ 2 - (1 / 4 : F) * U

/-- Weight-six leading boundary form at infinity. -/
def weightedInfinityG46 (r q B U : F) : F :=
  q ^ 3 + (3 / 2 : F) * r * q * B - (3 / 8 : F) * q * U +
    (3 / 8 : F) * B ^ 2

/-- Weight-seven leading `J₂` form at infinity. -/
def weightedInfinityJTwo46 (B U : F) : F :=
  (-3 / 4 : F) * B * U

/-- Weight-eight leading `J₁` form at infinity. -/
def weightedInfinityJOne46 (r q B U : F) : F :=
  (3 / 2 : F) * r ^ 2 * B ^ 2 - (3 / 2 : F) * q * B ^ 2 +
    (3 / 32 : F) * U ^ 2

/-- The four highest weighted forms have no common zero except the affine
line `(r,0,0,0)`.  Consequently their unique weighted-projective common
zero is `[1:0:0:0]`. -/
theorem weightedInfinity_commonZeros46 (r q B U : F)
    (hF : weightedInfinityF46 r q B U = 0)
    (hG : weightedInfinityG46 r q B U = 0)
    (hJ2 : weightedInfinityJTwo46 B U = 0)
    (hJ1 : weightedInfinityJOne46 r q B U = 0) :
    B = 0 ∧ U = 0 ∧ q = 0 := by
  have hBU : B * U = 0 := by
    rw [weightedInfinityJTwo46] at hJ2
    have hc : (-3 / 4 : F) ≠ 0 := by norm_num
    apply mul_left_cancel₀ hc
    simpa [mul_assoc] using hJ2
  rcases mul_eq_zero.mp hBU with hB | hU
  · subst B
    have hU2 : U ^ 2 = 0 := by
      rw [weightedInfinityJOne46] at hJ1
      norm_num at hJ1 ⊢
      exact hJ1
    have hU0 : U = 0 := by
      by_contra hU
      exact pow_ne_zero 2 hU hU2
    subst U
    have hq2 : q ^ 2 = 0 := by
      rw [weightedInfinityF46] at hF
      simpa using hF
    have hq0 : q = 0 := by
      by_contra hq
      exact pow_ne_zero 2 hq hq2
    exact ⟨rfl, rfl, hq0⟩
  · subst U
    by_cases hB : B = 0
    · subst B
      have hq2 : q ^ 2 = 0 := by
        rw [weightedInfinityF46] at hF
        simpa using hF
      have hq0 : q = 0 := by
        by_contra hq
        exact pow_ne_zero 2 hq hq2
      exact ⟨rfl, rfl, hq0⟩
    · have hrq : r ^ 2 = q := by
        rw [weightedInfinityJOne46] at hJ1
        have hB2 : B ^ 2 ≠ 0 := pow_ne_zero 2 hB
        have hc : (3 / 2 : F) ≠ 0 := by norm_num
        apply (mul_left_cancel₀ hB2)
        apply (mul_left_cancel₀ hc)
        linear_combination hJ1
      by_cases hr : r = 0
      · subst r
        have hq : q = 0 := by simpa using hrq.symm
        subst q
        rw [weightedInfinityG46] at hG
        have hB2 : B ^ 2 = 0 := by
          norm_num at hG ⊢
          exact hG
        exact (pow_ne_zero 2 hB hB2).elim
      · have hBform : B = -r ^ 3 := by
          rw [weightedInfinityF46, ← hrq] at hF
          apply (mul_left_cancel₀ hr)
          linear_combination hF
        rw [weightedInfinityG46, ← hrq, hBform] at hG
        have hr6 : r ^ 6 = 0 := by
          ring_nf at hG
          have hc : (-1 / 8 : F) ≠ 0 := by norm_num
          exact (mul_eq_zero.mp hG).resolve_right hc
        exact (pow_ne_zero 6 hr hr6).elim

end WeightedInfinity

end CoefficientCurve

end Max11DegreeRoutes
