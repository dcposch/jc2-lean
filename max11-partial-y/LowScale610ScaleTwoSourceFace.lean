import LowScale410ScaleTwoSourceFace

/-! # Scale-two source reduction for the normalized `(6,10)`, `H = 2` leaf

The first row below the leading weighted-Wronskian row has the source
discriminator

`N = 5 * p₅ * H² - 3 * q₉`.

This file proves directly from the literal Keller bracket that
`N² = C κ * H⁹`.  Thus the normalized scale-two source has an exact first
face: either it is aligned (`N = 0`), or it lies on the nonzero ninth-power
face.  At scale two the nonzero face carries a linear root.  No total-degree
or twice-prime theorem is used, and neither face is excluded.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-- The first row below the leading weighted-Wronskian row for outer degrees
`(6,10)`.  It is the literal source of the nonic depression discriminator. -/
theorem nextCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 6).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 5).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 9).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 10).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 14) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (14 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 14 :
      Finset (ℕ × ℕ)) =
      ({(0, 14), (1, 13), (2, 12), (3, 11), (4, 10), (5, 9), (6, 8),
        (7, 7), (8, 6), (9, 5), (10, 4), (11, 3), (12, 2), (13, 1),
        (14, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) :=
    Polynomial.C_eq_natCast 9
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) :=
    Polynomial.C_eq_natCast 10
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) :=
    Polynomial.C_eq_natCast 6
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  rw [hC9, hC10, hC6, hC5]
  linear_combination hcoeff

/-- With leading coefficients `H³,H⁵`, the next row is precisely the
weighted derivative of `N = 5 p₅ H² - 3 q₉`. -/
theorem imprimitiveDiscriminatorRow_eq_zero_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5) :
    let N := (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9
    (2 : K[X]) * H * N.derivative -
        (9 : K[X]) * N * H.derivative = 0 := by
  dsimp only
  have hrow := nextCoefficientJacobianRow_610 hp hq hjac
  rw [hp6, hq10] at hrow
  have hscaled : H ^ 2 *
      ((2 : K[X]) * H *
          ((5 : K[X]) * p.coeff 5 * H ^ 2 -
            (3 : K[X]) * q.coeff 9).derivative -
        (9 : K[X]) *
          ((5 : K[X]) * p.coeff 5 * H ^ 2 -
            (3 : K[X]) * q.coeff 9) * H.derivative) = 0 := by
    calc
      H ^ 2 *
          ((2 : K[X]) * H *
              ((5 : K[X]) * p.coeff 5 * H ^ 2 -
                (3 : K[X]) * q.coeff 9).derivative -
            (9 : K[X]) *
              ((5 : K[X]) * p.coeff 5 * H ^ 2 -
                (3 : K[X]) * q.coeff 9) * H.derivative) =
          (H ^ 3).derivative * (q.coeff 9 * (9 : K[X])) +
              (p.coeff 5).derivative * (H ^ 5 * (10 : K[X])) -
            ((H ^ 3 * (6 : K[X])) * (q.coeff 9).derivative +
              (p.coeff 5 * (5 : K[X])) * (H ^ 5).derivative) := by
                simp only [Polynomial.derivative_sub,
                  Polynomial.derivative_mul, Polynomial.derivative_pow,
                  Polynomial.derivative_ofNat,
                  Polynomial.C_eq_natCast, zero_mul, zero_add]
                ring
      _ = 0 := hrow
  exact (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero 2 hH)

/-- Polynomial first integral of the `(6,10)` source discriminator. -/
theorem imprimitiveDiscriminatorPowerRelation_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5) :
    let N := (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9
    ∃ κ : K, N ^ 2 = Polynomial.C κ * H ^ 9 := by
  dsimp only
  let N : K[X] :=
    (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9
  have hrow :
      (2 : K[X]) * H * N.derivative -
          (9 : K[X]) * N * H.derivative = 0 := by
    simpa only [N] using
      imprimitiveDiscriminatorRow_eq_zero_610 hp hq hjac hH hp6 hq10
  have hrowC :
      Polynomial.C (2 : K) * H * N.derivative -
          Polynomial.C (9 : K) * N * H.derivative = 0 := by
    have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
      Polynomial.C_eq_natCast 2
    have hC9 : Polynomial.C (9 : K) = (9 : K[X]) :=
      Polynomial.C_eq_natCast 9
    rw [hC2, hC9]
    exact hrow
  have hW : Polynomial.wronskian (N ^ 2) (H ^ 9) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      N ^ 2 * (Polynomial.C (9 : K) * H ^ (9 - 1) * H.derivative) -
          (Polynomial.C (2 : K) * N ^ (2 - 1) * N.derivative) * H ^ 9 =
          N * H ^ 8 *
            (Polynomial.C (9 : K) * N * H.derivative -
              Polynomial.C (2 : K) * H * N.derivative) := by ring
      _ = 0 := by
        rw [sub_eq_zero.mpr (sub_eq_zero.mp hrowC).symm, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 9 hH) hW

/-- On the nonzero first face, algebraic closure absorbs the scalar in the
quadratic core and yields the literal square/ninth-power source shape.
The coprime `(2,9)` extraction is the same UFD packet already proved for
the `(4,10)` source face. -/
theorem squareCore_of_nonzero_imprimitiveRelation_610
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {H N : K[X]} {κ : K}
    (hH : H ≠ 0) (hκ : κ ≠ 0)
    (hrelation : N ^ 2 = Polynomial.C κ * H ^ 9) :
    ∃ (h : K[X]) (lambda : K),
      h ≠ 0 ∧ lambda ≠ 0 ∧ H = h ^ 2 ∧
        N = Polynomial.C lambda * h ^ 9 ∧ lambda ^ 2 = κ :=
  squareCore_of_nonzero_imprimitiveRelation_410 hH hκ hrelation

/-- Source-facing first integral for a normalized scale-two `(6,10)` pair. -/
theorem normalized610ScaleTwo_discriminatorPowerRelation
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    let N := (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9
    ∃ κ : K, N ^ 2 = Polynomial.C κ * H ^ 9 := by
  dsimp only
  rcases hsource with
    ⟨hH, _hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  exact imprimitiveDiscriminatorPowerRelation_610
    hp hq hjac hH (by simpa only [p] using hp6)
      (by simpa only [q] using hq10)

/-- The exact first-face dichotomy for every normalized scale-two `(6,10)`
source: the discriminator vanishes, or its square is a nonzero scalar times
the ninth power of the quadratic common core. -/
theorem normalized610ScaleTwo_discriminatorFirstFace
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    let N := (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9
    N = 0 ∨ ∃ κ : K, κ ≠ 0 ∧ N ^ 2 = Polynomial.C κ * H ^ 9 := by
  dsimp only
  obtain ⟨κ, hrelation⟩ :=
    normalized610ScaleTwo_discriminatorPowerRelation hsource
  by_cases hκ : κ = 0
  · left
    have hNsquare :
        ((5 : K[X]) *
            ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 5 *
              H ^ 2 -
          (3 : K[X]) *
            ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff 9) ^ 2 =
          0 := by
      simpa only [hκ, Polynomial.C_0, zero_mul] using hrelation
    exact sq_eq_zero_iff.mp hNsquare
  · exact Or.inr ⟨κ, hκ, hrelation⟩

/-- Over an algebraically closed ground field the nonzero first face has the
literal square/ninth-power form required by a source-pole analysis. -/
theorem normalized610ScaleTwo_imprimitiveDiscriminatorDichotomy
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    let N := (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9
    N = 0 ∨
      ∃ (h : K[X]) (lambda : K),
        h ≠ 0 ∧ lambda ≠ 0 ∧ H = h ^ 2 ∧
          N = Polynomial.C lambda * h ^ 9 := by
  dsimp only
  rcases normalized610ScaleTwo_discriminatorFirstFace hsource with
    hzero | ⟨κ, hκ, hrelation⟩
  · exact Or.inl hzero
  · right
    obtain ⟨h, lambda, hh, hlambda, hH, hN, _hlambdaSq⟩ :=
      squareCore_of_nonzero_imprimitiveRelation_610
        hsource.1 hκ hrelation
    exact ⟨h, lambda, hh, hlambda, hH, hN⟩

/-- The nonaligned scale-two face carries a degree-one square root of the
common core and hence a concrete finite root.  This is the exact entry point
for a later weighted-infinity/local-pole analysis. -/
theorem normalized610ScaleTwo_nonzeroFace_has_linear_root
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    let N := (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9
    ∃ (h : K[X]) (lambda a : K),
      h ≠ 0 ∧ lambda ≠ 0 ∧ h.natDegree = 1 ∧
        H = h ^ 2 ∧ h.eval a = 0 ∧
          N = Polynomial.C lambda * h ^ 9 := by
  dsimp only at hnonzero ⊢
  rcases normalized610ScaleTwo_imprimitiveDiscriminatorDichotomy
      hsource with hzero | ⟨h, lambda, hh, hlambda, hH, hN⟩
  · exact (hnonzero hzero).elim
  · have hhdegree : h.natDegree = 1 := by
      have hdegree := congrArg Polynomial.natDegree hH
      rw [hsource.2.1, Polynomial.natDegree_pow] at hdegree
      omega
    obtain ⟨c, hc, d, hlinear⟩ :=
      Polynomial.natDegree_eq_one.mp hhdegree
    let a : K := -d / c
    have hroot : h.eval a = 0 := by
      rw [← hlinear]
      simp only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
      dsimp only [a]
      field_simp [hc]
      ring
    exact ⟨h, lambda, a, hh, hlambda, hhdegree, hH, hroot, hN⟩

#print axioms imprimitiveDiscriminatorPowerRelation_610
#print axioms squareCore_of_nonzero_imprimitiveRelation_610
#print axioms normalized610ScaleTwo_discriminatorFirstFace
#print axioms normalized610ScaleTwo_imprimitiveDiscriminatorDichotomy
#print axioms normalized610ScaleTwo_nonzeroFace_has_linear_root

end Max11DegreeRoutes
