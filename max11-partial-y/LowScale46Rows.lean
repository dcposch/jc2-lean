import LowScaleCore

/-! # The first genuine `(4,6)` Jacobian discriminator

After the leading coefficients of a partial-degree `(4,6)` Keller pair have
been normalized to `H ^ 2` and `H ^ 3`, its next Jacobian row is governed by

`N = 3 * a₃ * H - 2 * b₅`.

This module derives that row directly from the bivariate Jacobian and proves
the polynomial first integral `N ^ 2 = C κ * H ^ 5`.  In particular, the
argument does not divide by `H` or assume the later depressed normal form.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-- The first row below the leading weighted-Wronskian row for outer degrees
`(4,6)`. -/
theorem nextCoefficientJacobianRow_46 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 6)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 4).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 3).derivative * (q.coeff 6 * Polynomial.C (6 : K)) -
      ((p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 5).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 6).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 8) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (8 : ℕ) ≠ 0 by norm_num, if_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 8 : Finset (ℕ × ℕ)) =
      ({(0, 8), (1, 7), (2, 6), (3, 5), (4, 4), (5, 3), (6, 2),
        (7, 1), (8, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) :=
    Polynomial.C_eq_natCast 6
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  rw [hC5, hC6, hC4, hC3]
  linear_combination hcoeff

/-- The normalized `(4,6)` next row is exactly the weighted derivative of
the imprimitive discriminator `N = 3 a₃ H - 2 b₅`. -/
theorem imprimitiveDiscriminatorRow_eq_zero_46 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]}
    (hp : p.natDegree = 4) (hq : q.natDegree = 6)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp4 : p.coeff 4 = H ^ 2) (hq6 : q.coeff 6 = H ^ 3) :
    let N := (3 : K[X]) * p.coeff 3 * H - (2 : K[X]) * q.coeff 5
    (2 : K[X]) * H * N.derivative -
        (5 : K[X]) * N * H.derivative = 0 := by
  dsimp only
  have hrow := nextCoefficientJacobianRow_46 hp hq hjac
  rw [hp4, hq6] at hrow
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) :=
    Polynomial.C_eq_natCast 6
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  rw [hC5, hC6, hC4, hC3] at hrow
  have hscaled : H *
      ((2 : K[X]) * H *
          ((3 : K[X]) * p.coeff 3 * H -
            (2 : K[X]) * q.coeff 5).derivative -
        (5 : K[X]) *
          ((3 : K[X]) * p.coeff 3 * H -
            (2 : K[X]) * q.coeff 5) * H.derivative) = 0 := by
    calc
      H *
          ((2 : K[X]) * H *
              ((3 : K[X]) * p.coeff 3 * H -
                (2 : K[X]) * q.coeff 5).derivative -
            (5 : K[X]) *
              ((3 : K[X]) * p.coeff 3 * H -
                (2 : K[X]) * q.coeff 5) * H.derivative) =
          (H ^ 2).derivative * (q.coeff 5 * (5 : K[X])) +
              (p.coeff 3).derivative * (H ^ 3 * (6 : K[X])) -
            ((H ^ 2 * (4 : K[X])) * (q.coeff 5).derivative +
              (p.coeff 3 * (3 : K[X])) * (H ^ 3).derivative) := by
                simp only [Polynomial.derivative_sub,
                  Polynomial.derivative_mul, Polynomial.derivative_pow,
                  Polynomial.derivative_natCast, Polynomial.derivative_ofNat,
                  Polynomial.C_eq_natCast, zero_mul, zero_add]
                ring
      _ = 0 := hrow
  exact (mul_eq_zero.mp hscaled).resolve_left hH

/-- Polynomial form of the first integral for the normalized `(4,6)`
discriminator.  This is the exact split `N² = κ H⁵`; it is obtained from a
Wronskian and therefore needs no rational-function quotient. -/
theorem imprimitiveDiscriminatorPowerRelation_46 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]}
    (hp : p.natDegree = 4) (hq : q.natDegree = 6)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp4 : p.coeff 4 = H ^ 2) (hq6 : q.coeff 6 = H ^ 3) :
    let N := (3 : K[X]) * p.coeff 3 * H - (2 : K[X]) * q.coeff 5
    ∃ κ : K, N ^ 2 = Polynomial.C κ * H ^ 5 := by
  dsimp only
  let N : K[X] :=
    (3 : K[X]) * p.coeff 3 * H - (2 : K[X]) * q.coeff 5
  have hrow :
      (2 : K[X]) * H * N.derivative -
          (5 : K[X]) * N * H.derivative = 0 := by
    simpa only [N] using
      imprimitiveDiscriminatorRow_eq_zero_46 hp hq hjac hH hp4 hq6
  have hrowC :
      Polynomial.C (2 : K) * H * N.derivative -
          Polynomial.C (5 : K) * N * H.derivative = 0 := by
    have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
      Polynomial.C_eq_natCast 2
    have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
      Polynomial.C_eq_natCast 5
    rw [hC2, hC5]
    exact hrow
  have hW : Polynomial.wronskian (N ^ 2) (H ^ 5) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      N ^ 2 * (Polynomial.C (5 : K) * H ^ (5 - 1) * H.derivative) -
          (Polynomial.C (2 : K) * N ^ (2 - 1) * N.derivative) * H ^ 5 =
          N * H ^ 4 *
            (Polynomial.C (5 : K) * N * H.derivative -
              Polynomial.C (2 : K) * H * N.derivative) := by
                ring
      _ = 0 := by rw [sub_eq_zero.mpr (sub_eq_zero.mp hrowC).symm, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 5 hH) hW

/-- On the nonzero branch of `N² = κ H⁵`, algebraic closure absorbs the
remaining scalar and exposes the square/fifth-power normalization used by
the mismatch analysis. -/
theorem squareCore_of_nonzero_imprimitiveRelation_46 {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K] {H N : K[X]} {κ : K}
    (hH : H ≠ 0) (hκ : κ ≠ 0)
    (hrelation : N ^ 2 = Polynomial.C κ * H ^ 5) :
    ∃ (h : K[X]) (lambda : K),
      h ≠ 0 ∧ lambda ≠ 0 ∧ H = h ^ 2 ∧
        N = Polynomial.C lambda * h ^ 5 ∧ lambda ^ 2 = κ := by
  have hN : N ≠ 0 := by
    intro hzero
    have hright : Polynomial.C κ * H ^ 5 ≠ 0 :=
      mul_ne_zero (Polynomial.C_ne_zero.mpr hκ) (pow_ne_zero 5 hH)
    apply hright
    simpa [hzero] using hrelation.symm
  have hinverse : H ^ 5 = Polynomial.C κ⁻¹ * N ^ 2 := by
    calc
      H ^ 5 = (Polynomial.C κ⁻¹ * Polynomial.C κ) * H ^ 5 := by
        rw [← Polynomial.C_mul, inv_mul_cancel₀ hκ, Polynomial.C_1, one_mul]
      _ = Polynomial.C κ⁻¹ * (Polynomial.C κ * H ^ 5) := by ring
      _ = Polynomial.C κ⁻¹ * N ^ 2 := by rw [← hrelation]
  obtain ⟨alpha, beta, h₀, halpha, hbeta, hh₀, hHform, hNform⟩ :=
    commonCore_of_powerRelation_25 hH hN κ⁻¹ (inv_ne_zero hκ) hinverse
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq alpha (by norm_num : 0 < 2)
  have ht0 : t ≠ 0 := by
    intro htzero
    apply halpha
    rw [← ht, htzero, zero_pow (by norm_num : 2 ≠ 0)]
  let h : K[X] := Polynomial.C t * h₀
  let lambda : K := beta * (t ^ 5)⁻¹
  have hh : h ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr ht0) hh₀
  have hlambda : lambda ≠ 0 :=
    mul_ne_zero hbeta (inv_ne_zero (pow_ne_zero 5 ht0))
  have hHsquare : H = h ^ 2 := by
    rw [hHform]
    dsimp only [h]
    rw [mul_pow, ← Polynomial.C_pow, ht]
  have hNfifth : N = Polynomial.C lambda * h ^ 5 := by
    have hcancel : lambda * t ^ 5 = beta := by
      dsimp only [lambda]
      field_simp
    calc
      N = Polynomial.C beta * h₀ ^ 5 := hNform
      _ = Polynomial.C (lambda * t ^ 5) * h₀ ^ 5 := by rw [hcancel]
      _ = (Polynomial.C lambda * Polynomial.C (t ^ 5)) * h₀ ^ 5 := by
        rw [Polynomial.C_mul]
      _ = Polynomial.C lambda * (Polynomial.C t * h₀) ^ 5 := by
        rw [mul_pow, ← Polynomial.C_pow]
        ring
      _ = Polynomial.C lambda * h ^ 5 := by rfl
  have hcoeff :
      Polynomial.C (lambda ^ 2) * h ^ 10 =
        Polynomial.C κ * h ^ 10 := by
    calc
      Polynomial.C (lambda ^ 2) * h ^ 10 =
          (Polynomial.C lambda * h ^ 5) ^ 2 := by
            simp only [mul_pow, map_pow]
            ring
      _ = N ^ 2 := by rw [← hNfifth]
      _ = Polynomial.C κ * H ^ 5 := hrelation
      _ = Polynomial.C κ * h ^ 10 := by rw [hHsquare]; ring
  have hCeq : Polynomial.C (lambda ^ 2) = Polynomial.C κ := by
    exact mul_right_cancel₀ (pow_ne_zero 10 hh) hcoeff
  refine ⟨h, lambda, hh, hlambda, hHsquare, hNfifth, ?_⟩
  exact Polynomial.C_injective hCeq

/-- Source-facing form: a genuine normalized `(4,6)` Keller pair supplies
the exact imprimitive discriminator split. -/
theorem planeKellerPair_46_imprimitiveDiscriminatorPowerRelation {K : Type*}
    [Field K] [CharZero K] {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hP : degreeOf 1 P = 4) (hQ : degreeOf 1 Q = 6)
    (hKeller : IsPlaneKellerPair P Q) (hH : H ≠ 0)
    (hp4 : ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 4 = H ^ 2)
    (hq6 : ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff 6 = H ^ 3) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    let N := (3 : K[X]) * p.coeff 3 * H - (2 : K[X]) * q.coeff 5
    ∃ κ : K, N ^ 2 = Polynomial.C κ * H ^ 5 := by
  dsimp only
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hpdegree : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hP
  have hqdegree : q.natDegree = 6 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQ
  obtain ⟨j, -, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  exact imprimitiveDiscriminatorPowerRelation_46
    hpdegree hqdegree hjac hH hp4 hq6

/-- The reviewed first split of a genuine normalized `(4,6)` source.  The
aligned branch has `N = 0`; every nonaligned branch has `H = h²` and
`N = λh⁵` for a nonzero constant `λ`. -/
theorem planeKellerPair_46_imprimitiveDiscriminatorDichotomy {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hP : degreeOf 1 P = 4) (hQ : degreeOf 1 Q = 6)
    (hKeller : IsPlaneKellerPair P Q) (hH : H ≠ 0)
    (hp4 : ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 4 = H ^ 2)
    (hq6 : ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff 6 = H ^ 3) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    let N := (3 : K[X]) * p.coeff 3 * H - (2 : K[X]) * q.coeff 5
    N = 0 ∨
      ∃ (h : K[X]) (lambda : K),
        h ≠ 0 ∧ lambda ≠ 0 ∧ H = h ^ 2 ∧
          N = Polynomial.C lambda * h ^ 5 := by
  dsimp only
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  let N : K[X] :=
    (3 : K[X]) * p.coeff 3 * H - (2 : K[X]) * q.coeff 5
  obtain ⟨κ, hrelation⟩ :=
    planeKellerPair_46_imprimitiveDiscriminatorPowerRelation
      hP hQ hKeller hH hp4 hq6
  by_cases hκ : κ = 0
  · left
    have hNsquare : N ^ 2 = 0 := by
      simpa only [hκ, Polynomial.C_0, zero_mul] using hrelation
    exact sq_eq_zero_iff.mp hNsquare
  · right
    obtain ⟨h, lambda, hh, hlambda, hHsquare, hNfifth, -⟩ :=
      squareCore_of_nonzero_imprimitiveRelation_46 hH hκ hrelation
    exact ⟨h, lambda, hh, hlambda, hHsquare, hNfifth⟩

end Max11DegreeRoutes
