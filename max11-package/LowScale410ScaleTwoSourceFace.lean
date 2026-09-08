import LowScale68ScaleTwoSourceFace

/-! # Scale-two source reduction for the normalized `(4,10)`, `H = 2` leaf

The first row below the leading weighted-Wronskian row has the source
discriminator

`N = 5 * p₃ * H³ - 2 * q₉`.

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
`(4,10)`.  It is the literal source of the nonic depression discriminator. -/
theorem nextCoefficientJacobianRow_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 4).derivative * (q.coeff 9 * Polynomial.C (9 : K)) +
        (p.coeff 3).derivative * (q.coeff 10 * Polynomial.C (10 : K)) -
      ((p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 9).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 10).derivative) = 0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 12) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (12 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 12 :
      Finset (ℕ × ℕ)) =
      ({(0, 12), (1, 11), (2, 10), (3, 9), (4, 8), (5, 7), (6, 6),
        (7, 5), (8, 4), (9, 3), (10, 2), (11, 1), (12, 0)} :
        Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC9 : Polynomial.C (9 : K) = (9 : K[X]) :=
    Polynomial.C_eq_natCast 9
  have hC10 : Polynomial.C (10 : K) = (10 : K[X]) :=
    Polynomial.C_eq_natCast 10
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  rw [hC9, hC10, hC4, hC3]
  linear_combination hcoeff

/-- With leading coefficients `H²,H⁵`, the next row is precisely the
weighted derivative of `N = 5 p₃ H³ - 2 q₉`. -/
theorem imprimitiveDiscriminatorRow_eq_zero_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5) :
    let N := (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9
    (2 : K[X]) * H * N.derivative -
        (9 : K[X]) * N * H.derivative = 0 := by
  dsimp only
  have hrow := nextCoefficientJacobianRow_410 hp hq hjac
  rw [hp4, hq10] at hrow
  have hscaled : H *
      ((2 : K[X]) * H *
          ((5 : K[X]) * p.coeff 3 * H ^ 3 -
            (2 : K[X]) * q.coeff 9).derivative -
        (9 : K[X]) *
          ((5 : K[X]) * p.coeff 3 * H ^ 3 -
            (2 : K[X]) * q.coeff 9) * H.derivative) = 0 := by
    calc
      H *
          ((2 : K[X]) * H *
              ((5 : K[X]) * p.coeff 3 * H ^ 3 -
                (2 : K[X]) * q.coeff 9).derivative -
            (9 : K[X]) *
              ((5 : K[X]) * p.coeff 3 * H ^ 3 -
                (2 : K[X]) * q.coeff 9) * H.derivative) =
          (H ^ 2).derivative * (q.coeff 9 * (9 : K[X])) +
              (p.coeff 3).derivative * (H ^ 5 * (10 : K[X])) -
            ((H ^ 2 * (4 : K[X])) * (q.coeff 9).derivative +
              (p.coeff 3 * (3 : K[X])) * (H ^ 5).derivative) := by
                simp only [Polynomial.derivative_sub,
                  Polynomial.derivative_mul, Polynomial.derivative_pow,
                  Polynomial.derivative_ofNat,
                  Polynomial.C_eq_natCast, zero_mul, zero_add]
                ring
      _ = 0 := hrow
  exact (mul_eq_zero.mp hscaled).resolve_left hH

/-- Polynomial first integral of the `(4,10)` source discriminator. -/
theorem imprimitiveDiscriminatorPowerRelation_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5) :
    let N := (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9
    ∃ κ : K, N ^ 2 = Polynomial.C κ * H ^ 9 := by
  dsimp only
  let N : K[X] :=
    (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9
  have hrow :
      (2 : K[X]) * H * N.derivative -
          (9 : K[X]) * N * H.derivative = 0 := by
    simpa only [N] using
      imprimitiveDiscriminatorRow_eq_zero_410 hp hq hjac hH hp4 hq10
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

/-- UFD extraction tailored to the coprime powers `(2,9)`.  Removing the
gcd leaves a seventh/square relation, so the existing `(2,7)` extraction
finishes the proof. -/
theorem commonCore_of_powerRelation_29 {K : Type*}
    [Field K] [CharZero K] {A B : K[X]} (_hA : A ≠ 0) (hB : B ≠ 0)
    (c : K) (hc : c ≠ 0)
    (hpowers : A ^ 9 = Polynomial.C c * B ^ 2) :
    ∃ (alpha beta : K) (h : K[X]),
      alpha ≠ 0 ∧ beta ≠ 0 ∧ h ≠ 0 ∧
        A = Polynomial.C alpha * h ^ 2 ∧
        B = Polynomial.C beta * h ^ 9 := by
  classical
  let := EuclideanDomain.gcdMonoid K[X]
  let d := gcd A B
  let A' := A / d
  let B' := B / d
  have hd : d ≠ 0 := gcd_ne_zero_of_right hB
  have hdA : d * A' = A :=
    EuclideanDomain.mul_div_cancel' hd (gcd_dvd_left A B)
  have hdB : d * B' = B :=
    EuclideanDomain.mul_div_cancel' hd (gcd_dvd_right A B)
  have hB' : B' ≠ 0 := by
    intro hzero
    apply hB
    rw [← hdB, hzero, mul_zero]
  have hcop : IsCoprime A' B' := isCoprime_div_gcd_div_gcd hB
  have hreduced : d ^ 7 * A' ^ 9 = Polynomial.C c * B' ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hd)
    calc
      d ^ 2 * (d ^ 7 * A' ^ 9) = (d * A') ^ 9 := by ring
      _ = A ^ 9 := by rw [hdA]
      _ = Polynomial.C c * B ^ 2 := hpowers
      _ = Polynomial.C c * (d * B') ^ 2 := by rw [hdB]
      _ = d ^ 2 * (Polynomial.C c * B' ^ 2) := by ring
  have hCunit : IsUnit (Polynomial.C c) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
  have hA'dvd : A' ∣ Polynomial.C c * B' ^ 2 := by
    refine ⟨d ^ 7 * A' ^ 8, ?_⟩
    rw [← hreduced]
    ring
  have hA'unit : IsUnit A' := by
    apply isUnit_of_dvd_unit
      (hcop.pow_right.dvd_of_dvd_mul_right hA'dvd) hCunit
  have hdpowassoc : Associated (d ^ 7) (B' ^ 2) :=
    (associated_mul_unit_left (d ^ 7) (A' ^ 9) (hA'unit.pow 9)).symm |>.trans
      (Associated.of_eq hreduced) |>.trans
        (associated_unit_mul_left (B' ^ 2) (Polynomial.C c) hCunit)
  obtain ⟨u, hu⟩ := hdpowassoc.symm
  obtain ⟨gamma, hgammaUnit, hgamma⟩ :=
    Polynomial.isUnit_iff.mp u.isUnit
  have hdpower : d ^ 7 = Polynomial.C gamma * B' ^ 2 := by
    calc
      d ^ 7 = B' ^ 2 * (u : K[X]) := hu.symm
      _ = Polynomial.C gamma * B' ^ 2 := by rw [← hgamma]; ring
  obtain ⟨delta, epsilon, h, hdelta, hepsilon, hh, hdcore, hB'core⟩ :=
    commonCore_of_powerRelation_27 hd hB' gamma
      (isUnit_iff_ne_zero.mp hgammaUnit) hdpower
  obtain ⟨a0, ha0unit, ha0⟩ := Polynomial.isUnit_iff.mp hA'unit
  refine ⟨delta * a0, delta * epsilon, h,
    mul_ne_zero hdelta (isUnit_iff_ne_zero.mp ha0unit),
    mul_ne_zero hdelta hepsilon, hh, ?_, ?_⟩
  · calc
      A = d * A' := hdA.symm
      _ = (Polynomial.C delta * h ^ 2) * Polynomial.C a0 := by
        rw [hdcore, ha0]
      _ = Polynomial.C (delta * a0) * h ^ 2 := by
        rw [Polynomial.C_mul]
        ring
  · calc
      B = d * B' := hdB.symm
      _ = (Polynomial.C delta * h ^ 2) *
          (Polynomial.C epsilon * h ^ 7) := by rw [hdcore, hB'core]
      _ = Polynomial.C (delta * epsilon) * h ^ 9 := by
        rw [Polynomial.C_mul]
        ring

/-- On the nonzero first face, algebraic closure absorbs the scalar in the
quadratic core and yields the literal square/ninth-power source shape. -/
theorem squareCore_of_nonzero_imprimitiveRelation_410
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {H N : K[X]} {κ : K}
    (hH : H ≠ 0) (hκ : κ ≠ 0)
    (hrelation : N ^ 2 = Polynomial.C κ * H ^ 9) :
    ∃ (h : K[X]) (lambda : K),
      h ≠ 0 ∧ lambda ≠ 0 ∧ H = h ^ 2 ∧
        N = Polynomial.C lambda * h ^ 9 ∧ lambda ^ 2 = κ := by
  have hN : N ≠ 0 := by
    intro hzero
    have hright : Polynomial.C κ * H ^ 9 ≠ 0 :=
      mul_ne_zero (Polynomial.C_ne_zero.mpr hκ) (pow_ne_zero 9 hH)
    apply hright
    simpa [hzero] using hrelation.symm
  have hinverse : H ^ 9 = Polynomial.C κ⁻¹ * N ^ 2 := by
    calc
      H ^ 9 = (Polynomial.C κ⁻¹ * Polynomial.C κ) * H ^ 9 := by
        rw [← Polynomial.C_mul, inv_mul_cancel₀ hκ,
          Polynomial.C_1, one_mul]
      _ = Polynomial.C κ⁻¹ * (Polynomial.C κ * H ^ 9) := by ring
      _ = Polynomial.C κ⁻¹ * N ^ 2 := by rw [← hrelation]
  obtain ⟨alpha, beta, h₀, halpha, hbeta, hh₀, hHform, hNform⟩ :=
    commonCore_of_powerRelation_29 hH hN κ⁻¹
      (inv_ne_zero hκ) hinverse
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq alpha
    (by norm_num : 0 < 2)
  have ht0 : t ≠ 0 := by
    intro htzero
    apply halpha
    rw [← ht, htzero, zero_pow (by norm_num : 2 ≠ 0)]
  let h : K[X] := Polynomial.C t * h₀
  let lambda : K := beta * (t ^ 9)⁻¹
  have hh : h ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr ht0) hh₀
  have hlambda : lambda ≠ 0 :=
    mul_ne_zero hbeta (inv_ne_zero (pow_ne_zero 9 ht0))
  have hHsquare : H = h ^ 2 := by
    rw [hHform]
    dsimp only [h]
    rw [mul_pow, ← Polynomial.C_pow, ht]
  have hNninth : N = Polynomial.C lambda * h ^ 9 := by
    have hcancel : lambda * t ^ 9 = beta := by
      dsimp only [lambda]
      field_simp
    calc
      N = Polynomial.C beta * h₀ ^ 9 := hNform
      _ = Polynomial.C (lambda * t ^ 9) * h₀ ^ 9 := by rw [hcancel]
      _ = (Polynomial.C lambda * Polynomial.C (t ^ 9)) * h₀ ^ 9 := by
        rw [Polynomial.C_mul]
      _ = Polynomial.C lambda * (Polynomial.C t * h₀) ^ 9 := by
        rw [mul_pow, ← Polynomial.C_pow]
        ring
      _ = Polynomial.C lambda * h ^ 9 := by rfl
  have hcoeff :
      Polynomial.C (lambda ^ 2) * h ^ 18 =
        Polynomial.C κ * h ^ 18 := by
    calc
      Polynomial.C (lambda ^ 2) * h ^ 18 =
          (Polynomial.C lambda * h ^ 9) ^ 2 := by
            simp only [mul_pow, map_pow]
            ring
      _ = N ^ 2 := by rw [← hNninth]
      _ = Polynomial.C κ * H ^ 9 := hrelation
      _ = Polynomial.C κ * h ^ 18 := by rw [hHsquare]; ring
  have hCeq : Polynomial.C (lambda ^ 2) = Polynomial.C κ :=
    mul_right_cancel₀ (pow_ne_zero 18 hh) hcoeff
  refine ⟨h, lambda, hh, hlambda, hHsquare, hNninth, ?_⟩
  exact Polynomial.C_injective hCeq

/-- Source-facing first integral for a normalized scale-two `(4,10)` pair. -/
theorem normalized410ScaleTwo_discriminatorPowerRelation
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    let N := (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9
    ∃ κ : K, N ^ 2 = Polynomial.C κ * H ^ 9 := by
  dsimp only
  rcases hsource with
    ⟨hH, _hHdegree, hPdegree, hQdegree, hp4, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  exact imprimitiveDiscriminatorPowerRelation_410
    hp hq hjac hH (by simpa only [p] using hp4)
      (by simpa only [q] using hq10)

/-- The exact first-face dichotomy for every normalized scale-two `(4,10)`
source: the discriminator vanishes, or its square is a nonzero scalar times
the ninth power of the quadratic common core. -/
theorem normalized410ScaleTwo_discriminatorFirstFace
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    let N := (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9
    N = 0 ∨ ∃ κ : K, κ ≠ 0 ∧ N ^ 2 = Polynomial.C κ * H ^ 9 := by
  dsimp only
  obtain ⟨κ, hrelation⟩ :=
    normalized410ScaleTwo_discriminatorPowerRelation hsource
  by_cases hκ : κ = 0
  · left
    have hNsquare :
        ((5 : K[X]) *
            ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 3 *
              H ^ 3 -
          (2 : K[X]) *
            ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff 9) ^ 2 =
          0 := by
      simpa only [hκ, Polynomial.C_0, zero_mul] using hrelation
    exact sq_eq_zero_iff.mp hNsquare
  · exact Or.inr ⟨κ, hκ, hrelation⟩

/-- Over an algebraically closed ground field the nonzero first face has the
literal square/ninth-power form required by a source-pole analysis. -/
theorem normalized410ScaleTwo_imprimitiveDiscriminatorDichotomy
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    let N := (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9
    N = 0 ∨
      ∃ (h : K[X]) (lambda : K),
        h ≠ 0 ∧ lambda ≠ 0 ∧ H = h ^ 2 ∧
          N = Polynomial.C lambda * h ^ 9 := by
  dsimp only
  rcases normalized410ScaleTwo_discriminatorFirstFace hsource with
    hzero | ⟨κ, hκ, hrelation⟩
  · exact Or.inl hzero
  · right
    obtain ⟨h, lambda, hh, hlambda, hH, hN, _hlambdaSq⟩ :=
      squareCore_of_nonzero_imprimitiveRelation_410
        hsource.1 hκ hrelation
    exact ⟨h, lambda, hh, hlambda, hH, hN⟩

/-- The nonaligned scale-two face carries a degree-one square root of the
common core and hence a concrete finite root.  This is the exact entry point
for a later weighted-infinity/local-pole analysis. -/
theorem normalized410ScaleTwo_nonzeroFace_has_linear_root
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    let N := (5 : K[X]) * p.coeff 3 * H ^ 3 - (2 : K[X]) * q.coeff 9
    ∃ (h : K[X]) (lambda a : K),
      h ≠ 0 ∧ lambda ≠ 0 ∧ h.natDegree = 1 ∧
        H = h ^ 2 ∧ h.eval a = 0 ∧
          N = Polynomial.C lambda * h ^ 9 := by
  dsimp only at hnonzero ⊢
  rcases normalized410ScaleTwo_imprimitiveDiscriminatorDichotomy
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

#print axioms imprimitiveDiscriminatorPowerRelation_410
#print axioms commonCore_of_powerRelation_29
#print axioms normalized410ScaleTwo_discriminatorFirstFace
#print axioms normalized410ScaleTwo_imprimitiveDiscriminatorDichotomy
#print axioms normalized410ScaleTwo_nonzeroFace_has_linear_root

end Max11DegreeRoutes
