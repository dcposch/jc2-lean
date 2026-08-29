import LowScale68SourceBridge

/-! # Scale-two source reduction for the normalized `(6,8)`, `H = 2` leaf

The first row below the leading weighted-Wronskian row has the source
discriminator

`N = 4 * p₅ * H - 3 * q₇`.

This file proves directly from the literal Keller bracket that
`N² = C κ * H⁷`.  Thus the normalized scale-two source has an exact first
face: either it is aligned (`N = 0`), or it lies on the nonzero seventh-power
face.  No total-degree or twice-prime theorem is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-- The first Jacobian row below the leading row for outer degrees `(6,8)`.
It is the literal source of the septic depression discriminator. -/
theorem nextCoefficientJacobianRow_68 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 6).derivative * (q.coeff 7 * Polynomial.C (7 : K)) +
        (p.coeff 5).derivative * (q.coeff 8 * Polynomial.C (8 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 7).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 8).derivative) = 0 := by
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
  have hC7 : Polynomial.C (7 : K) = (7 : K[X]) :=
    Polynomial.C_eq_natCast 7
  have hC8 : Polynomial.C (8 : K) = (8 : K[X]) :=
    Polynomial.C_eq_natCast 8
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) :=
    Polynomial.C_eq_natCast 6
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  rw [hC7, hC8, hC6, hC5]
  linear_combination hcoeff

/-- With leading coefficients `H³,H⁴`, the next row is precisely the
weighted derivative of `N = 4 p₅ H - 3 q₇`. -/
theorem imprimitiveDiscriminatorRow_eq_zero_68 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4) :
    let N := (4 : K[X]) * p.coeff 5 * H - (3 : K[X]) * q.coeff 7
    (2 : K[X]) * H * N.derivative -
        (7 : K[X]) * N * H.derivative = 0 := by
  dsimp only
  have hrow := nextCoefficientJacobianRow_68 hp hq hjac
  rw [hp6, hq8] at hrow
  have hscaled : H ^ 2 *
      ((2 : K[X]) * H *
          ((4 : K[X]) * p.coeff 5 * H -
            (3 : K[X]) * q.coeff 7).derivative -
        (7 : K[X]) *
          ((4 : K[X]) * p.coeff 5 * H -
            (3 : K[X]) * q.coeff 7) * H.derivative) = 0 := by
    calc
      H ^ 2 *
          ((2 : K[X]) * H *
              ((4 : K[X]) * p.coeff 5 * H -
                (3 : K[X]) * q.coeff 7).derivative -
            (7 : K[X]) *
              ((4 : K[X]) * p.coeff 5 * H -
                (3 : K[X]) * q.coeff 7) * H.derivative) =
          (H ^ 3).derivative * (q.coeff 7 * (7 : K[X])) +
              (p.coeff 5).derivative * (H ^ 4 * (8 : K[X])) -
            ((H ^ 3 * (6 : K[X])) * (q.coeff 7).derivative +
              (p.coeff 5 * (5 : K[X])) * (H ^ 4).derivative) := by
                simp only [Polynomial.derivative_sub,
                  Polynomial.derivative_mul, Polynomial.derivative_pow,
                  Polynomial.derivative_ofNat,
                  Polynomial.C_eq_natCast, zero_mul, zero_add]
                ring
      _ = 0 := hrow
  exact (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero 2 hH)

/-- Polynomial first integral of the `(6,8)` source discriminator. -/
theorem imprimitiveDiscriminatorPowerRelation_68 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K} {H : K[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4) :
    let N := (4 : K[X]) * p.coeff 5 * H - (3 : K[X]) * q.coeff 7
    ∃ κ : K, N ^ 2 = Polynomial.C κ * H ^ 7 := by
  dsimp only
  let N : K[X] :=
    (4 : K[X]) * p.coeff 5 * H - (3 : K[X]) * q.coeff 7
  have hrow :
      (2 : K[X]) * H * N.derivative -
          (7 : K[X]) * N * H.derivative = 0 := by
    simpa only [N] using
      imprimitiveDiscriminatorRow_eq_zero_68 hp hq hjac hH hp6 hq8
  have hrowC :
      Polynomial.C (2 : K) * H * N.derivative -
          Polynomial.C (7 : K) * N * H.derivative = 0 := by
    have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
      Polynomial.C_eq_natCast 2
    have hC7 : Polynomial.C (7 : K) = (7 : K[X]) :=
      Polynomial.C_eq_natCast 7
    rw [hC2, hC7]
    exact hrow
  have hW : Polynomial.wronskian (N ^ 2) (H ^ 7) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      N ^ 2 * (Polynomial.C (7 : K) * H ^ (7 - 1) * H.derivative) -
          (Polynomial.C (2 : K) * N ^ (2 - 1) * N.derivative) * H ^ 7 =
          N * H ^ 6 *
            (Polynomial.C (7 : K) * N * H.derivative -
              Polynomial.C (2 : K) * H * N.derivative) := by ring
      _ = 0 := by
        rw [sub_eq_zero.mpr (sub_eq_zero.mp hrowC).symm, mul_zero]
  exact eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 7 hH) hW

/-- UFD extraction tailored to the coprime powers `(2,7)`.  Removing the
gcd leaves a fifth/square relation, so the existing `(2,5)` extraction
finishes the proof. -/
theorem commonCore_of_powerRelation_27 {K : Type*}
    [Field K] [CharZero K] {A B : K[X]} (_hA : A ≠ 0) (hB : B ≠ 0)
    (c : K) (hc : c ≠ 0)
    (hpowers : A ^ 7 = Polynomial.C c * B ^ 2) :
    ∃ (alpha beta : K) (h : K[X]),
      alpha ≠ 0 ∧ beta ≠ 0 ∧ h ≠ 0 ∧
        A = Polynomial.C alpha * h ^ 2 ∧
        B = Polynomial.C beta * h ^ 7 := by
  classical
  letI := EuclideanDomain.gcdMonoid K[X]
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
  have hreduced : d ^ 5 * A' ^ 7 = Polynomial.C c * B' ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hd)
    calc
      d ^ 2 * (d ^ 5 * A' ^ 7) = (d * A') ^ 7 := by ring
      _ = A ^ 7 := by rw [hdA]
      _ = Polynomial.C c * B ^ 2 := hpowers
      _ = Polynomial.C c * (d * B') ^ 2 := by rw [hdB]
      _ = d ^ 2 * (Polynomial.C c * B' ^ 2) := by ring
  have hCunit : IsUnit (Polynomial.C c) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
  have hA'dvd : A' ∣ Polynomial.C c * B' ^ 2 := by
    refine ⟨d ^ 5 * A' ^ 6, ?_⟩
    rw [← hreduced]
    ring
  have hA'unit : IsUnit A' := by
    apply isUnit_of_dvd_unit
      (hcop.pow_right.dvd_of_dvd_mul_right hA'dvd) hCunit
  have hdpowassoc : Associated (d ^ 5) (B' ^ 2) :=
    (associated_mul_unit_left (d ^ 5) (A' ^ 7) (hA'unit.pow 7)).symm |>.trans
      (Associated.of_eq hreduced) |>.trans
        (associated_unit_mul_left (B' ^ 2) (Polynomial.C c) hCunit)
  obtain ⟨u, hu⟩ := hdpowassoc.symm
  obtain ⟨gamma, hgammaUnit, hgamma⟩ :=
    Polynomial.isUnit_iff.mp u.isUnit
  have hdpower : d ^ 5 = Polynomial.C gamma * B' ^ 2 := by
    calc
      d ^ 5 = B' ^ 2 * (u : K[X]) := hu.symm
      _ = Polynomial.C gamma * B' ^ 2 := by rw [← hgamma]; ring
  obtain ⟨delta, epsilon, h, hdelta, hepsilon, hh, hdcore, hB'core⟩ :=
    commonCore_of_powerRelation_25 hd hB' gamma
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
          (Polynomial.C epsilon * h ^ 5) := by rw [hdcore, hB'core]
      _ = Polynomial.C (delta * epsilon) * h ^ 7 := by
        rw [Polynomial.C_mul]
        ring

/-- On the nonzero first face, algebraic closure absorbs the scalar in the
quadratic core and yields the literal square/seventh-power source shape. -/
theorem squareCore_of_nonzero_imprimitiveRelation_68
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {H N : K[X]} {κ : K}
    (hH : H ≠ 0) (hκ : κ ≠ 0)
    (hrelation : N ^ 2 = Polynomial.C κ * H ^ 7) :
    ∃ (h : K[X]) (lambda : K),
      h ≠ 0 ∧ lambda ≠ 0 ∧ H = h ^ 2 ∧
        N = Polynomial.C lambda * h ^ 7 ∧ lambda ^ 2 = κ := by
  have hN : N ≠ 0 := by
    intro hzero
    have hright : Polynomial.C κ * H ^ 7 ≠ 0 :=
      mul_ne_zero (Polynomial.C_ne_zero.mpr hκ) (pow_ne_zero 7 hH)
    apply hright
    simpa [hzero] using hrelation.symm
  have hinverse : H ^ 7 = Polynomial.C κ⁻¹ * N ^ 2 := by
    calc
      H ^ 7 = (Polynomial.C κ⁻¹ * Polynomial.C κ) * H ^ 7 := by
        rw [← Polynomial.C_mul, inv_mul_cancel₀ hκ,
          Polynomial.C_1, one_mul]
      _ = Polynomial.C κ⁻¹ * (Polynomial.C κ * H ^ 7) := by ring
      _ = Polynomial.C κ⁻¹ * N ^ 2 := by rw [← hrelation]
  obtain ⟨alpha, beta, h₀, halpha, hbeta, hh₀, hHform, hNform⟩ :=
    commonCore_of_powerRelation_27 hH hN κ⁻¹
      (inv_ne_zero hκ) hinverse
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq alpha
    (by norm_num : 0 < 2)
  have ht0 : t ≠ 0 := by
    intro htzero
    apply halpha
    rw [← ht, htzero, zero_pow (by norm_num : 2 ≠ 0)]
  let h : K[X] := Polynomial.C t * h₀
  let lambda : K := beta * (t ^ 7)⁻¹
  have hh : h ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr ht0) hh₀
  have hlambda : lambda ≠ 0 :=
    mul_ne_zero hbeta (inv_ne_zero (pow_ne_zero 7 ht0))
  have hHsquare : H = h ^ 2 := by
    rw [hHform]
    dsimp only [h]
    rw [mul_pow, ← Polynomial.C_pow, ht]
  have hNseventh : N = Polynomial.C lambda * h ^ 7 := by
    have hcancel : lambda * t ^ 7 = beta := by
      dsimp only [lambda]
      field_simp
    calc
      N = Polynomial.C beta * h₀ ^ 7 := hNform
      _ = Polynomial.C (lambda * t ^ 7) * h₀ ^ 7 := by rw [hcancel]
      _ = (Polynomial.C lambda * Polynomial.C (t ^ 7)) * h₀ ^ 7 := by
        rw [Polynomial.C_mul]
      _ = Polynomial.C lambda * (Polynomial.C t * h₀) ^ 7 := by
        rw [mul_pow, ← Polynomial.C_pow]
        ring
      _ = Polynomial.C lambda * h ^ 7 := by rfl
  have hcoeff :
      Polynomial.C (lambda ^ 2) * h ^ 14 =
        Polynomial.C κ * h ^ 14 := by
    calc
      Polynomial.C (lambda ^ 2) * h ^ 14 =
          (Polynomial.C lambda * h ^ 7) ^ 2 := by
            simp only [mul_pow, map_pow]
            ring
      _ = N ^ 2 := by rw [← hNseventh]
      _ = Polynomial.C κ * H ^ 7 := hrelation
      _ = Polynomial.C κ * h ^ 14 := by rw [hHsquare]; ring
  have hCeq : Polynomial.C (lambda ^ 2) = Polynomial.C κ :=
    mul_right_cancel₀ (pow_ne_zero 14 hh) hcoeff
  refine ⟨h, lambda, hh, hlambda, hHsquare, hNseventh, ?_⟩
  exact Polynomial.C_injective hCeq

/-- Source-facing first integral for a normalized scale-two `(6,8)` pair. -/
theorem normalized68ScaleTwo_discriminatorPowerRelation
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    let N := (4 : K[X]) * p.coeff 5 * H - (3 : K[X]) * q.coeff 7
    ∃ κ : K, N ^ 2 = Polynomial.C κ * H ^ 7 := by
  dsimp only
  rcases hsource with
    ⟨hH, _hHdegree, hPdegree, hQdegree, hp6, hq8, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 8 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  exact imprimitiveDiscriminatorPowerRelation_68
    hp hq hjac hH (by simpa only [p] using hp6)
      (by simpa only [q] using hq8)

/-- The exact first-face dichotomy for every normalized scale-two `(6,8)`
source: the discriminator vanishes, or its square is a nonzero scalar times
the seventh power of the quadratic common core. -/
theorem normalized68ScaleTwo_discriminatorFirstFace
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    let N := (4 : K[X]) * p.coeff 5 * H - (3 : K[X]) * q.coeff 7
    N = 0 ∨ ∃ κ : K, κ ≠ 0 ∧ N ^ 2 = Polynomial.C κ * H ^ 7 := by
  dsimp only
  obtain ⟨κ, hrelation⟩ :=
    normalized68ScaleTwo_discriminatorPowerRelation hsource
  by_cases hκ : κ = 0
  · left
    have hNsquare :
        ((4 : K[X]) *
            ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 5 * H -
          (3 : K[X]) *
            ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff 7) ^ 2 =
          0 := by
      simpa only [hκ, Polynomial.C_0, zero_mul] using hrelation
    exact sq_eq_zero_iff.mp hNsquare
  · exact Or.inr ⟨κ, hκ, hrelation⟩

/-- Over an algebraically closed ground field the nonzero first face has the
literal square/seventh-power form required by a source-pole analysis. -/
theorem normalized68ScaleTwo_imprimitiveDiscriminatorDichotomy
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    let N := (4 : K[X]) * p.coeff 5 * H - (3 : K[X]) * q.coeff 7
    N = 0 ∨
      ∃ (h : K[X]) (lambda : K),
        h ≠ 0 ∧ lambda ≠ 0 ∧ H = h ^ 2 ∧
          N = Polynomial.C lambda * h ^ 7 := by
  dsimp only
  rcases normalized68ScaleTwo_discriminatorFirstFace hsource with
    hzero | ⟨κ, hκ, hrelation⟩
  · exact Or.inl hzero
  · right
    obtain ⟨h, lambda, hh, hlambda, hH, hN, _hlambdaSq⟩ :=
      squareCore_of_nonzero_imprimitiveRelation_68
        hsource.1 hκ hrelation
    exact ⟨h, lambda, hh, hlambda, hH, hN⟩

/-- The nonaligned scale-two face carries a degree-one square root of the
common core and hence a concrete finite root.  This is the exact entry point
for the weighted-infinity/local-pole machinery. -/
theorem normalized68ScaleTwo_nonzeroFace_has_linear_root
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2)
    (hnonzero :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (4 : K[X]) * p.coeff 5 * H - (3 : K[X]) * q.coeff 7 ≠ 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    let N := (4 : K[X]) * p.coeff 5 * H - (3 : K[X]) * q.coeff 7
    ∃ (h : K[X]) (lambda a : K),
      h ≠ 0 ∧ lambda ≠ 0 ∧ h.natDegree = 1 ∧
        H = h ^ 2 ∧ h.eval a = 0 ∧
          N = Polynomial.C lambda * h ^ 7 := by
  dsimp only at hnonzero ⊢
  rcases normalized68ScaleTwo_imprimitiveDiscriminatorDichotomy
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

#print axioms imprimitiveDiscriminatorPowerRelation_68
#print axioms commonCore_of_powerRelation_27
#print axioms normalized68ScaleTwo_discriminatorFirstFace
#print axioms normalized68ScaleTwo_imprimitiveDiscriminatorDichotomy
#print axioms normalized68ScaleTwo_nonzeroFace_has_linear_root

end Max11DegreeRoutes
