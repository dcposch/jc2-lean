import LowScale46NewtonFaces

/-! # Polynomial coefficient-curve endgame for the `(4,6)` leaf

This module instantiates the generic leading-degree cancellation principle on
the two exact coefficient-curve equations.  In the mismatch branch, when all
three coefficient functions are nonconstant, the abstract support conditions
are therefore consequences of the actual polynomial equations rather than
extra hypotheses.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-- The first coefficient-curve row over the polynomial base `F[x]`, with
all structural constants embedded coefficientwise. -/
def coefficientCurveTwoPolynomial46 {F : Type*} [Field F]
    (L beta gamma delta : F) (A B U : F[X]) : F[X] :=
  C ((5 / 32 : F) * L) * A ^ 3 + C ((3 / 8 : F) * beta) * A ^ 2 +
    C ((-5 / 16 : F) * L) * (A * U) + C delta * A +
    C ((5 / 8 : F) * L) * B ^ 2 + C (-3 / 4 : F) * (B * U) +
    C (2 * gamma) * B + C ((-3 / 4 : F) * beta) * U

/-- The second coefficient-curve row over the polynomial base `F[x]`. -/
def coefficientCurveOnePolynomial46 {F : Type*} [Field F]
    (L beta gamma delta : F) (A B U : F[X]) : F[X] :=
  C ((-5 / 32 : F) * L) * (A ^ 2 * B) +
    C (-3 / 4 : F) * (A * B ^ 2) +
    C ((-3 / 4 : F) * beta) * (A * B) +
    C ((-5 / 16 : F) * L) * (B * U) + C delta * B +
    C (3 / 32 : F) * U ^ 2 + C (-1 / 2 * gamma) * U

/-- Coefficient of `A'` in the polynomial pullback of the final-row form. -/
def etaAPolynomial46 {F : Type*} [Field F]
    (L beta gamma delta : F) (A B U : F[X]) : F[X] :=
  C ((15 / 64 : F) * L) * A ^ 3 + C ((-5 / 16 : F) * L) * B ^ 2 +
    C ((-5 / 32 : F) * L) * (A * U) +
    C ((3 / 8 : F) * beta) * A ^ 2 +
    C (3 / 16 : F) * (B * U) + C (-1 / 2 * gamma) * B +
    C (1 / 2 * delta) * A

/-- Coefficient of `B'` in the polynomial pullback of the final-row form. -/
def etaBPolynomial46 {F : Type*} [Field F]
    (L beta : F) (A B : F[X]) : F[X] :=
  C ((-5 / 16 : F) * L) * (A * B) +
    C (-3 / 4 : F) * B ^ 2 + C ((-3 / 4 : F) * beta) * B

/-- Coefficient of `U'` in the polynomial pullback of the final-row form. -/
def etaUPolynomial46 {F : Type*} [Field F]
    (L beta delta : F) (A U : F[X]) : F[X] :=
  C ((-15 / 128 : F) * L) * A ^ 2 + C ((5 / 64 : F) * L) * U +
    C ((-3 / 16 : F) * beta) * A + C (-1 / 4 * delta)

/-- Pullback of the final-row one-form along a polynomial coefficient
trajectory. -/
def etaPolynomial46 {F : Type*} [Field F]
    (L beta gamma delta : F) (A B U : F[X]) : F[X] :=
  etaAPolynomial46 L beta gamma delta A B U * derivative A +
    etaBPolynomial46 L beta A B * derivative B +
    etaUPolynomial46 L beta delta A U * derivative U

section DegreeBounds

variable {F : Type*} [Field F]

/-- Multiplication by a constant cannot increase polynomial degree. -/
private theorem natDegree_C_mul_le46 (c : F) (P : F[X]) :
    (C c * P).natDegree ≤ P.natDegree := by
  calc
    (C c * P).natDegree ≤ (C c).natDegree + P.natDegree := natDegree_mul_le
    _ = P.natDegree := by rw [natDegree_C, zero_add]

/-- A five-term lower-order package used in each coefficient-curve row. -/
private theorem natDegree_four_add_sub_C_le46
    (p q r s : F[X]) (c : F) :
    (p + q + r + s - C c).natDegree ≤
      max (max p.natDegree q.natDegree)
        (max (max r.natDegree s.natDegree) 0) := by
  have hpq := natDegree_add_le p q
  have hpqr := natDegree_add_le (p + q) r
  have hpqrs := natDegree_add_le (p + q + r) s
  have hall := natDegree_sub_le (p + q + r + s) (C c)
  rw [natDegree_C] at hall
  omega

/-- If two nonzero displayed terms dominate a lower remainder in a vanishing
sum, their degrees are equal. -/
private theorem natDegree_eq_of_two_polynomial_terms_add_lower_eq_zero46
    (p q t : F[X]) (hp : p ≠ 0) (hq : q ≠ 0)
    (ht : t.natDegree < max p.natDegree q.natDegree)
    (hsum : p + q + t = 0) : p.natDegree = q.natDegree := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hpq | hqp
  · have hp0 := coeff_eq_zero_of_natDegree_lt hpq
    have ht0 : t.coeff q.natDegree = 0 := coeff_eq_zero_of_natDegree_lt (by
      rw [max_eq_right hpq.le] at ht
      exact ht)
    have hcoeff := congrArg (fun u : F[X] => u.coeff q.natDegree) hsum
    simp only [coeff_add, coeff_zero, hp0, ht0, zero_add, add_zero] at hcoeff
    have hq0 : q.coeff q.natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hq
    exact hq0 hcoeff
  · have hq0 := coeff_eq_zero_of_natDegree_lt hqp
    have ht0 : t.coeff p.natDegree = 0 := coeff_eq_zero_of_natDegree_lt (by
      rw [max_eq_left hqp.le] at ht
      exact ht)
    have hcoeff := congrArg (fun u : F[X] => u.coeff p.natDegree) hsum
    simp only [coeff_add, coeff_zero, hq0, ht0, add_zero] at hcoeff
    have hp0 : p.coeff p.natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hp
    exact hp0 hcoeff

/-- A single nonzero term cannot be cancelled by a strictly lower-degree
remainder. -/
private theorem singlePolynomialTerm_add_lower_ne_zero46
    (p t : F[X]) (hp : p ≠ 0) (ht : t.natDegree < p.natDegree) :
    p + t ≠ 0 := by
  intro hsum
  have ht0 := coeff_eq_zero_of_natDegree_lt ht
  have hcoeff := congrArg (fun u : F[X] => u.coeff p.natDegree) hsum
  simp only [coeff_add, coeff_zero, ht0, add_zero] at hcoeff
  have hp0 : p.coeff p.natDegree ≠ 0 := by
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hp
  exact hp0 hcoeff

end DegreeBounds

section MismatchPolynomialCone

variable {F : Type*} [Field F] [CharZero F]

/-- The first exact mismatch coefficient-curve equation supplies its required
four-way leading-degree tie whenever `A`, `B`, and `U` are nonconstant. -/
theorem mismatchPolynomialJTwoMaxTie46
    (L beta gamma delta k2 : F) (A B U : F[X])
    (hL : L ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (ha : 0 < A.natDegree) (hb : 0 < B.natDegree)
    (hu : 0 < U.natDegree)
    (hJ2 : coefficientCurveTwoPolynomial46 L beta gamma delta A B U = C k2) :
    MaxTie4 (3 * A.natDegree) (A.natDegree + U.natDegree)
      (2 * B.natDegree) (B.natDegree + U.natDegree) := by
  let p : F[X] := C ((5 / 32 : F) * L) * A ^ 3
  let q : F[X] := C ((-5 / 16 : F) * L) * (A * U)
  let r : F[X] := C ((5 / 8 : F) * L) * B ^ 2
  let s : F[X] := C (-3 / 4 : F) * (B * U)
  let t : F[X] := C ((3 / 8 : F) * beta) * A ^ 2 +
    C delta * A + C (2 * gamma) * B +
    C ((-3 / 4 : F) * beta) * U - C k2
  have hp : p ≠ 0 := by
    dsimp [p]
    exact mul_ne_zero (C_ne_zero.mpr (mul_ne_zero (by norm_num) hL))
      (pow_ne_zero 3 hA)
  have hq : q ≠ 0 := by
    dsimp [q]
    exact mul_ne_zero (C_ne_zero.mpr (mul_ne_zero (by norm_num) hL))
      (mul_ne_zero hA hU)
  have hr : r ≠ 0 := by
    dsimp [r]
    exact mul_ne_zero (C_ne_zero.mpr (mul_ne_zero (by norm_num) hL))
      (pow_ne_zero 2 hB)
  have hs : s ≠ 0 := by
    dsimp [s]
    exact mul_ne_zero (C_ne_zero.mpr (by norm_num)) (mul_ne_zero hB hU)
  have hpdeg : p.natDegree = 3 * A.natDegree := by
    dsimp [p]
    rw [natDegree_C_mul (mul_ne_zero (by norm_num) hL), natDegree_pow]
  have hqdeg : q.natDegree = A.natDegree + U.natDegree := by
    dsimp [q]
    rw [natDegree_C_mul (mul_ne_zero (by norm_num) hL),
      natDegree_mul hA hU]
  have hrdeg : r.natDegree = 2 * B.natDegree := by
    dsimp [r]
    rw [natDegree_C_mul (mul_ne_zero (by norm_num) hL), natDegree_pow]
  have hsdeg : s.natDegree = B.natDegree + U.natDegree := by
    dsimp [s]
    rw [natDegree_C_mul (by norm_num), natDegree_mul hB hU]
  have htA : (C ((3 / 8 : F) * beta) * A ^ 2).natDegree ≤
      2 * A.natDegree := by
    refine (natDegree_C_mul_le46 _ _).trans_eq ?_
    rw [natDegree_pow]
  have htD : (C delta * A).natDegree ≤ A.natDegree :=
    natDegree_C_mul_le46 _ _
  have htG : (C (2 * gamma) * B).natDegree ≤ B.natDegree :=
    natDegree_C_mul_le46 _ _
  have htB : (C ((-3 / 4 : F) * beta) * U).natDegree ≤ U.natDegree :=
    natDegree_C_mul_le46 _ _
  have ht0 := natDegree_four_add_sub_C_le46
    (C ((3 / 8 : F) * beta) * A ^ 2) (C delta * A)
    (C (2 * gamma) * B) (C ((-3 / 4 : F) * beta) * U) k2
  have htbound : t.natDegree ≤
      max (max (2 * A.natDegree) A.natDegree)
        (max (max B.natDegree U.natDegree) 0) := by
    dsimp [t]
    omega
  have ht : t.natDegree <
      max (max p.natDegree q.natDegree) (max r.natDegree s.natDegree) := by
    rw [hpdeg, hqdeg, hrdeg, hsdeg]
    omega
  have hsum : p + q + r + s + t = 0 := by
    calc
      p + q + r + s + t =
          coefficientCurveTwoPolynomial46 L beta gamma delta A B U - C k2 := by
            dsimp [p, q, r, s, t, coefficientCurveTwoPolynomial46]
            ring
      _ = 0 := sub_eq_zero.mpr hJ2
  have htie := maxTie4_of_polynomial_sum_add_lower_eq_zero46
    p q r s t hp hq hr hs ht hsum
  simpa [hpdeg, hqdeg, hrdeg, hsdeg] using htie

/-- The second exact mismatch coefficient-curve equation supplies its
four-way leading-degree tie under the same nonconstancy hypotheses. -/
theorem mismatchPolynomialJOneMaxTie46
    (L beta gamma delta k1 : F) (A B U : F[X])
    (hL : L ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (ha : 0 < A.natDegree) (hb : 0 < B.natDegree)
    (hu : 0 < U.natDegree)
    (hJ1 : coefficientCurveOnePolynomial46 L beta gamma delta A B U = C k1) :
    MaxTie4 (2 * A.natDegree + B.natDegree)
      (A.natDegree + 2 * B.natDegree)
      (B.natDegree + U.natDegree) (2 * U.natDegree) := by
  let p : F[X] := C ((-5 / 32 : F) * L) * (A ^ 2 * B)
  let q : F[X] := C (-3 / 4 : F) * (A * B ^ 2)
  let r : F[X] := C ((-5 / 16 : F) * L) * (B * U)
  let s : F[X] := C (3 / 32 : F) * U ^ 2
  let t : F[X] := C ((-3 / 4 : F) * beta) * (A * B) +
    C delta * B + C (-1 / 2 * gamma) * U + 0 - C k1
  have hp : p ≠ 0 := by
    dsimp [p]
    exact mul_ne_zero (C_ne_zero.mpr (mul_ne_zero (by norm_num) hL))
      (mul_ne_zero (pow_ne_zero 2 hA) hB)
  have hq : q ≠ 0 := by
    dsimp [q]
    exact mul_ne_zero (C_ne_zero.mpr (by norm_num))
      (mul_ne_zero hA (pow_ne_zero 2 hB))
  have hr : r ≠ 0 := by
    dsimp [r]
    exact mul_ne_zero (C_ne_zero.mpr (mul_ne_zero (by norm_num) hL))
      (mul_ne_zero hB hU)
  have hs : s ≠ 0 := by
    dsimp [s]
    exact mul_ne_zero (C_ne_zero.mpr (by norm_num)) (pow_ne_zero 2 hU)
  have hpdeg : p.natDegree = 2 * A.natDegree + B.natDegree := by
    dsimp [p]
    rw [natDegree_C_mul (mul_ne_zero (by norm_num) hL),
      natDegree_mul (pow_ne_zero 2 hA) hB, natDegree_pow]
  have hqdeg : q.natDegree = A.natDegree + 2 * B.natDegree := by
    dsimp [q]
    rw [natDegree_C_mul (by norm_num),
      natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow]
  have hrdeg : r.natDegree = B.natDegree + U.natDegree := by
    dsimp [r]
    rw [natDegree_C_mul (mul_ne_zero (by norm_num) hL),
      natDegree_mul hB hU]
  have hsdeg : s.natDegree = 2 * U.natDegree := by
    dsimp [s]
    rw [natDegree_C_mul (by norm_num), natDegree_pow]
  have htAB : (C ((-3 / 4 : F) * beta) * (A * B)).natDegree ≤
      A.natDegree + B.natDegree := by
    refine (natDegree_C_mul_le46 _ _).trans_eq ?_
    rw [natDegree_mul hA hB]
  have htD : (C delta * B).natDegree ≤ B.natDegree :=
    natDegree_C_mul_le46 _ _
  have htG : (C (-1 / 2 * gamma) * U).natDegree ≤ U.natDegree :=
    natDegree_C_mul_le46 _ _
  have htZ : (0 : F[X]).natDegree ≤ 0 := by simp
  have ht0 := natDegree_four_add_sub_C_le46
    (C ((-3 / 4 : F) * beta) * (A * B)) (C delta * B)
    (C (-1 / 2 * gamma) * U) 0 k1
  have htbound : t.natDegree ≤
      max (max (A.natDegree + B.natDegree) B.natDegree)
        (max (max U.natDegree 0) 0) := by
    dsimp [t]
    omega
  have ht : t.natDegree <
      max (max p.natDegree q.natDegree) (max r.natDegree s.natDegree) := by
    rw [hpdeg, hqdeg, hrdeg, hsdeg]
    omega
  have hsum : p + q + r + s + t = 0 := by
    calc
      p + q + r + s + t =
          coefficientCurveOnePolynomial46 L beta gamma delta A B U - C k1 := by
            dsimp [p, q, r, s, t, coefficientCurveOnePolynomial46]
            ring
      _ = 0 := sub_eq_zero.mpr hJ1
  have htie := maxTie4_of_polynomial_sum_add_lower_eq_zero46
    p q r s t hp hq hr hs ht hsum
  simpa [hpdeg, hqdeg, hrdeg, hsdeg] using htie

/-- Exact mismatch coefficient-curve equations force the unique positive
degree cone `(4n,5n,7n)` when all three coefficient functions vary. -/
theorem mismatchPolynomialDegreeCone46
    (L beta gamma delta k2 k1 : F) (A B U : F[X])
    (hL : L ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (ha : 0 < A.natDegree) (hb : 0 < B.natDegree)
    (hu : 0 < U.natDegree)
    (hJ2 : coefficientCurveTwoPolynomial46 L beta gamma delta A B U = C k2)
    (hJ1 : coefficientCurveOnePolynomial46 L beta gamma delta A B U = C k1) :
    ∃ n : ℕ, 0 < n ∧ A.natDegree = 4 * n ∧
      B.natDegree = 5 * n ∧ U.natDegree = 7 * n := by
  exact mismatchDegreeCone46 A.natDegree B.natDegree U.natDegree ha hb hu
    (mismatchPolynomialJTwoMaxTie46 L beta gamma delta k2 A B U hL hA hB hU
      ha hb hu hJ2)
    (mismatchPolynomialJOneMaxTie46 L beta gamma delta k1 A B U hL hA hB hU
      ha hb hu hJ1)

/-- On the mismatch degree cone, the two actual curve equations give the two
reviewed leading-coefficient relations. -/
theorem mismatchPolynomialLeadingRelations46
    (L beta gamma delta k2 k1 : F) (A B U : F[X]) (n : ℕ)
    (hn : 0 < n) (_hL : L ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hAdeg : A.natDegree = 4 * n) (hBdeg : B.natDegree = 5 * n)
    (hUdeg : U.natDegree = 7 * n)
    (hJ2 : coefficientCurveTwoPolynomial46 L beta gamma delta A B U = C k2)
    (hJ1 : coefficientCurveOnePolynomial46 L beta gamma delta A B U = C k1) :
    5 * L * A.leadingCoeff ^ 3 = 24 * B.leadingCoeff * U.leadingCoeff ∧
      U.leadingCoeff ^ 2 = 8 * A.leadingCoeff * B.leadingCoeff ^ 2 := by
  have hA3deg : (A ^ 3).natDegree = 12 * n := by
    rw [natDegree_pow, hAdeg]
    omega
  have hA2deg : (A ^ 2).natDegree = 8 * n := by
    rw [natDegree_pow, hAdeg]
    omega
  have hAUdeg : (A * U).natDegree = 11 * n := by
    rw [natDegree_mul hA hU, hAdeg, hUdeg]
    omega
  have hB2deg : (B ^ 2).natDegree = 10 * n := by
    rw [natDegree_pow, hBdeg]
    omega
  have hBUdeg : (B * U).natDegree = 12 * n := by
    rw [natDegree_mul hB hU, hBdeg, hUdeg]
    omega
  have hA2Bdeg : (A ^ 2 * B).natDegree = 13 * n := by
    rw [natDegree_mul (pow_ne_zero 2 hA) hB, natDegree_pow, hAdeg, hBdeg]
    omega
  have hAB2deg : (A * B ^ 2).natDegree = 14 * n := by
    rw [natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow, hAdeg, hBdeg]
    omega
  have hABdeg : (A * B).natDegree = 9 * n := by
    rw [natDegree_mul hA hB, hAdeg, hBdeg]
    omega
  have hU2deg : (U ^ 2).natDegree = 14 * n := by
    rw [natDegree_pow, hUdeg]
    omega
  have hcA3 : (A ^ 3).coeff (12 * n) = A.leadingCoeff ^ 3 := by
    rw [← hA3deg, coeff_natDegree, leadingCoeff_pow]
  have hcA2 : (A ^ 2).coeff (12 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hcAU : (A * U).coeff (12 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hcB2 : (B ^ 2).coeff (12 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hcBU : (B * U).coeff (12 * n) =
      B.leadingCoeff * U.leadingCoeff := by
    rw [← hBUdeg, coeff_natDegree, leadingCoeff_mul]
  have hcA : A.coeff (12 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hcB : B.coeff (12 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hcU : U.coeff (12 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hcoeffJ2 := congrArg (fun P : F[X] => P.coeff (12 * n)) hJ2
  simp only [coefficientCurveTwoPolynomial46, coeff_add, coeff_C_mul,
    hcA3, hcA2, hcAU, hcA, hcB2, hcBU, hcB, hcU, mul_zero, add_zero] at hcoeffJ2
  have h12n : 12 * n ≠ 0 := by omega
  simp [coeff_C, h12n] at hcoeffJ2
  have hleadJ2 : 5 * L * A.leadingCoeff ^ 3 =
      24 * B.leadingCoeff * U.leadingCoeff := by
    linear_combination 32 * hcoeffJ2
  have hcA2B : (A ^ 2 * B).coeff (14 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hcAB2 : (A * B ^ 2).coeff (14 * n) =
      A.leadingCoeff * B.leadingCoeff ^ 2 := by
    rw [← hAB2deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hcAB : (A * B).coeff (14 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hcBU' : (B * U).coeff (14 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hcB' : B.coeff (14 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hcU2 : (U ^ 2).coeff (14 * n) = U.leadingCoeff ^ 2 := by
    rw [← hU2deg, coeff_natDegree, leadingCoeff_pow]
  have hcU' : U.coeff (14 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hcoeffJ1 := congrArg (fun P : F[X] => P.coeff (14 * n)) hJ1
  simp only [coefficientCurveOnePolynomial46, coeff_add, coeff_C_mul,
    hcA2B, hcAB2, hcAB, hcBU', hcB', hcU2, hcU', mul_zero,
    zero_add, add_zero] at hcoeffJ1
  have h14n : 14 * n ≠ 0 := by omega
  simp [coeff_C, h14n] at hcoeffJ1
  have hleadJ1 : U.leadingCoeff ^ 2 =
      8 * A.leadingCoeff * B.leadingCoeff ^ 2 := by
    linear_combination (32 / 3 : F) * hcoeffJ1
  exact ⟨hleadJ2, hleadJ1⟩

/-- In the all-nonconstant mismatch cone, the actual final-row pullback has
degree exactly `16n-1`; in particular it cannot be constant. -/
theorem mismatchPolynomialEtaNatDegree46
    (L beta gamma delta : F) (A B U : F[X]) (n : ℕ)
    (hn : 0 < n) (hL : L ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) (hU : U ≠ 0)
    (hAdeg : A.natDegree = 4 * n) (hBdeg : B.natDegree = 5 * n)
    (hUdeg : U.natDegree = 7 * n)
    (hlead : 5 * L * A.leadingCoeff ^ 3 =
      24 * B.leadingCoeff * U.leadingCoeff) :
    (etaPolynomial46 L beta gamma delta A B U).natDegree = 16 * n - 1 := by
  let topCoefficient : F[X] :=
    C ((15 / 64 : F) * L) * A ^ 3 + C (3 / 16 : F) * (B * U)
  let restA : F[X] :=
    C ((-5 / 16 : F) * L) * B ^ 2 +
      C ((-5 / 32 : F) * L) * (A * U) +
      C ((3 / 8 : F) * beta) * A ^ 2 +
      C (-1 / 2 * gamma) * B + C (1 / 2 * delta) * A
  let rest : F[X] := restA * derivative A +
    etaBPolynomial46 L beta A B * derivative B +
    etaUPolynomial46 L beta delta A U * derivative U
  have hAlead : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA
  have htopCoeff : topCoefficient.coeff (12 * n) =
      (35 / 128 : F) * L * A.leadingCoeff ^ 3 := by
    have hA3deg : (A ^ 3).natDegree = 12 * n := by
      rw [natDegree_pow, hAdeg]
      omega
    have hBUdeg : (B * U).natDegree = 12 * n := by
      rw [natDegree_mul hB hU, hBdeg, hUdeg]
      omega
    have hcA3 : (A ^ 3).coeff (12 * n) = A.leadingCoeff ^ 3 := by
      rw [← hA3deg, coeff_natDegree, leadingCoeff_pow]
    have hcBU : (B * U).coeff (12 * n) =
        B.leadingCoeff * U.leadingCoeff := by
      rw [← hBUdeg, coeff_natDegree, leadingCoeff_mul]
    dsimp [topCoefficient]
    rw [coeff_add, coeff_C_mul, coeff_C_mul, hcA3, hcBU]
    linear_combination (-1 / 128 : F) * hlead
  have htopCoeffNe : topCoefficient.coeff (12 * n) ≠ 0 := by
    rw [htopCoeff]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hL) (pow_ne_zero 3 hAlead)
  have htopDegreeLe : topCoefficient.natDegree ≤ 12 * n := by
    dsimp [topCoefficient]
    compute_degree
    omega
  have htopDegree : topCoefficient.natDegree = 12 * n :=
    natDegree_eq_of_le_of_coeff_ne_zero htopDegreeLe htopCoeffNe
  have htopCoefficient : topCoefficient ≠ 0 := by
    intro hz
    rw [hz, coeff_zero] at htopCoeffNe
    exact htopCoeffNe rfl
  have hderA : derivative A ≠ 0 := derivative_ne_zero.mpr (by omega)
  have htop : (topCoefficient * derivative A).natDegree = 16 * n - 1 := by
    rw [natDegree_mul htopCoefficient hderA,
      htopDegree, natDegree_derivative, hAdeg]
    omega
  have hrestA : restA.natDegree ≤ 11 * n := by
    dsimp [restA]
    compute_degree
    omega
  have hetaB : (etaBPolynomial46 L beta A B).natDegree ≤ 10 * n := by
    dsimp [etaBPolynomial46]
    compute_degree
    omega
  have hetaU : (etaUPolynomial46 L beta delta A U).natDegree ≤ 8 * n := by
    dsimp [etaUPolynomial46]
    compute_degree
    omega
  have hrest : rest.natDegree ≤ 15 * n - 1 := by
    dsimp [rest]
    have hdA := natDegree_derivative A
    have hdB := natDegree_derivative B
    have hdU := natDegree_derivative U
    have hmulA := natDegree_mul_le (p := restA) (q := derivative A)
    have hmulB := natDegree_mul_le
      (p := etaBPolynomial46 L beta A B) (q := derivative B)
    have hmulU := natDegree_mul_le
      (p := etaUPolynomial46 L beta delta A U) (q := derivative U)
    have hadd1 := natDegree_add_le
      (restA * derivative A) (etaBPolynomial46 L beta A B * derivative B)
    have hadd2 := natDegree_add_le
      (restA * derivative A + etaBPolynomial46 L beta A B * derivative B)
      (etaUPolynomial46 L beta delta A U * derivative U)
    omega
  have hrestlt : rest.natDegree < (topCoefficient * derivative A).natDegree := by
    rw [htop]
    omega
  have hsplit : etaPolynomial46 L beta gamma delta A B U =
      topCoefficient * derivative A + rest := by
    dsimp [etaPolynomial46, etaAPolynomial46, topCoefficient, restA, rest]
    ring
  rw [hsplit, natDegree_add_eq_left_of_natDegree_lt hrestlt, htop]

/-- The exact two curve rows rule out a constant last row on every mismatch
polynomial trajectory for which `A`, `B`, and `U` are all nonconstant. -/
theorem mismatchPolynomial_allNonconstant_impossible46
    (L beta gamma delta k2 k1 j : F) (A B U : F[X])
    (hL : L ≠ 0) (hAdeg : 0 < A.natDegree)
    (hBdeg : 0 < B.natDegree) (hUdeg : 0 < U.natDegree)
    (hJ2 : coefficientCurveTwoPolynomial46 L beta gamma delta A B U = C k2)
    (hJ1 : coefficientCurveOnePolynomial46 L beta gamma delta A B U = C k1)
    (hlast : etaPolynomial46 L beta gamma delta A B U = C j) : False := by
  have hA : A ≠ 0 := by
    intro h
    rw [h] at hAdeg
    simp at hAdeg
  have hB : B ≠ 0 := by
    intro h
    rw [h] at hBdeg
    simp at hBdeg
  have hU : U ≠ 0 := by
    intro h
    rw [h] at hUdeg
    simp at hUdeg
  obtain ⟨n, hn, hnA, hnB, hnU⟩ :=
    mismatchPolynomialDegreeCone46 L beta gamma delta k2 k1 A B U
      hL hA hB hU hAdeg hBdeg hUdeg hJ2 hJ1
  have hrelations := mismatchPolynomialLeadingRelations46
    L beta gamma delta k2 k1 A B U n hn hL hA hB hU hnA hnB hnU hJ2 hJ1
  have heta := mismatchPolynomialEtaNatDegree46 L beta gamma delta A B U n
    hn hL hA hB hU hnA hnB hnU hrelations.1
  have hpositive : 0 < (etaPolynomial46 L beta gamma delta A B U).natDegree := by
    rw [heta]
    omega
  rw [hlast, natDegree_C] at hpositive
  omega

/-- If `A` is constant while `B,U` vary in the mismatch branch, the first
curve row forces equal degrees and the `B² B'` contribution gives the unique
top degree of the last row. -/
theorem mismatchPolynomial_Aconstant_BU_nonconstant_impossible46
    (L beta gamma delta k2 k1 j a : F) (B U : F[X])
    (hL : L ≠ 0) (hBdeg : 0 < B.natDegree) (hUdeg : 0 < U.natDegree)
    (hJ2 : coefficientCurveTwoPolynomial46 L beta gamma delta (C a) B U = C k2)
    (_hJ1 : coefficientCurveOnePolynomial46 L beta gamma delta (C a) B U = C k1)
    (hlast : etaPolynomial46 L beta gamma delta (C a) B U = C j) : False := by
  have hB : B ≠ 0 := by
    intro h
    rw [h] at hBdeg
    simp at hBdeg
  have hU : U ≠ 0 := by
    intro h
    rw [h] at hUdeg
    simp at hUdeg
  let p : F[X] := C ((5 / 8 : F) * L) * B ^ 2
  let q : F[X] := C (-3 / 4 : F) * (B * U)
  let t : F[X] := C ((5 / 32 : F) * L) * (C a) ^ 3 +
    C ((3 / 8 : F) * beta) * (C a) ^ 2 +
    C ((-5 / 16 : F) * L) * (C a * U) + C delta * C a +
    C (2 * gamma) * B + C ((-3 / 4 : F) * beta) * U - C k2
  have hp : p ≠ 0 := by
    dsimp [p]
    exact mul_ne_zero (C_ne_zero.mpr (mul_ne_zero (by norm_num) hL))
      (pow_ne_zero 2 hB)
  have hq : q ≠ 0 := by
    dsimp [q]
    exact mul_ne_zero (C_ne_zero.mpr (by norm_num)) (mul_ne_zero hB hU)
  have hpdeg : p.natDegree = 2 * B.natDegree := by
    dsimp [p]
    rw [natDegree_C_mul (mul_ne_zero (by norm_num) hL), natDegree_pow]
  have hqdeg : q.natDegree = B.natDegree + U.natDegree := by
    dsimp [q]
    rw [natDegree_C_mul (by norm_num), natDegree_mul hB hU]
  have htbound : t.natDegree ≤ max B.natDegree U.natDegree := by
    dsimp [t]
    compute_degree
    omega
  have ht : t.natDegree < max p.natDegree q.natDegree := by
    rw [hpdeg, hqdeg]
    omega
  have hsum : p + q + t = 0 := by
    calc
      p + q + t =
          coefficientCurveTwoPolynomial46 L beta gamma delta (C a) B U - C k2 := by
            dsimp [p, q, t, coefficientCurveTwoPolynomial46]
            ring
      _ = 0 := sub_eq_zero.mpr hJ2
  have hdegrees := natDegree_eq_of_two_polynomial_terms_add_lower_eq_zero46
    p q t hp hq ht hsum
  rw [hpdeg, hqdeg] at hdegrees
  have hBUdeg : U.natDegree = B.natDegree := by omega
  let top : F[X] := C (-3 / 4 : F) * B ^ 2 * derivative B
  let restB : F[X] := C ((-5 / 16 : F) * L) * (C a * B) +
    C ((-3 / 4 : F) * beta) * B
  let rest : F[X] := restB * derivative B +
    etaUPolynomial46 L beta delta (C a) U * derivative U
  have hderB : derivative B ≠ 0 := derivative_ne_zero.mpr hBdeg.ne'
  have htop : top.natDegree = 3 * B.natDegree - 1 := by
    dsimp [top]
    rw [natDegree_mul
      (mul_ne_zero (C_ne_zero.mpr (by norm_num)) (pow_ne_zero 2 hB)) hderB,
      natDegree_C_mul (by norm_num), natDegree_pow, natDegree_derivative]
    omega
  have hrestB : restB.natDegree ≤ B.natDegree := by
    dsimp [restB]
    compute_degree
  have hetaU : (etaUPolynomial46 L beta delta (C a) U).natDegree ≤
      U.natDegree := by
    dsimp [etaUPolynomial46]
    compute_degree
  have hrest : rest.natDegree ≤ 2 * B.natDegree - 1 := by
    dsimp [rest]
    have hdB := natDegree_derivative B
    have hdU := natDegree_derivative U
    have hmulB := natDegree_mul_le (p := restB) (q := derivative B)
    have hmulU := natDegree_mul_le
      (p := etaUPolynomial46 L beta delta (C a) U) (q := derivative U)
    have hadd := natDegree_add_le (restB * derivative B)
      (etaUPolynomial46 L beta delta (C a) U * derivative U)
    omega
  have hrestlt : rest.natDegree < top.natDegree := by
    rw [htop]
    omega
  have hsplit : etaPolynomial46 L beta gamma delta (C a) B U = top + rest := by
    dsimp [etaPolynomial46, etaAPolynomial46, etaBPolynomial46,
      top, restB, rest]
    simp only [derivative_C, mul_zero, zero_add]
    ring
  have hetaDegree : (etaPolynomial46 L beta gamma delta (C a) B U).natDegree =
      3 * B.natDegree - 1 := by
    rw [hsplit, natDegree_add_eq_left_of_natDegree_lt hrestlt, htop]
  have hpositive : 0 < (etaPolynomial46 L beta gamma delta (C a) B U).natDegree := by
    rw [hetaDegree]
    omega
  rw [hlast, natDegree_C] at hpositive
  omega

/-- With only `A` varying, its cubic term is the unique top term of `J₂`. -/
theorem mismatchPolynomial_A_nonconstant_B_U_constant_impossible46
    (L beta gamma delta k2 b u : F) (A : F[X])
    (hL : L ≠ 0) (hAdeg : 0 < A.natDegree)
    (hJ2 : coefficientCurveTwoPolynomial46 L beta gamma delta A (C b) (C u) = C k2) :
    False := by
  have hA : A ≠ 0 := by
    intro h
    rw [h] at hAdeg
    simp at hAdeg
  let p : F[X] := C ((5 / 32 : F) * L) * A ^ 3
  let t : F[X] := C ((3 / 8 : F) * beta) * A ^ 2 +
    C ((-5 / 16 : F) * L) * (A * C u) + C delta * A +
    C ((5 / 8 : F) * L) * (C b) ^ 2 +
    C (-3 / 4 : F) * (C b * C u) + C (2 * gamma) * C b +
    C ((-3 / 4 : F) * beta) * C u - C k2
  have hp : p ≠ 0 := by
    dsimp [p]
    exact mul_ne_zero (C_ne_zero.mpr (mul_ne_zero (by norm_num) hL))
      (pow_ne_zero 3 hA)
  have hpdeg : p.natDegree = 3 * A.natDegree := by
    dsimp [p]
    rw [natDegree_C_mul (mul_ne_zero (by norm_num) hL), natDegree_pow]
  have htbound : t.natDegree ≤ 2 * A.natDegree := by
    dsimp [t]
    compute_degree
    omega
  have ht : t.natDegree < p.natDegree := by
    rw [hpdeg]
    omega
  have hsum : p + t = 0 := by
    calc
      p + t = coefficientCurveTwoPolynomial46 L beta gamma delta A (C b) (C u) - C k2 := by
        dsimp [p, t, coefficientCurveTwoPolynomial46]
        ring
      _ = 0 := sub_eq_zero.mpr hJ2
  exact singlePolynomialTerm_add_lower_ne_zero46 p t hp ht hsum

/-- With `A,U` varying and `B` constant, the first row forces
`deg U=2 deg A`, after which `U²` is uniquely top in `J₁`. -/
theorem mismatchPolynomial_AU_nonconstant_B_constant_impossible46
    (L beta gamma delta k2 k1 b : F) (A U : F[X])
    (hL : L ≠ 0) (hAdeg : 0 < A.natDegree) (hUdeg : 0 < U.natDegree)
    (hJ2 : coefficientCurveTwoPolynomial46 L beta gamma delta A (C b) U = C k2)
    (hJ1 : coefficientCurveOnePolynomial46 L beta gamma delta A (C b) U = C k1) :
    False := by
  have hA : A ≠ 0 := by
    intro h
    rw [h] at hAdeg
    simp at hAdeg
  have hU : U ≠ 0 := by
    intro h
    rw [h] at hUdeg
    simp at hUdeg
  let p : F[X] := C ((5 / 32 : F) * L) * A ^ 3
  let q : F[X] := C ((-5 / 16 : F) * L) * (A * U)
  let t : F[X] := C ((3 / 8 : F) * beta) * A ^ 2 + C delta * A +
    C ((5 / 8 : F) * L) * (C b) ^ 2 +
    C (-3 / 4 : F) * (C b * U) + C (2 * gamma) * C b +
    C ((-3 / 4 : F) * beta) * U - C k2
  have hp : p ≠ 0 := by
    dsimp [p]
    exact mul_ne_zero (C_ne_zero.mpr (mul_ne_zero (by norm_num) hL))
      (pow_ne_zero 3 hA)
  have hq : q ≠ 0 := by
    dsimp [q]
    exact mul_ne_zero (C_ne_zero.mpr (mul_ne_zero (by norm_num) hL))
      (mul_ne_zero hA hU)
  have hpdeg : p.natDegree = 3 * A.natDegree := by
    dsimp [p]
    rw [natDegree_C_mul (mul_ne_zero (by norm_num) hL), natDegree_pow]
  have hqdeg : q.natDegree = A.natDegree + U.natDegree := by
    dsimp [q]
    rw [natDegree_C_mul (mul_ne_zero (by norm_num) hL), natDegree_mul hA hU]
  have htbound : t.natDegree ≤ max (2 * A.natDegree) U.natDegree := by
    dsimp [t]
    compute_degree
    omega
  have ht : t.natDegree < max p.natDegree q.natDegree := by
    rw [hpdeg, hqdeg]
    omega
  have hsum : p + q + t = 0 := by
    calc
      p + q + t = coefficientCurveTwoPolynomial46 L beta gamma delta A (C b) U - C k2 := by
        dsimp [p, q, t, coefficientCurveTwoPolynomial46]
        ring
      _ = 0 := sub_eq_zero.mpr hJ2
  have hdegrees := natDegree_eq_of_two_polynomial_terms_add_lower_eq_zero46
    p q t hp hq ht hsum
  rw [hpdeg, hqdeg] at hdegrees
  have hUeq : U.natDegree = 2 * A.natDegree := by omega
  let lead : F[X] := C (3 / 32 : F) * U ^ 2
  let lower : F[X] := C ((-5 / 32 : F) * L) * (A ^ 2 * C b) +
    C (-3 / 4 : F) * (A * (C b) ^ 2) +
    C ((-3 / 4 : F) * beta) * (A * C b) +
    C ((-5 / 16 : F) * L) * (C b * U) + C delta * C b +
    C (-1 / 2 * gamma) * U - C k1
  have hlead : lead ≠ 0 := by
    dsimp [lead]
    exact mul_ne_zero (C_ne_zero.mpr (by norm_num)) (pow_ne_zero 2 hU)
  have hleaddeg : lead.natDegree = 2 * U.natDegree := by
    dsimp [lead]
    rw [natDegree_C_mul (by norm_num), natDegree_pow]
  have hlowerbound : lower.natDegree ≤ 2 * A.natDegree := by
    dsimp [lower]
    compute_degree
    omega
  have hlower : lower.natDegree < lead.natDegree := by
    rw [hleaddeg, hUeq]
    omega
  have hsum1 : lead + lower = 0 := by
    calc
      lead + lower = coefficientCurveOnePolynomial46 L beta gamma delta A (C b) U - C k1 := by
        dsimp [lead, lower, coefficientCurveOnePolynomial46]
        ring
      _ = 0 := sub_eq_zero.mpr hJ1
  exact singlePolynomialTerm_add_lower_ne_zero46 lead lower hlead hlower hsum1

/-- With `A,B` varying and `U` constant, the first row forces
`3 deg A=2 deg B`, after which `A B²` is uniquely top in `J₁`. -/
theorem mismatchPolynomial_AB_nonconstant_U_constant_impossible46
    (L beta gamma delta k2 k1 u : F) (A B : F[X])
    (hL : L ≠ 0) (hAdeg : 0 < A.natDegree) (hBdeg : 0 < B.natDegree)
    (hJ2 : coefficientCurveTwoPolynomial46 L beta gamma delta A B (C u) = C k2)
    (hJ1 : coefficientCurveOnePolynomial46 L beta gamma delta A B (C u) = C k1) :
    False := by
  have hA : A ≠ 0 := by
    intro h
    rw [h] at hAdeg
    simp at hAdeg
  have hB : B ≠ 0 := by
    intro h
    rw [h] at hBdeg
    simp at hBdeg
  let p : F[X] := C ((5 / 32 : F) * L) * A ^ 3
  let q : F[X] := C ((5 / 8 : F) * L) * B ^ 2
  let t : F[X] := C ((3 / 8 : F) * beta) * A ^ 2 +
    C ((-5 / 16 : F) * L) * (A * C u) + C delta * A +
    C (-3 / 4 : F) * (B * C u) + C (2 * gamma) * B +
    C ((-3 / 4 : F) * beta) * C u - C k2
  have hp : p ≠ 0 := by
    dsimp [p]
    exact mul_ne_zero (C_ne_zero.mpr (mul_ne_zero (by norm_num) hL))
      (pow_ne_zero 3 hA)
  have hq : q ≠ 0 := by
    dsimp [q]
    exact mul_ne_zero (C_ne_zero.mpr (mul_ne_zero (by norm_num) hL))
      (pow_ne_zero 2 hB)
  have hpdeg : p.natDegree = 3 * A.natDegree := by
    dsimp [p]
    rw [natDegree_C_mul (mul_ne_zero (by norm_num) hL), natDegree_pow]
  have hqdeg : q.natDegree = 2 * B.natDegree := by
    dsimp [q]
    rw [natDegree_C_mul (mul_ne_zero (by norm_num) hL), natDegree_pow]
  have htbound : t.natDegree ≤ max (2 * A.natDegree) B.natDegree := by
    dsimp [t]
    compute_degree
    omega
  have ht : t.natDegree < max p.natDegree q.natDegree := by
    rw [hpdeg, hqdeg]
    omega
  have hsum : p + q + t = 0 := by
    calc
      p + q + t = coefficientCurveTwoPolynomial46 L beta gamma delta A B (C u) - C k2 := by
        dsimp [p, q, t, coefficientCurveTwoPolynomial46]
        ring
      _ = 0 := sub_eq_zero.mpr hJ2
  have hdegrees := natDegree_eq_of_two_polynomial_terms_add_lower_eq_zero46
    p q t hp hq ht hsum
  rw [hpdeg, hqdeg] at hdegrees
  let lead : F[X] := C (-3 / 4 : F) * (A * B ^ 2)
  let lower : F[X] := C ((-5 / 32 : F) * L) * (A ^ 2 * B) +
    C ((-3 / 4 : F) * beta) * (A * B) +
    C ((-5 / 16 : F) * L) * (B * C u) + C delta * B +
    C (3 / 32 : F) * (C u) ^ 2 + C (-1 / 2 * gamma) * C u - C k1
  have hlead : lead ≠ 0 := by
    dsimp [lead]
    exact mul_ne_zero (C_ne_zero.mpr (by norm_num))
      (mul_ne_zero hA (pow_ne_zero 2 hB))
  have hleaddeg : lead.natDegree = A.natDegree + 2 * B.natDegree := by
    dsimp [lead]
    rw [natDegree_C_mul (by norm_num),
      natDegree_mul hA (pow_ne_zero 2 hB), natDegree_pow]
  have hlowerbound : lower.natDegree ≤ 2 * A.natDegree + B.natDegree := by
    dsimp [lower]
    compute_degree
    omega
  have hlower : lower.natDegree < lead.natDegree := by
    rw [hleaddeg]
    omega
  have hsum1 : lead + lower = 0 := by
    calc
      lead + lower = coefficientCurveOnePolynomial46 L beta gamma delta A B (C u) - C k1 := by
        dsimp [lead, lower, coefficientCurveOnePolynomial46]
        ring
      _ = 0 := sub_eq_zero.mpr hJ1
  exact singlePolynomialTerm_add_lower_ne_zero46 lead lower hlead hlower hsum1

/-- With `A,U` constant and only `B` varying, `B²` is uniquely top in the
first curve row. -/
theorem mismatchPolynomial_B_nonconstant_A_U_constant_impossible46
    (L beta gamma delta k2 a u : F) (B : F[X])
    (hL : L ≠ 0) (hBdeg : 0 < B.natDegree)
    (hJ2 : coefficientCurveTwoPolynomial46 L beta gamma delta (C a) B (C u) = C k2) :
    False := by
  have hB : B ≠ 0 := by
    intro h
    rw [h] at hBdeg
    simp at hBdeg
  let p : F[X] := C ((5 / 8 : F) * L) * B ^ 2
  let t : F[X] := C ((5 / 32 : F) * L) * (C a) ^ 3 +
    C ((3 / 8 : F) * beta) * (C a) ^ 2 +
    C ((-5 / 16 : F) * L) * (C a * C u) + C delta * C a +
    C (-3 / 4 : F) * (B * C u) + C (2 * gamma) * B +
    C ((-3 / 4 : F) * beta) * C u - C k2
  have hp : p ≠ 0 := by
    dsimp [p]
    exact mul_ne_zero (C_ne_zero.mpr (mul_ne_zero (by norm_num) hL))
      (pow_ne_zero 2 hB)
  have hpdeg : p.natDegree = 2 * B.natDegree := by
    dsimp [p]
    rw [natDegree_C_mul (mul_ne_zero (by norm_num) hL), natDegree_pow]
  have htbound : t.natDegree ≤ B.natDegree := by
    dsimp [t]
    compute_degree
  have ht : t.natDegree < p.natDegree := by
    rw [hpdeg]
    omega
  have hsum : p + t = 0 := by
    calc
      p + t = coefficientCurveTwoPolynomial46 L beta gamma delta (C a) B (C u) - C k2 := by
        dsimp [p, t, coefficientCurveTwoPolynomial46]
        ring
      _ = 0 := sub_eq_zero.mpr hJ2
  exact singlePolynomialTerm_add_lower_ne_zero46 p t hp ht hsum

/-- With `A,B` constant and only `U` varying, `U²` is uniquely top in the
second curve row. -/
theorem mismatchPolynomial_U_nonconstant_A_B_constant_impossible46
    (L beta gamma delta k1 a b : F) (U : F[X])
    (hUdeg : 0 < U.natDegree)
    (hJ1 : coefficientCurveOnePolynomial46 L beta gamma delta (C a) (C b) U = C k1) :
    False := by
  have hU : U ≠ 0 := by
    intro h
    rw [h] at hUdeg
    simp at hUdeg
  let p : F[X] := C (3 / 32 : F) * U ^ 2
  let t : F[X] := C ((-5 / 32 : F) * L) * ((C a) ^ 2 * C b) +
    C (-3 / 4 : F) * (C a * (C b) ^ 2) +
    C ((-3 / 4 : F) * beta) * (C a * C b) +
    C ((-5 / 16 : F) * L) * (C b * U) + C delta * C b +
    C (-1 / 2 * gamma) * U - C k1
  have hp : p ≠ 0 := by
    dsimp [p]
    exact mul_ne_zero (C_ne_zero.mpr (by norm_num)) (pow_ne_zero 2 hU)
  have hpdeg : p.natDegree = 2 * U.natDegree := by
    dsimp [p]
    rw [natDegree_C_mul (by norm_num), natDegree_pow]
  have htbound : t.natDegree ≤ U.natDegree := by
    dsimp [t]
    compute_degree
  have ht : t.natDegree < p.natDegree := by
    rw [hpdeg]
    omega
  have hsum : p + t = 0 := by
    calc
      p + t = coefficientCurveOnePolynomial46 L beta gamma delta (C a) (C b) U - C k1 := by
        dsimp [p, t, coefficientCurveOnePolynomial46]
        ring
      _ = 0 := sub_eq_zero.mpr hJ1
  exact singlePolynomialTerm_add_lower_ne_zero46 p t hp ht hsum

/-- Complete polynomial mismatch endgame.  For `L ≠ 0`, the two exact
coefficient-curve equations and a nonzero constant last row are inconsistent,
with every constant/nonconstant pattern of `A,B,U` handled internally. -/
theorem mismatchPolynomialTrajectory_impossible46
    (L beta gamma delta k2 k1 j : F) (A B U : F[X])
    (hL : L ≠ 0) (hj : j ≠ 0)
    (hJ2 : coefficientCurveTwoPolynomial46 L beta gamma delta A B U = C k2)
    (hJ1 : coefficientCurveOnePolynomial46 L beta gamma delta A B U = C k1)
    (hlast : etaPolynomial46 L beta gamma delta A B U = C j) : False := by
  by_cases hA0 : A.natDegree = 0
  · obtain ⟨a, ha⟩ := natDegree_eq_zero.mp hA0
    rw [← ha] at hJ2 hJ1 hlast
    by_cases hB0 : B.natDegree = 0
    · obtain ⟨b, hb⟩ := natDegree_eq_zero.mp hB0
      rw [← hb] at hJ2 hJ1 hlast
      by_cases hU0 : U.natDegree = 0
      · obtain ⟨u, hu⟩ := natDegree_eq_zero.mp hU0
        rw [← hu] at hJ2 hJ1 hlast
        have heta : etaPolynomial46 L beta gamma delta (C a) (C b) (C u) = 0 := by
          simp [etaPolynomial46]
        rw [heta] at hlast
        have hj0 : C j = C (0 : F) := by simpa using hlast.symm
        exact hj (C_injective hj0)
      · exact mismatchPolynomial_U_nonconstant_A_B_constant_impossible46
          L beta gamma delta k1 a b U (Nat.pos_of_ne_zero hU0) hJ1
    · have hBpos := Nat.pos_of_ne_zero hB0
      by_cases hU0 : U.natDegree = 0
      · obtain ⟨u, hu⟩ := natDegree_eq_zero.mp hU0
        rw [← hu] at hJ2 hJ1 hlast
        exact mismatchPolynomial_B_nonconstant_A_U_constant_impossible46
          L beta gamma delta k2 a u B hL hBpos hJ2
      · exact mismatchPolynomial_Aconstant_BU_nonconstant_impossible46
          L beta gamma delta k2 k1 j a B U hL hBpos
            (Nat.pos_of_ne_zero hU0) hJ2 hJ1 hlast
  · have hApos := Nat.pos_of_ne_zero hA0
    by_cases hB0 : B.natDegree = 0
    · obtain ⟨b, hb⟩ := natDegree_eq_zero.mp hB0
      rw [← hb] at hJ2 hJ1 hlast
      by_cases hU0 : U.natDegree = 0
      · obtain ⟨u, hu⟩ := natDegree_eq_zero.mp hU0
        rw [← hu] at hJ2 hJ1 hlast
        exact mismatchPolynomial_A_nonconstant_B_U_constant_impossible46
          L beta gamma delta k2 b u A hL hApos hJ2
      · exact mismatchPolynomial_AU_nonconstant_B_constant_impossible46
          L beta gamma delta k2 k1 b A U hL hApos
            (Nat.pos_of_ne_zero hU0) hJ2 hJ1
    · have hBpos := Nat.pos_of_ne_zero hB0
      by_cases hU0 : U.natDegree = 0
      · obtain ⟨u, hu⟩ := natDegree_eq_zero.mp hU0
        rw [← hu] at hJ2 hJ1 hlast
        exact mismatchPolynomial_AB_nonconstant_U_constant_impossible46
          L beta gamma delta k2 k1 u A B hL hApos hBpos hJ2 hJ1
      · exact mismatchPolynomial_allNonconstant_impossible46
          L beta gamma delta k2 k1 j A B U hL hApos hBpos
            (Nat.pos_of_ne_zero hU0) hJ2 hJ1 hlast

end MismatchPolynomialCone

end Max11DegreeRoutes
