import LowScale68SecondaryLaterDeepFiveToSixRowOnePart02Scratch

/-! # The row-one face in the later-deep five-to-six chamber

This module closes the two spurious families left by the I4/I3/row-zero
classification.  The only surviving top packet is `e = 0`, `a*b = 3*d`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveToSixRowOne68

variable {k : Type*} [Field k] [CharZero k]

private structure Leaf68Bound (p : k[X]) (u : ℕ) : Prop where
  le : p.natDegree ≤ u

private theorem leaf68_bd_of_le {p : k[X]} {u : ℕ} (h : p.natDegree ≤ u) :
    Leaf68Bound p u := ⟨h⟩

private theorem leaf68_bd_C (a : k) : Leaf68Bound (C a) 0 :=
  ⟨(natDegree_C a).le⟩

private theorem leaf68_bd_smul (r : k) {p : k[X]} {u : ℕ}
    (hp : Leaf68Bound p u) : Leaf68Bound (r • p) u :=
  ⟨(natDegree_smul_le r p).trans hp.le⟩

private theorem leaf68_bd_neg {p : k[X]} {u : ℕ}
    (hp : Leaf68Bound p u) : Leaf68Bound (-p) u :=
  ⟨(natDegree_neg p).le.trans hp.le⟩

private theorem leaf68_bd_add {p q : k[X]} {u v : ℕ}
    (hp : Leaf68Bound p u) (hq : Leaf68Bound q v) :
    Leaf68Bound (p + q) (max u v) :=
  ⟨(natDegree_add_le p q).trans (max_le_max hp.le hq.le)⟩

private theorem leaf68_bd_sub {p q : k[X]} {u v : ℕ}
    (hp : Leaf68Bound p u) (hq : Leaf68Bound q v) :
    Leaf68Bound (p - q) (max u v) :=
  ⟨(natDegree_sub_le p q).trans (max_le_max hp.le hq.le)⟩

private theorem leaf68_bd_mul {p q : k[X]} {u v : ℕ}
    (hp : Leaf68Bound p u) (hq : Leaf68Bound q v) :
    Leaf68Bound (p * q) (u + v) :=
  ⟨natDegree_mul_le.trans (Nat.add_le_add hp.le hq.le)⟩

private theorem leaf68_bd_pow {p : k[X]} {u : ℕ} (m : ℕ)
    (hp : Leaf68Bound p u) : Leaf68Bound (p ^ m) (m * u) :=
  ⟨natDegree_pow_le.trans (Nat.mul_le_mul (le_refl m) hp.le)⟩

private theorem leaf68_bd_deriv {p : k[X]} {u : ℕ}
    (hp : Leaf68Bound p u) : Leaf68Bound (derivative p) (u - 1) :=
  ⟨(natDegree_derivative_le p).trans (Nat.sub_le_sub_right hp.le 1)⟩

private theorem leaf68_lt_of_bd {p : k[X]} {u b : ℕ}
    (hp : Leaf68Bound p u) (h : u < b) : p.natDegree < b :=
  lt_of_le_of_lt hp.le h

private theorem leaf68_le_of_bd {p : k[X]} {u b : ℕ}
    (hp : Leaf68Bound p u) (h : u ≤ b) : p.natDegree ≤ b :=
  hp.le.trans h


set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem cubicHomogeneousRowOnePolynomial68_secondaryCoeff_fiveToSix
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicHomogeneousRowOnePolynomial68 A B c D e).coeff
        (12 * n - 2 * g - 1) =
      (-8 / 81 : k) * firstSecondaryOne68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hrem : (cubicRemainderRowOnePolynomial68 A B c D e).natDegree <
      12 * n - 2 * g - 1 := by
    simp only [cubicRemainderRowOnePolynomial68]
    apply leaf68_lt_of_bd
    repeat'
      first
      | with_reducible exact leaf68_bd_of_le hA
      | with_reducible exact leaf68_bd_of_le hB
      | with_reducible exact leaf68_bd_of_le hc
      | with_reducible exact leaf68_bd_of_le hD
      | with_reducible exact leaf68_bd_of_le he
      | with_reducible apply leaf68_bd_smul
      | with_reducible apply leaf68_bd_neg
      | with_reducible apply leaf68_bd_sub
      | with_reducible apply leaf68_bd_add
      | with_reducible apply leaf68_bd_pow
      | with_reducible apply leaf68_bd_deriv
      | with_reducible apply leaf68_bd_mul
      | with_reducible apply leaf68_bd_C
      | omega
  rw [cubicHomogeneousRowOnePolynomial68_eq_expanded,
    cubicHomogeneousRowOneExpandedPolynomial68, coeff_add,
    coeff_eq_zero_of_natDegree_lt hrem, add_zero]
  exact firstSecondaryCoreRowOnePolynomial68_coeff_fiveToSix
    A B c D e n g hn hwindow hA hB hc hD he

/-- After `l=beta=delta=0`, the remaining load correction in row one has a
small exact Wronskian form. -/
theorem cubicLoadRowOnePolynomial68_zero_beta_delta_exact
    (alpha gamma epsilon zeta eta : k) (A B c D e : k[X]) :
    cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c D e =
      (2 / 3 * gamma : k) • (B * derivative D - D * derivative B) +
      (4 / 3 * gamma : k) • (A * derivative e) -
      (4 / 3 * gamma : k) • (c * derivative c) +
      (2 / 3 * epsilon : k) • (A * derivative c) +
      (2 * epsilon : k) • derivative e + zeta • derivative D := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadRowOnePolynomial68, cubicLoadTPolynomial68,
    cubicLoadUPolynomial68, cubicLoadVPolynomial68, derivative_add,
    derivative_sub, derivative_smul, derivative_mul, derivative_pow,
    derivative_C, zero_pow, zero_smul, smul_zero, zero_mul, mul_zero,
    add_zero, zero_add, sub_zero, Polynomial.C_eq_natCast,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
    map_neg, map_zero, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one]
  ring

theorem cubicLoadRowOnePolynomial68_degree_lt_fiveToSix
    (alpha gamma epsilon zeta eta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c D e).natDegree < 12 * n - 2 * g - 1 := by
  rw [cubicLoadRowOnePolynomial68_zero_beta_delta_exact]
  apply leaf68_lt_of_bd
  repeat'
    first
    | with_reducible exact leaf68_bd_of_le hA
    | with_reducible exact leaf68_bd_of_le hB
    | with_reducible exact leaf68_bd_of_le hc
    | with_reducible exact leaf68_bd_of_le hD
    | with_reducible exact leaf68_bd_of_le he
    | with_reducible apply leaf68_bd_smul
    | with_reducible apply leaf68_bd_neg
    | with_reducible apply leaf68_bd_sub
    | with_reducible apply leaf68_bd_add
    | with_reducible apply leaf68_bd_pow
    | with_reducible apply leaf68_bd_deriv
    | with_reducible apply leaf68_bd_mul
    | with_reducible apply leaf68_bd_C
    | omega

end LaterDeepFiveToSixRowOne68
end Max11DegreeRoutes
