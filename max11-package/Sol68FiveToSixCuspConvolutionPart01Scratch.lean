import Sol68FiveToSixCuspThirdJetScratch

/-! # Finite discriminant convolution at an arbitrary cusp depth

The exact first-integral combination from the third-jet file works at every
contracted depth.  Reflection turns its leading term `Delta*d` into an
ordinary coefficient convolution.  Since the edge coefficient of `d` is
nonzero, strong induction kills every `Delta` jet strictly before the first
load `mu = min(S, 7N-2G-S)`.  At `mu` the same convolution leaves exactly
the `d^2`, `zeta*A`, or simultaneous loaded scalar.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspConvolution68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- If every lower coefficient of the left factor vanishes, the coefficient
of a product is its new left coefficient times the constant right edge. -/
theorem mul_coeff_eq_left_edge_of_lower_zero68
    (p q : k[X]) (t : ℕ)
    (hzero : ∀ j, j < t → p.coeff j = 0) :
    (p * q).coeff t = p.coeff t * q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_eq_single t]
  · simp
  · intro j hj hne
    have hjt : j < t := by
      have := Finset.mem_range.mp hj
      omega
    rw [hzero j hjt, zero_mul]
  · intro ht
    exact (ht (Finset.mem_range.mpr (Nat.lt_succ_self t))).elim

/-- Reflected fixed-bound form of the same convolution. -/
theorem coeff_mul_at_reflect_of_left_lower_zero68
    (p q : k[X]) (u v t : ℕ)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (ht : t ≤ u + v)
    (hzero : ∀ j, j < t → (p.reflect u).coeff j = 0) :
    (p * q).coeff (u + v - t) =
      (p.reflect u).coeff t * (q.reflect v).coeff 0 := by
  have h := congrArg (fun r : k[X] => r.coeff t)
    (reflect_mul p q hp hq)
  rw [coeff_reflect, revAt_le ht,
    mul_coeff_eq_left_edge_of_lower_zero68 _ _ _ hzero] at h
  exact h

/-- Exact first-load residual after the complete homogeneous induction. -/
def FiveToSixCuspFirstLoadFactor68
    (zeta : k) (A B c d : k[X]) (N G S : ℕ) : Prop :=
  let R := 7 * N - 2 * G
  let mu := min S (R - S)
  let Delta := fiveToSixCuspDiscriminantPolynomial68 A B c
  let U := 8 * N - 2 * G
  let V := 5 * N - G - S
  let a := A.coeff (2 * N)
  let b := B.coeff (3 * N - G)
  let c0 := c.coeff (4 * N - G)
  let ds := d.coeff V
  (∀ q, q < mu → (Delta.reflect U).coeff q = 0) ∧
    ((S < R - S ∧ mu = S ∧
        (Delta.reflect U).coeff mu * ds -
          (3 / 2 : k) * b * ds ^ 2 = 0) ∨
      (R - S < S ∧ mu = R - S ∧
        (Delta.reflect U).coeff mu * ds +
          (9 / 8 : k) * zeta * a * c0 = 0) ∨
      (S = R - S ∧ mu = S ∧ mu = R - S ∧
        (Delta.reflect U).coeff mu * ds +
            (9 / 8 : k) * zeta * a * c0 -
          (3 / 2 : k) * b * ds ^ 2 = 0))

end FiveToSixCuspConvolution68
end Max11DegreeRoutes
