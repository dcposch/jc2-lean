import LowScale68SecondaryFirstLoadWallCorePart07Scratch

/-! # Literal coefficient cores on the `(6,8)` wall `2g = n`

This module checks the invariant and homogeneous one-form coefficients, the
pure `l` Jacobian cores, and the load-free row-one coefficient on the first
loaded equality wall.  The remaining bridge is the core-plus-remainder split
for the full row-two and row-zero load polynomials.
-/

noncomputable section

namespace Max11DegreeRoutes

/-! ## Polynomial coefficient extraction on `2g = n`

The formulas below re-prove the mixed leading coefficients of §3.3 by the
same `coeff_mul_at_bounds68` / `coeff_derivative_at_bound68` style as the
tracked first-face extraction.  Derivative substitutions are the coefficient
identity `(p').coeff(u-1) = u * p.coeff u`, which holds for constant
coordinates as well (both sides vanish).  On this wall every displayed
bound is positive: `2g = n` and `0 < n` force `n ≥ 2`. -/

section FirstLoadWallExtraction68

open Polynomial

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

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


/-! ### Jacobian load cores, with the `A^5` cancellation checked by `ring` -/

set_option maxHeartbeats 2000000 in
theorem cubicHomogeneousRowZeroPolynomial68_coeff_loadWall
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicHomogeneousRowZeroPolynomial68 A B c D e).coeff (12 * n - 1) =
      (8 / 81 : k) * (n : k) * A.coeff (2 * n) *
        firstSecondaryZero68
          (A.coeff (2 * n)) (B.coeff (3 * n - g))
          (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
          (e.coeff (6 * n - g)) := by
  have hrem : (cubicRemainderRowZeroPolynomial68 A B c D e).natDegree <
      12 * n - 1 := by
    simp only [cubicRemainderRowZeroPolynomial68]
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
  rw [cubicHomogeneousRowZeroPolynomial68_eq_expanded,
    cubicHomogeneousRowZeroExpandedPolynomial68, coeff_add,
    coeff_eq_zero_of_natDegree_lt hrem, add_zero]
  exact firstSecondaryCoreRowZeroPolynomial68_coeff_loadWall A B c D e n g
    hn hg hwall hA hB hc hD he

/-! ### Load remainders versus the wall indices

Row one stays strictly load-free.  Rows two and zero meet the Jacobian
core, so only the non-core load is claimed to lie below the face. -/

set_option maxHeartbeats 3000000 in
theorem cubicLoadPolynomials68_degreeBounds_loadWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadSPolynomial68 l alpha beta delta A B c).natDegree ≤ 4 * n ∧
    (cubicLoadTPolynomial68 l alpha beta gamma epsilon A B c D).natDegree ≤
      5 * n - g ∧
    (cubicLoadUPolynomial68 l alpha beta gamma delta zeta
      A B c D e).natDegree ≤ 6 * n ∧
    (cubicLoadVPolynomial68 l alpha beta gamma delta epsilon eta
      A B c D e).natDegree ≤ 7 * n - g := by
  simp only [cubicLoadSPolynomial68, cubicLoadTPolynomial68,
    cubicLoadUPolynomial68, cubicLoadVPolynomial68]
  constructor
  · compute_degree
    omega
  constructor
  · compute_degree
    omega
  constructor <;> compute_degree <;> omega

end FirstLoadWallExtraction68
end Max11DegreeRoutes
