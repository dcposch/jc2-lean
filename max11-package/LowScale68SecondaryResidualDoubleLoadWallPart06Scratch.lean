import LowScale68SecondaryResidualDoubleLoadWallPart05Scratch

/-! # Mixed residual double face on the `(6,8)` wall `n = 3g`, `h = 2g`

On `n = 3g` the residual double face `9n-3g` collides with the Jacobian
load `l A^4` at degree `8n`.  Row two and row zero likewise meet the cores
`l A^5` and `l A^6` at `10n-1` and `12n-1`.  I3 and row one remain
load-free.  The five leading scalars force `l = b = c = 0`; residual
support `b ≠ 0 ∨ c ≠ 0` therefore excludes the wall.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Abstract mixed numerators -/

/-! ## Scalar identities -/

/-! ## Wall index arithmetic -/

/-! ## I4 load core versus remainder -/

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralThreePolynomial68_coeff_residualDoubleLoadWall
    (l beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hg : 0 < g) (hwall : 3 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicFirstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (9 * n) =
      (8 / 9 : k) * residualDoubleThreeHom68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
        (e.coeff (6 * n - 2 * g)) := by
  have htwo : 2 * g < n := residualDoubleLoadWall_twoGap n g hg hwall
  have hidx : 10 * n - 3 * g = 9 * n :=
    residualDoubleLoadWall_threeIndex n g hwall
  rw [← hidx, cubicFirstIntegralThreePolynomial68_coeff_residualDouble_of_twoGap
    l beta gamma delta epsilon zeta A B c d e n g hg htwo
    hA hB hc hd he]
  simp only [residualDoubleThreeHom68]
  ring

private theorem natDegree_mul_derivative_le_add_sub68
    (p q : k[X]) (u v : ℕ) (hv : 0 < v)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v) :
    (p * derivative q).natDegree ≤ u + v - 1 := by
  have hd : (derivative q).natDegree ≤ v - 1 :=
    (natDegree_derivative_le q).trans (Nat.sub_le_sub_right hq 1)
  have hsum : p.natDegree + (derivative q).natDegree ≤ u + (v - 1) :=
    Nat.add_le_add hp hd
  have hidx : u + (v - 1) = u + v - 1 := by omega
  exact natDegree_mul_le.trans (hidx ▸ hsum)

private theorem natDegree_mul_derivative_lt_of_add_sub68
    (p q : k[X]) (u v bound : ℕ) (hv : 0 < v)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (huv : u + v - 1 < bound) :
    (p * derivative q).natDegree < bound :=
  (natDegree_mul_derivative_le_add_sub68 p q u v hv hp hq).trans_lt huv

private theorem natDegree_smul_lt68 (r : k) {p : k[X]} {n : ℕ}
    (hp : p.natDegree < n) : (r • p).natDegree < n :=
  (natDegree_smul_le r p).trans_lt hp

private theorem natDegree_add_lt68 {p q : k[X]} {n : ℕ}
    (hp : p.natDegree < n) (hq : q.natDegree < n) :
    (p + q).natDegree < n :=
  (natDegree_add_le p q).trans_lt (max_lt hp hq)

private theorem natDegree_sub_lt68 {p q : k[X]} {n : ℕ}
    (hp : p.natDegree < n) (hq : q.natDegree < n) :
    (p - q).natDegree < n :=
  (natDegree_sub_le p q).trans_lt (max_lt hp hq)

set_option maxHeartbeats 2000000 in
theorem cubicLoadSRestPolynomial68_degree_le_wall
    (l alpha beta delta : k) (A B c : k[X]) (n g : ℕ)
    (hg : 0 < g) (hwall : 3 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (cubicLoadSRestPolynomial68 l alpha beta delta A B c).natDegree ≤
      4 * n - g := by
  simp only [cubicLoadSRestPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicLoadURestPolynomial68_degree_le_wall
    (l alpha beta gamma delta zeta : k) (A B c D e : k[X]) (n g : ℕ)
    (hg : 0 < g) (hwall : 3 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicLoadURestPolynomial68 l alpha beta gamma delta zeta
      A B c D e).natDegree ≤ 6 * n - g := by
  simp only [cubicLoadURestPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicERestPolynomial68_degree_le_wall
    (A c e : k[X]) (n g : ℕ)
    (hg : 0 < g) (hwall : 3 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hc : c.natDegree ≤ 4 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicERestPolynomial68 A c e).natDegree ≤ 6 * n - g := by
  simp only [cubicERestPolynomial68]
  compute_degree
  omega

end Max11DegreeRoutes
