import LowScale68SecondaryResidualDoubleLoadWallPart04Scratch

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

set_option maxHeartbeats 3000000 in
theorem secondaryLoadInvariantFourLCorePolynomial68_coeff_wall
    (l : k) (A : k[X]) (n : ℕ) (hA : A.natDegree ≤ 2 * n) :
    (secondaryLoadInvariantFourLCorePolynomial68 l A).coeff (8 * n) =
      (35 / 1728 : k) * l * A.coeff (2 * n) ^ 4 := by
  have hA4 : (A ^ 4).coeff (8 * n) = A.coeff (2 * n) ^ 4 := by
    have h := coeff_pow_at_bound68 A (2 * n) 4 hA
    have hi : 4 * (2 * n) = 8 * n := by omega
    simpa only [hi] using h
  rw [secondaryLoadInvariantFourLCorePolynomial68, coeff_smul, hA4,
    smul_eq_mul]

set_option maxHeartbeats 4000000 in
theorem secondaryLoadInvariantFourRestPolynomial68_degree_lt_wall
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hg : 0 < g) (hwall : 3 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryLoadInvariantFourRestPolynomial68 l beta gamma delta epsilon
      zeta A B c D e).natDegree < 8 * n := by
  simp only [secondaryLoadInvariantFourRestPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 4000000 in
/-- Mixed I4 coefficient at the collided index `8n = 9n-3g`. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_residualDoubleLoadWall
    (l beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hg : 0 < g) (hwall : 3 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (8 * n) =
      residualDoubleLoadWallFourScalar68
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
        (e.coeff (6 * n - 2 * g)) l := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have htwo : 2 * g < n := residualDoubleLoadWall_twoGap n g hg hwall
  have hidx : 9 * n - 3 * g = 8 * n :=
    residualDoubleLoadWall_fourIndex n g hwall
  have hhom := secondaryResidualInvariantFourPolynomial68_coeff_double_of_twoGap
    B c d e n g hg htwo hB hc hd he
  have hcore := secondaryLoadInvariantFourLCorePolynomial68_coeff_wall
    l A n hA
  have hrest := secondaryLoadInvariantFourRestPolynomial68_degree_lt_wall
    l beta gamma delta epsilon zeta A B c D e n g hg hwall
    hA hB hc hD he
  rw [← hidx, cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantFourPolynomial68 B c d e by
      simpa only [D] using
        cubicFirstIntegralFourPolynomial68_residualCoordinates A B c d e,
    secondaryLoadInvariantFourPolynomial68_eq_core_add_rest,
    coeff_add, coeff_add, hhom, hidx, hcore,
    coeff_eq_zero_of_natDegree_lt hrest, add_zero]
  simp only [residualDoubleLoadWallFourScalar68]
  ring

end Max11DegreeRoutes
