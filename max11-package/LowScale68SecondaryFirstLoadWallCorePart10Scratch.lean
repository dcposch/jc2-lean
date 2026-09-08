import LowScale68SecondaryFirstLoadWallCorePart09Scratch

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

/-! ### Jacobian load cores, with the `A^5` cancellation checked by `ring` -/

set_option maxHeartbeats 4000000 in
theorem integratedLowerRowOnePolynomial68_coeff_loadWall
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hwall : 2 * g = n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta A B
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
          (11 * n - 1) =
      (-8 / 81 : k) * firstSecondaryOne68 (n : k) (g : k)
        (A.coeff (2 * n)) (B.coeff (3 * n - g))
        (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
        (e.coeff (6 * n - g)) := by
  have hcoords := integratedPolynomial68_cubicCoordinates
    l alpha beta gamma delta epsilon zeta eta A B c D e
  rw [hcoords.t_eq, hcoords.u_eq, hcoords.v_eq, cubicRowOnePolynomial68_split,
    coeff_add, coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowOnePolynomial68_degree_lt_loadWall
        l alpha beta gamma delta epsilon zeta eta A B c D e n g
        hn hg hwall hA hB hc hD he), add_zero]
  exact cubicHomogeneousRowOnePolynomial68_coeff_loadWall A B c D e n g
    hn hg hwall hA hB hc hD he

/-! The remaining gap on this wall is to identify the *full* load polynomials
`cubicLoadRowTwoPolynomial68` and `cubicLoadRowZeroPolynomial68` with their
Jacobian cores plus a remainder of degree strictly below `10n-1` / `12n-1`.
That comparison does not cancel in `compute_degree`, and the algebraic split
into core-plus-rest is not yet a `ring` identity.  Until that split is
checked, the canonical `IntegratedPolynomialLowerSystem68` wrapper cannot
feed `FirstLoadWallFace68`. -/

end FirstLoadWallExtraction68
end Max11DegreeRoutes
