import LowScale68SecondaryOneFormsPart10Scratch

/-! # The last two `(6,8)` secondary one-form equations

The preceding extraction module handles both invariants and the first
one-form row.  This module performs the same load-free/load decomposition for
the remaining two rows and connects their literal polynomial coefficients to
`F1` and `F0` of `FirstSecondaryFace68`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SecondaryOneForms68

variable {k : Type*} [Field k] [CharZero k]

/-- Direct classified form of the literal first secondary face. -/
theorem integratedPolynomialLowerSystem_firstSecondaryClassified68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 c D E e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hsmall : 2 * g < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hE0 : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    e.coeff (6 * n - g) = 0 ∧
      A.coeff (2 * n) * B.coeff (3 * n - g) =
        3 * D.coeff (5 * n - g) := by
  exact firstSecondaryFace68_classify_of_two_mul_gap_lt_radius n g
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
    (e.coeff (6 * n - g)) ha hsmall
    (integratedPolynomialLowerSystem_firstSecondaryFace68
      l alpha beta gamma delta epsilon zeta eta terminal
      A B C0 c D E e n g hn hg hsmall hA hB hc hD he ha hC0 hE0 hsys)

end SecondaryOneForms68
end Max11DegreeRoutes
