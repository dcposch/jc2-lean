import Sol410ScaleTwoNonzeroSuppliedFinalContradictionScratch
import Sol410ScaleTwoRemainingSquareFacesScratch

/-!
# Source-facing exclusion of the nonzero square `(4,10)` face

This wrapper extracts the literal bivariate coefficients and Jacobian from
the normalized source, but keeps the caller's exact `h₀` and `lambda`.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

set_option linter.unusedSectionVars false

theorem planeKeller410_nonzeroSquareExclusion :
    PlaneKeller410NonzeroSquareExclusion (K := K) := by
  intro P Q H h0 lambda hsource hh0 hlambda hH hN
  dsimp only at hN
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  rcases hsource with
    ⟨_hHne, hHdegree, hPdegree, hQdegree, hp4, hq10, hKeller⟩
  have hp : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp4' : p.coeff 4 = H ^ 2 := by
    simpa only [p] using hp4
  have hq10' : q.coeff 10 = H ^ 5 := by
    simpa only [q] using hq10
  have hN' : (5 : K[X]) * p.coeff 3 * H ^ 3 -
      (2 : K[X]) * q.coeff 9 = Polynomial.C lambda * h0 ^ 9 := by
    simpa only [p, q] using hN
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  have hdegree : h0.natDegree = 1 := by
    have hdegree' := congrArg Polynomial.natDegree hH
    rw [hHdegree, Polynomial.natDegree_pow] at hdegree'
    omega
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdegree
  let a : K := -d / c
  have hroot : h0.eval a = 0 := by
    rw [← hlinear]
    simp only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    dsimp only [a]
    field_simp [hc]
    ring
  exact nonzeroFace410_linearRoot_suppliedFinalContradiction p q H h0
    j lambda a hp hq hh0 hdegree hH hp4' hq10' hN' hD hroot hlambda hj

#print axioms planeKeller410_nonzeroSquareExclusion

end Max11DegreeRoutes
