import Solution
import SolutionV2

/-! # Complete normalized common-cubic exclusion at `(6,9)`

The polynomial common core is either a cube or a noncube.  The two published
source-facing exclusions cover these cases and hence exhaust the normalized
common-cubic residue.
-/

open Polynomial

/-- A literal normalized `(6,9)` source with leading coefficients `H²,H³`,
nonzero constant Keller bracket, and `3 ∣ deg H` is impossible, without a
caller-supplied cube/noncube choice. -/
theorem GCD369PolynomialCommonCubicSourceExclusionV2
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (H : k[X]) (p q : k[X][X]) (j : k)
    (hdegreeDiv : 3 ∣ H.natDegree) (hj : j ≠ 0)
    (hp : p.natDegree = 6) (hq : q.natDegree = 9)
    (hp6 : p.coeff 6 = H ^ 2) (hq9 : q.coeff 9 = H ^ 3)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j)) : False := by
  by_cases hcube : ∃ s : k[X], H = s ^ 3
  · obtain ⟨s, rfl⟩ := hcube
    have hp0 : p ≠ 0 := by
      intro hp0
      rw [hp0, Polynomial.natDegree_zero] at hp
      omega
    have hp6ne : p.coeff 6 ≠ 0 := by
      rw [← hp, Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hp0
    have hs : s ≠ 0 := by
      intro hs
      apply hp6ne
      rw [hp6, hs]
      norm_num
    have hp6' : p.coeff 6 = s ^ 6 := by
      rw [hp6]
      ring
    have hq9' : q.coeff 9 = s ^ 9 := by
      rw [hq9]
      ring
    have hjac : GCD369CubeBivariateJacobian p q = C (C j) := by
      simpa only [GCD369CubeBivariateJacobian,
        GCD369CubeSourceXDeriv, GCD369SourceXDeriv] using hD
    exact GCD369PolynomialCubeSourceExclusionV2
      s p q j hs hj hp hq hp6' hq9' hjac
  · exact GCD369PolynomialNoncubeSourceExclusion
      H p q j hcube hdegreeDiv hj hp hq hp6 hq9 hD

#print axioms GCD369PolynomialCommonCubicSourceExclusionV2
