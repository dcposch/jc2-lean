import DegreeRoutes
import GCD369DivisibleSourceExclusion

/-! # Max-eleven handoff from the complete divisible `(6,9)` exclusion

This module adapts the literal polynomial source theorem to the normalized
`MvPolynomial` interface used by the max-eleven degree router.  It closes both
cube and noncube branches of the divisible common-core residue.  The final
composition remains conditional only on the classical gcd-at-most-two route
and the historical nondivisible-core route.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-- A normalized `(6,9)` Keller source whose common-core degree is divisible
by three is impossible. -/
theorem normalized69Source_impossible_of_degree_dvd_three
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {h : K[X]}
    (hsource : Normalized69Source P Q h)
    (hdiv : 3 ∣ h.natDegree) : False := by
  rcases hsource with ⟨_hh, hP, hQ, hp6, hq9, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hP
  have hq : q.natDegree = 9 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQ
  have hp6' : p.coeff 6 = h ^ 2 := by
    simpa only [p] using hp6
  have hq9' : q.coeff 9 = h ^ 3 := by
    simpa only [q] using hq9
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  exact GCD369PolynomialCommonCubicSourceExclusionV2
    h p q j hdiv hj hp hq hp6' hq9' hD

/-- The imported literal theorem supplies the divisible cube exclusion
required by the max-eleven router. -/
theorem imported_planeKeller69DivisibleCubeExclusion
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] :
    PlaneKeller69DivisibleCubeExclusion (K := K) := by
  intro P Q h hsource hdiv _hcube
  exact normalized69Source_impossible_of_degree_dvd_three hsource hdiv

/-- The same exhaustive theorem supplies the divisible noncube exclusion. -/
theorem imported_planeKeller69DivisibleNoncubeExclusion
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] :
    PlaneKeller69DivisibleNoncubeExclusion (K := K) := by
  intro P Q h hsource hdiv _hnoncube
  exact normalized69Source_impossible_of_degree_dvd_three hsource hdiv

/-- Max-eleven generation after discharging the entire divisible `(6,9)`
residue with the formalized cube/noncube source exclusions. -/
theorem Max11PlaneKellerGenerationWithImportedDivisible69Exclusion
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (hgcd : ∀ m n, Nat.gcd m n ≤ 2 →
      PlaneKellerAutomorphicAtDegrees (K := K) m n)
    (hhistory : PlaneKeller69NondivisibleCoreRoute (K := K)) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      degreeOf 1 P ≤ 11 → degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  exact Max11PlaneKellerGenerationWithHistoryAndDivisible69Exclusions
    hgcd hhistory imported_planeKeller69DivisibleCubeExclusion
      imported_planeKeller69DivisibleNoncubeExclusion

#print axioms normalized69Source_impossible_of_degree_dvd_three
#print axioms imported_planeKeller69DivisibleCubeExclusion
#print axioms imported_planeKeller69DivisibleNoncubeExclusion
#print axioms Max11PlaneKellerGenerationWithImportedDivisible69Exclusion

end Max11DegreeRoutes
