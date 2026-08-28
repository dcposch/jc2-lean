import HistoryDegree
import TotalDegreeRoutes
import CoprimeDegreeRoute
import EndpointGCDRoute
import LowScale46AlignedFinitePoles
import GCD369DivisibleSourceExclusion

/-! # Max-eleven handoff from the complete divisible `(6,9)` exclusion

This module adapts the literal polynomial source theorem to the normalized
`MvPolynomial` interface used by the max-eleven degree router.  It closes both
cube and noncube branches of the divisible common-core residue.  The local
large-source-shear proof also reduces the nondivisible residue to the
classical prime-total-degree-gcd theorem.  The final composition now reduces
the former gcd-at-most-two premise to the even common-leading-scale residue
at partial-degree gcd two.
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

/-- The checked large-source-shear calculation and Dirichlet argument reduce
the entire nondivisible `(6,9)` residue to the canonical classical theorem for
Keller pairs whose total-degree gcd is prime. -/
theorem imported_planeKeller69NondivisibleCoreRoute_of_primeTotalDegreeGCD
    {K : Type*} [Field K]
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K)) :
    PlaneKeller69NondivisibleCoreRoute (K := K) :=
  planeKeller69NondivisibleCoreRoute_of_exactTotalDegree_and_primeGCD
    planeKeller69SourceShearExactTotalDegree hprime

/-- Max-eleven generation after importing the complete divisible `(6,9)`
exclusion and proving every local step of the nondivisible source-shear route.
The only remaining inputs are the prime-total-degree-gcd theorem and the
classical gcd-at-most-two partial-degree route. -/
theorem Max11PlaneKellerGenerationWithPrimeTotalDegreeGCDRoute
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (hgcd : ∀ m n, Nat.gcd m n ≤ 2 →
      PlaneKellerAutomorphicAtDegrees (K := K) m n)
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K)) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      degreeOf 1 P ≤ 11 → degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  exact Max11PlaneKellerGenerationWithImportedDivisible69Exclusion hgcd
    (imported_planeKeller69NondivisibleCoreRoute_of_primeTotalDegreeGCD hprime)

/-- The complete imported `(6,9)` route, reduced only to the classical
prime-total-degree-gcd theorem. -/
theorem imported_planeKellerAutomorphicAtDegrees_69_of_primeTotalDegreeGCD
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K)) :
    PlaneKellerAutomorphicAtDegrees (K := K) 6 9 := by
  have hhistory : PlaneKeller69NondivisibleCoreRoute (K := K) :=
    imported_planeKeller69NondivisibleCoreRoute_of_primeTotalDegreeGCD hprime
  exact planeKellerAutomorphicAtDegrees_69_of_normalized_routes
    (planeKeller69CubeRoute_of_history_and_divisible_exclusion hhistory
      imported_planeKeller69DivisibleCubeExclusion)
    (planeKeller69NoncubeRoute_of_history_and_divisible_exclusion hhistory
      imported_planeKeller69DivisibleNoncubeExclusion)

/-- Max-11 with the former global gcd-two premise reduced to the five
unordered primitive leaves `(4,6)`, `(4,10)`, `(6,8)`, `(6,10)`, and
`(8,10)`. -/
theorem Max11PlaneKellerGenerationWithFiveGCDTwoLeaves
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K))
    (h46 : PlaneKellerAutomorphicAtDegrees (K := K) 4 6)
    (h410 : PlaneKellerAutomorphicAtDegrees (K := K) 4 10)
    (h68 : PlaneKellerAutomorphicAtDegrees (K := K) 6 8)
    (h610 : PlaneKellerAutomorphicAtDegrees (K := K) 6 10)
    (h810 : PlaneKellerAutomorphicAtDegrees (K := K) 8 10) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      degreeOf 1 P ≤ 11 → degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  have hcop : ∀ m n, m.Coprime n →
      PlaneKellerAutomorphicAtDegrees (K := K) m n := by
    intro m n hmn
    by_cases hmzero : m = 0
    · subst m
      exact Max11ClassicalRoutes.planeKellerAutomorphicAtDegrees_zero n
    by_cases hnzero : n = 0
    · subst n
      exact (Max11ClassicalRoutes.planeKellerAutomorphicAtDegrees_zero m).swap
    exact planeKellerAutomorphicAtDegrees_of_coprime_and_primeTotalDegreeGCD
      m n (Nat.pos_of_ne_zero hmzero) (Nat.pos_of_ne_zero hnzero) hmn hprime
  have hall := MaxPartialDegreeElevenClosureWithFiveGCDTwoLeaves
    (PlaneKellerAutomorphicAtDegrees (K := K))
    (fun _ _ h => h.swap)
    Max11ClassicalRoutes.planeKellerAutomorphicAtDegrees_zero hcop
    planeKellerAutomorphicAtDegrees_of_dvd
    planeKellerAutomorphicAtDegrees_equal
    h46 h410 h68 h610 h810
    (imported_planeKellerAutomorphicAtDegrees_69_of_primeTotalDegreeGCD hprime)
  intro P Q hPdegree hQdegree hKeller
  exact hall (degreeOf 1 P) (degreeOf 1 Q) hPdegree hQdegree
    P Q rfl rfl hKeller

/-- Source-honest Max-11 composition with the gcd-at-most-two premise reduced
to its exact gcd-two residue.  The prime theorem now proves every positive
coprime partial-degree pair internally. -/
theorem Max11PlaneKellerGenerationWithGCDTwoResidual
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (hgcdTwo : ∀ m n, Nat.gcd m n = 2 →
      PlaneKellerAutomorphicAtDegrees (K := K) m n)
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K)) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      degreeOf 1 P ≤ 11 → degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  exact Max11PlaneKellerGenerationWithPrimeTotalDegreeGCDRoute
    (planeKellerAutomorphicAtDegrees_of_gcd_le_two hgcdTwo hprime) hprime

/-- The narrowest checked Max-11 handoff: the classical prime-total-degree
route proves every coprime partial-degree pair and every gcd-two pair with
odd common leading-degree scale.  Only the even-scale gcd-two interface
remains as a nonclassical mathematical premise. -/
theorem Max11PlaneKellerGenerationWithEvenLeadingScaleGCDTwoRoute
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (heven : PlaneKellerEvenLeadingScaleGCDTwoRoute (K := K))
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K)) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      degreeOf 1 P ≤ 11 → degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  exact Max11PlaneKellerGenerationWithGCDTwoResidual
    (planeKellerAutomorphicAtDegrees_of_gcd_two_and_evenLeadingScale
      hprime heven) hprime

/-- The narrowest finite Max-11 handoff: only the even common-scale subcases
of the five primitive gcd-two degree pairs remain, together with the prime
total-degree theorem. -/
theorem Max11PlaneKellerGenerationWithFiveEvenScaleGCDTwoLeaves
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K))
    (h46 : PlaneKellerEvenLeadingScaleAtDegrees (K := K) 4 6)
    (h410 : PlaneKellerEvenLeadingScaleAtDegrees (K := K) 4 10)
    (h68 : PlaneKellerEvenLeadingScaleAtDegrees (K := K) 6 8)
    (h610 : PlaneKellerEvenLeadingScaleAtDegrees (K := K) 6 10)
    (h810 : PlaneKellerEvenLeadingScaleAtDegrees (K := K) 8 10) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      degreeOf 1 P ≤ 11 → degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  exact Max11PlaneKellerGenerationWithFiveGCDTwoLeaves hprime
    (planeKellerAutomorphicAtDegrees_of_gcd_two_and_evenLeadingScaleAtDegrees
      4 6 (by norm_num) (by norm_num) (by norm_num) hprime h46)
    (planeKellerAutomorphicAtDegrees_of_gcd_two_and_evenLeadingScaleAtDegrees
      4 10 (by norm_num) (by norm_num) (by norm_num) hprime h410)
    (planeKellerAutomorphicAtDegrees_of_gcd_two_and_evenLeadingScaleAtDegrees
      6 8 (by norm_num) (by norm_num) (by norm_num) hprime h68)
    (planeKellerAutomorphicAtDegrees_of_gcd_two_and_evenLeadingScaleAtDegrees
      6 10 (by norm_num) (by norm_num) (by norm_num) hprime h610)
    (planeKellerAutomorphicAtDegrees_of_gcd_two_and_evenLeadingScaleAtDegrees
      8 10 (by norm_num) (by norm_num) (by norm_num) hprime h810)

/-- The standard-pair endpoint obstruction eliminates every even common
leading scale above two.  Consequently Max-11 needs only the literal scales
`0` and `2` at each of the five gcd-two leaves, together with the classical
prime-total-degree route. -/
theorem Max11PlaneKellerGenerationWithStandardEndpointAndFiveLowScaleLeaves
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K))
    (hendpoint : PlaneKellerStandardEndpointGCDRoute (K := K))
    (h46 : PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 4 6)
    (h410 : PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 4 10)
    (h68 : PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 6 8)
    (h610 : PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 6 10)
    (h810 : PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 8 10) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      degreeOf 1 P ≤ 11 → degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  exact Max11PlaneKellerGenerationWithFiveEvenScaleGCDTwoLeaves hprime
    (planeKellerEvenLeadingScaleAtDegrees_of_standardEndpoint_and_lowScales
      4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hendpoint h46)
    (planeKellerEvenLeadingScaleAtDegrees_of_standardEndpoint_and_lowScales
      4 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hendpoint h410)
    (planeKellerEvenLeadingScaleAtDegrees_of_standardEndpoint_and_lowScales
      6 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hendpoint h68)
    (planeKellerEvenLeadingScaleAtDegrees_of_standardEndpoint_and_lowScales
      6 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hendpoint h610)
    (planeKellerEvenLeadingScaleAtDegrees_of_standardEndpoint_and_lowScales
      8 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hendpoint h810)

/-- The same narrow Max-11 handoff with the classical endpoint input stated
in its literal published form: every standard normalized right endpoint has
coordinate gcd strictly greater than two. -/
theorem Max11PlaneKellerGenerationWithStandardEndpointObstructionAndFiveLowScaleLeaves
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K))
    (hendpoint : PlaneKellerStandardEndpointGCDObstruction (K := K))
    (h46 : PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 4 6)
    (h410 : PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 4 10)
    (h68 : PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 6 8)
    (h610 : PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 6 10)
    (h810 : PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 8 10) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      degreeOf 1 P ≤ 11 → degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  exact Max11PlaneKellerGenerationWithStandardEndpointAndFiveLowScaleLeaves
    hprime (planeKellerStandardEndpointGCDRoute_of_obstruction hendpoint)
    h46 h410 h68 h610 h810

/-- The `(4,6)` low-scale leaf is normalized internally to a literal
square/cube common core of degree zero or two.  Four low-scale leaves remain
in their coefficient-degree form. -/
theorem Max11PlaneKellerGenerationWithNormalized46AndFourLowScaleLeaves
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K))
    (hendpoint : PlaneKellerStandardEndpointGCDObstruction (K := K))
    (h46 : PlaneKellerNormalized46LowScaleRoute (K := K))
    (h410 : PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 4 10)
    (h68 : PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 6 8)
    (h610 : PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 6 10)
    (h810 : PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 8 10) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      degreeOf 1 P ≤ 11 → degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  exact Max11PlaneKellerGenerationWithStandardEndpointObstructionAndFiveLowScaleLeaves
    hprime hendpoint
    (planeKellerLowEvenLeadingScalesAtDegrees_46_of_normalized h46)
    h410 h68 h610 h810

/-- The three leaves with consecutive reduced weights are normalized
internally to exact common powers.  Only `(4,10)` and `(6,10)`, whose reduced
weights are nonconsecutive, remain in coefficient-degree form. -/
theorem Max11PlaneKellerGenerationWithThreeNormalizedAndTwoLowScaleLeaves
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K))
    (hendpoint : PlaneKellerStandardEndpointGCDObstruction (K := K))
    (h46 : PlaneKellerNormalized46LowScaleRoute (K := K))
    (h410 : PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 4 10)
    (h68 : PlaneKellerNormalized68LowScaleRoute (K := K))
    (h610 : PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 6 10)
    (h810 : PlaneKellerNormalized810LowScaleRoute (K := K)) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      degreeOf 1 P ≤ 11 → degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  exact Max11PlaneKellerGenerationWithStandardEndpointObstructionAndFiveLowScaleLeaves
    hprime hendpoint
    (planeKellerLowEvenLeadingScalesAtDegrees_46_of_normalized h46)
    h410
    (planeKellerLowEvenLeadingScalesAtDegrees_68_of_normalized h68)
    h610
    (planeKellerLowEvenLeadingScalesAtDegrees_810_of_normalized h810)

/-- The narrow normalized Max-11 handoff: every primitive gcd-two leaf has
been reduced internally to exact common-core powers at scale zero or two. -/
theorem Max11PlaneKellerGenerationWithFiveNormalizedLowScaleRoutes
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K))
    (hendpoint : PlaneKellerStandardEndpointGCDObstruction (K := K))
    (h46 : PlaneKellerNormalized46LowScaleRoute (K := K))
    (h410 : PlaneKellerNormalized410LowScaleRoute (K := K))
    (h68 : PlaneKellerNormalized68LowScaleRoute (K := K))
    (h610 : PlaneKellerNormalized610LowScaleRoute (K := K))
    (h810 : PlaneKellerNormalized810LowScaleRoute (K := K)) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      degreeOf 1 P ≤ 11 → degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  exact Max11PlaneKellerGenerationWithStandardEndpointObstructionAndFiveLowScaleLeaves
    hprime hendpoint
    (planeKellerLowEvenLeadingScalesAtDegrees_46_of_normalized h46)
    (planeKellerLowEvenLeadingScalesAtDegrees_410_of_normalized h410)
    (planeKellerLowEvenLeadingScalesAtDegrees_68_of_normalized h68)
    (planeKellerLowEvenLeadingScalesAtDegrees_610_of_normalized h610)
    (planeKellerLowEvenLeadingScalesAtDegrees_810_of_normalized h810)

/-- Fully assembled Max-11 conditional on the classical prime-total-degree
result and the strong arbitrary-pair twice-prime interface.  The latter is
kept explicit because the published arbitrary-pair proof has a documented
gap; the 2017 theorem concerns only the globally minimal counterexample gcd. -/
theorem Max11PlaneKellerGenerationWithPrimeAndTwicePrimeTotalDegreeGCDRoutes
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K))
    (htwice : PlaneKellerTwicePrimeTotalDegreeGCDRoute (K := K)) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      degreeOf 1 P ≤ 11 → degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  exact Max11PlaneKellerGenerationWithEvenLeadingScaleGCDTwoRoute
    (planeKellerEvenLeadingScaleGCDTwoRoute_of_twicePrimeTotalDegreeGCD htwice)
    hprime

#print axioms normalized69Source_impossible_of_degree_dvd_three
#print axioms imported_planeKeller69DivisibleCubeExclusion
#print axioms imported_planeKeller69DivisibleNoncubeExclusion
#print axioms Max11PlaneKellerGenerationWithImportedDivisible69Exclusion
#print axioms imported_planeKeller69NondivisibleCoreRoute_of_primeTotalDegreeGCD
#print axioms Max11PlaneKellerGenerationWithPrimeTotalDegreeGCDRoute
#print axioms imported_planeKellerAutomorphicAtDegrees_69_of_primeTotalDegreeGCD
#print axioms Max11PlaneKellerGenerationWithFiveGCDTwoLeaves
#print axioms Max11PlaneKellerGenerationWithGCDTwoResidual
#print axioms Max11PlaneKellerGenerationWithEvenLeadingScaleGCDTwoRoute
#print axioms Max11PlaneKellerGenerationWithFiveEvenScaleGCDTwoLeaves
#print axioms Max11PlaneKellerGenerationWithStandardEndpointAndFiveLowScaleLeaves
#print axioms Max11PlaneKellerGenerationWithStandardEndpointObstructionAndFiveLowScaleLeaves
#print axioms Max11PlaneKellerGenerationWithNormalized46AndFourLowScaleLeaves
#print axioms Max11PlaneKellerGenerationWithThreeNormalizedAndTwoLowScaleLeaves
#print axioms Max11PlaneKellerGenerationWithFiveNormalizedLowScaleRoutes
#print axioms Max11PlaneKellerGenerationWithPrimeAndTwicePrimeTotalDegreeGCDRoutes

end Max11DegreeRoutes
