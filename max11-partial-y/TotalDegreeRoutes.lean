import HistoryRoute

/-! # Canonical total-degree gcd routes

This module relates the specialized `(2p,3p)` interface used by the
nondivisible `(6,9)` history argument to canonical statements phrased only
in terms of the gcd of the two total degrees.
-/

noncomputable section

open MvPolynomial

namespace Max11DegreeRoutes

/-- The classical plane Keller result for pairs whose total-degree gcd is
prime, in its coordinate-free total-degree form. -/
def PlaneKellerPrimeTotalDegreeGCDRoute
    {K : Type*} [Field K] : Prop :=
  ∀ P Q : MvPolynomial (Fin 2) K,
    IsPlaneKellerPair P Q →
    (Nat.gcd P.totalDegree Q.totalDegree).Prime →
    PlanePairGenerates P Q

/-- The strong per-pair interface for Keller pairs whose total-degree gcd is
twice a prime.  The prime is retained explicitly so downstream reductions do
not have to extract it from a divisibility statement.  This definition is an
interface only: the 2017 GGV theorem proves the corresponding restriction for
the globally minimal counterexample gcd `B`, while its cited arbitrary-pair
predecessor has a documented proof gap, so neither is imported here as a proof
of this stronger statement. -/
def PlaneKellerTwicePrimeTotalDegreeGCDRoute
    {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (p : ℕ),
    IsPlaneKellerPair P Q →
    p.Prime →
    Nat.gcd P.totalDegree Q.totalDegree = 2 * p →
    PlanePairGenerates P Q

/-- The elementary gcd calculation behind the passage from total degrees
`(2p,3p)` to the canonical prime-gcd route. -/
theorem gcd_two_mul_three_mul (p : ℕ) :
    Nat.gcd (2 * p) (3 * p) = p := by
  simp [Nat.gcd_mul_right]

/-- A canonical prime-total-degree-gcd theorem supplies the specialized
`(2p,3p)` theorem required by the history route. -/
theorem planeKeller23PrimeTotalDegreeRoute_of_primeTotalDegreeGCD
    {K : Type*} [Field K]
    (hroute : PlaneKellerPrimeTotalDegreeGCDRoute (K := K)) :
    PlaneKeller23PrimeTotalDegreeRoute (K := K) := by
  intro P Q p hKeller hp hPdegree hQdegree
  apply hroute P Q hKeller
  rw [hPdegree, hQdegree, gcd_two_mul_three_mul]
  exact hp

/-- The nondivisible normalized `(6,9)` route follows from the explicit
source-shear degree calculation and the canonical prime-gcd theorem. -/
theorem planeKeller69NondivisibleCoreRoute_of_exactTotalDegree_and_primeGCD
    {K : Type*} [Field K]
    (hdegree : PlaneKeller69SourceShearExactTotalDegreeRoute (K := K))
    (hprimeGCD : PlaneKellerPrimeTotalDegreeGCDRoute (K := K)) :
    PlaneKeller69NondivisibleCoreRoute (K := K) :=
  planeKeller69NondivisibleCoreRoute_of_totalDegree23Prime hdegree
    (planeKeller23PrimeTotalDegreeRoute_of_primeTotalDegreeGCD hprimeGCD)

end Max11DegreeRoutes
