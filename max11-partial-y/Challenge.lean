/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch (direction), OpenAI Codex agent (formalization)
-/
import Mathlib

/-!
# Challenge: exact partial-degree closure through eleven

These declarations state the finite reduction certificate: the usual zero,
gcd-at-most-two, equal-degree, and divisibility routes leave only `(6,9)`
through maximum partial degree eleven, while maximum twelve first exposes
`(8,12)` and `(9,12)`.
-/

theorem Max11RouteClassification (m n : ℕ) (hmn : m ≤ n) (hn : n ≤ 11) :
    m = 0 ∨ Nat.gcd m n ≤ 2 ∨ m = n ∨ (m < n ∧ m ∣ n) ∨ (m = 6 ∧ n = 9) := by
  sorry

/-- Before the `(6,9)` theorem is supplied, `(6,9)` is the unique primitive
unordered pair through maximum degree eleven. -/
theorem Max11UniquePrimitive (m n : ℕ) (hmn : m ≤ n) (hn : n ≤ 11)
    (hzero : m ≠ 0) (hgcd : ¬ Nat.gcd m n ≤ 2) (hequal : m ≠ n)
    (hdiv : ¬ (m < n ∧ m ∣ n)) : m = 6 ∧ n = 9 := by
  sorry

/-- The five unordered gcd-two pairs through eleven which are neither equal
nor related by divisibility. -/
def Max11GCDTwoPrimitive (m n : ℕ) : Prop :=
  (m = 4 ∧ n = 6) ∨ (m = 4 ∧ n = 10) ∨
  (m = 6 ∧ n = 8) ∨ (m = 6 ∧ n = 10) ∨ (m = 8 ∧ n = 10)

/-- Replacing the broad gcd-at-most-two route by the coprime route leaves
exactly five gcd-two primitive pairs, in addition to `(6,9)`. -/
theorem Max11PrimeRouteClassification (m n : ℕ)
    (hmn : m ≤ n) (hn : n ≤ 11) :
    m = 0 ∨ m.Coprime n ∨ m = n ∨ (m < n ∧ m ∣ n) ∨
      Max11GCDTwoPrimitive m n ∨ (m = 6 ∧ n = 9) := by
  sorry

/-- Recursive closure through eleven using the coprime route and only the
five genuinely primitive gcd-two leaves. -/
theorem MaxPartialDegreeElevenClosureWithFiveGCDTwoLeaves
    (Good : ℕ → ℕ → Prop)
    (hsymm : ∀ m n, Good m n → Good n m)
    (hzero : ∀ n, Good 0 n)
    (hcop : ∀ m n, m.Coprime n → Good m n)
    (hdiv : ∀ m n, m < n → m ∣ n → (∀ r, r < n → Good m r) → Good m n)
    (hequal : ∀ n, (∀ r, r < n → Good r n) → Good n n)
    (h46 : Good 4 6) (h410 : Good 4 10) (h68 : Good 6 8)
    (h610 : Good 6 10) (h810 : Good 8 10) (h69 : Good 6 9) :
    ∀ m n, m ≤ 11 → n ≤ 11 → Good m n := by
  sorry

/-- Any symmetric degree property satisfying the four standard recursive
routes and the exceptional `(6,9)` leaf holds for every ordered pair through
maximum degree eleven. -/
theorem MaxPartialDegreeElevenClosure (Good : ℕ → ℕ → Prop)
    (hsymm : ∀ m n, Good m n → Good n m)
    (hzero : ∀ n, Good 0 n)
    (hgcd : ∀ m n, Nat.gcd m n ≤ 2 → Good m n)
    (hdiv : ∀ m n, m < n → m ∣ n → (∀ r, r < n → Good m r) → Good m n)
    (hequal : ∀ n, (∀ r, r < n → Good r n) → Good n n)
    (h69 : Good 6 9) :
    ∀ m n, m ≤ 11 → n ≤ 11 → Good m n := by
  sorry

/-- The Jacobian determinant of an ordered pair of bivariate polynomials,
with variables `0=x` and `1=y`. -/
noncomputable def PlaneJacobian {K : Type*} [CommRing K]
    (P Q : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.pderiv 0 P * MvPolynomial.pderiv 1 Q -
    MvPolynomial.pderiv 1 P * MvPolynomial.pderiv 0 Q

/-- A bivariate Keller pair has a nonzero constant Jacobian. -/
def IsPlaneKellerPair {K : Type*} [CommRing K]
    (P Q : MvPolynomial (Fin 2) K) : Prop :=
  ∃ j : K, j ≠ 0 ∧ PlaneJacobian P Q = MvPolynomial.C j

/-- The coordinate-ring formulation of polynomial invertibility:
`K[P,Q] = K[x,y]`. -/
def PlanePairGenerates {K : Type*} [CommRing K]
    (P Q : MvPolynomial (Fin 2) K) : Prop :=
  Algebra.adjoin K ({P, Q} : Set (MvPolynomial (Fin 2) K)) = ⊤

/-- The concrete degree predicate used by the maximum-eleven theorem. -/
def PlaneKellerAutomorphicAtDegrees {K : Type*} [Field K]
    (m n : ℕ) : Prop :=
  ∀ P Q : MvPolynomial (Fin 2) K,
    MvPolynomial.degreeOf 1 P = m →
    MvPolynomial.degreeOf 1 Q = n →
    IsPlaneKellerPair P Q → PlanePairGenerates P Q

/-- Concrete maximum-partial-`y`-degree-eleven composition, conditional on
the four standard degree routes and the exceptional `(6,9)` leaf. -/
theorem Max11PlaneKellerGeneration {K : Type*} [Field K]
    (hzero : ∀ n, PlaneKellerAutomorphicAtDegrees (K := K) 0 n)
    (hgcd : ∀ m n, Nat.gcd m n ≤ 2 →
      PlaneKellerAutomorphicAtDegrees (K := K) m n)
    (hdiv : ∀ m n, m < n → m ∣ n →
      (∀ r, r < n → PlaneKellerAutomorphicAtDegrees (K := K) m r) →
      PlaneKellerAutomorphicAtDegrees (K := K) m n)
    (hequal : ∀ n,
      (∀ r, r < n → PlaneKellerAutomorphicAtDegrees (K := K) r n) →
      PlaneKellerAutomorphicAtDegrees (K := K) n n)
    (h69 : PlaneKellerAutomorphicAtDegrees (K := K) 6 9) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      MvPolynomial.degreeOf 1 P ≤ 11 →
      MvPolynomial.degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  sorry

namespace Max11ClassicalRoutes

/-- Concrete maximum-eleven composition in characteristic zero with the
zero-partial-degree route proved internally. -/
theorem Max11PlaneKellerGenerationWithZeroRoute {K : Type*}
    [Field K] [CharZero K]
    (hgcd : ∀ m n, Nat.gcd m n ≤ 2 →
      PlaneKellerAutomorphicAtDegrees (K := K) m n)
    (hdiv : ∀ m n, m < n → m ∣ n →
      (∀ r, r < n → PlaneKellerAutomorphicAtDegrees (K := K) m r) →
      PlaneKellerAutomorphicAtDegrees (K := K) m n)
    (hequal : ∀ n,
      (∀ r, r < n → PlaneKellerAutomorphicAtDegrees (K := K) r n) →
      PlaneKellerAutomorphicAtDegrees (K := K) n n)
    (h69 : PlaneKellerAutomorphicAtDegrees (K := K) 6 9) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      MvPolynomial.degreeOf 1 P ≤ 11 →
      MvPolynomial.degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  sorry

end Max11ClassicalRoutes

namespace Max11DegreeRoutes

/-- Multiply one target coordinate by a constant. -/
noncomputable def targetRescale {K : Type*} [CommRing K] (u : K)
    (P : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C u * P

/-- The source-facing normalized form of a genuine partial-degree `(6,9)`
Keller pair. -/
def Normalized69Source {K : Type*} [Field K]
    (P Q : MvPolynomial (Fin 2) K) (h : Polynomial K) : Prop :=
  h ≠ 0 ∧
  MvPolynomial.degreeOf 1 P = 6 ∧
  MvPolynomial.degreeOf 1 Q = 9 ∧
  ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 6 = h ^ 2 ∧
  ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff 9 = h ^ 3 ∧
  IsPlaneKellerPair P Q

/-- The first source row available on the literal cube-core branch. -/
def Cube69FirstRowSource {K : Type*} [Field K]
    (P Q : MvPolynomial (Fin 2) K) (s : Polynomial K) : Prop :=
  s ≠ 0 ∧
  MvPolynomial.degreeOf 1 P = 6 ∧
  MvPolynomial.degreeOf 1 Q = 9 ∧
  ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 6 = s ^ 6 ∧
  ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff 9 = s ^ 9 ∧
  IsPlaneKellerPair P Q ∧
  let a := ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 5
  let b := ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff 8
  (3 : Polynomial K) * s ^ 4 * a.derivative -
      (15 : Polynomial K) * s ^ 3 * a * s.derivative -
    (2 : Polynomial K) * s * b.derivative +
      (16 : Polynomial K) * b * s.derivative = 0

/-- Closure of the normalized `(6,9)` cube-core branch. -/
def PlaneKeller69CubeRoute {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (h : Polynomial K),
    Normalized69Source P Q h →
    (∃ u : Polynomial K, h = u ^ 3) → PlanePairGenerates P Q

/-- Closure of the normalized `(6,9)` noncube-core branch. -/
def PlaneKeller69NoncubeRoute {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (h : Polynomial K),
    Normalized69Source P Q h →
    (¬ ∃ u : Polynomial K, h = u ^ 3) → PlanePairGenerates P Q

/-- Impossibility of every normalized cube-core `(6,9)` Keller source. -/
def PlaneKeller69CubeExclusion {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (h : Polynomial K),
    Normalized69Source P Q h → (∃ u : Polynomial K, h = u ^ 3) → False

/-- Impossibility of every normalized noncube-core `(6,9)` Keller source. -/
def PlaneKeller69NoncubeExclusion {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (h : Polynomial K),
    Normalized69Source P Q h → (¬ ∃ u : Polynomial K, h = u ^ 3) → False

/-- The reviewed history route for the part of the `(6,9)` leaf whose
common-core degree is not divisible by three. -/
def PlaneKeller69NondivisibleCoreRoute {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (h : Polynomial K),
    Normalized69Source P Q h → ¬ 3 ∣ h.natDegree → PlanePairGenerates P Q

/-- Closure of every Keller pair whose two total degrees have prime gcd. -/
def PlaneKellerPrimeTotalDegreeGCDRoute
    {K : Type*} [Field K] : Prop :=
  ∀ P Q : MvPolynomial (Fin 2) K,
    IsPlaneKellerPair P Q →
    (Nat.gcd P.totalDegree Q.totalDegree).Prime →
    PlanePairGenerates P Q

/-- Strong arbitrary-pair closure when the total-degree gcd is twice a
prime.  This is an explicit premise, not asserted here as a classical fact. -/
def PlaneKellerTwicePrimeTotalDegreeGCDRoute
    {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (p : ℕ),
    IsPlaneKellerPair P Q →
    p.Prime →
    Nat.gcd P.totalDegree Q.totalDegree = 2 * p →
    PlanePairGenerates P Q

/-- The residual partial-degree gcd-two route when the common numerical
scale of the two top coefficient degrees is even. -/
def PlaneKellerEvenLeadingScaleGCDTwoRoute
    {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (m n H : ℕ),
    MvPolynomial.degreeOf 1 P = m → MvPolynomial.degreeOf 1 Q = n →
    0 < m → 0 < n → Nat.gcd m n = 2 →
    IsPlaneKellerPair P Q →
    (((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff m).natDegree =
      (m / 2) * H →
    (((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff n).natDegree =
      (n / 2) * H →
    2 ∣ H → PlanePairGenerates P Q

/-- The even common-leading-scale residue localized to one fixed
partial-degree pair. -/
def PlaneKellerEvenLeadingScaleAtDegrees
    {K : Type*} [Field K] (m n : ℕ) : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (H : ℕ),
    MvPolynomial.degreeOf 1 P = m → MvPolynomial.degreeOf 1 Q = n →
    IsPlaneKellerPair P Q →
    (((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff m).natDegree =
      (m / 2) * H →
    (((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff n).natDegree =
      (n / 2) * H →
    2 ∣ H → PlanePairGenerates P Q

/-- The classical standard-pair endpoint obstruction, in a source-facing
form: normalized endpoint gcd at most two closes the pair. -/
def PlaneKellerStandardEndpointGCDRoute
    {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (a b S u v : ℕ),
    1 < a → 1 < b → a.Coprime b →
    IsPlaneKellerPair P Q →
    MvPolynomial.degreeOf 1 P = a * u →
    MvPolynomial.degreeOf 1 Q = b * u →
    (((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff (a * u)).natDegree =
      a * v →
    (((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff (b * u)).natDegree =
      b * v →
    P.totalDegree = a * S → Q.totalDegree = b * S →
    u < v → Nat.gcd u v ≤ 2 →
    PlanePairGenerates P Q

/-- The literal numerical conclusion of the classical standard-pair endpoint
theorem. -/
def PlaneKellerStandardEndpointGCDObstruction
    {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (a b S u v : ℕ),
    1 < a → 1 < b → a.Coprime b →
    IsPlaneKellerPair P Q →
    MvPolynomial.degreeOf 1 P = a * u →
    MvPolynomial.degreeOf 1 Q = b * u →
    (((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff (a * u)).natDegree =
      a * v →
    (((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff (b * u)).natDegree =
      b * v →
    P.totalDegree = a * S → Q.totalDegree = b * S →
    u < v → 2 < Nat.gcd u v

/-- One literal common leading-degree scale at a fixed partial-degree pair. -/
def PlaneKellerLeadingScaleAtDegrees
    {K : Type*} [Field K] (m n H : ℕ) : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K),
    MvPolynomial.degreeOf 1 P = m → MvPolynomial.degreeOf 1 Q = n →
    IsPlaneKellerPair P Q →
    (((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff m).natDegree =
      (m / 2) * H →
    (((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff n).natDegree =
      (n / 2) * H →
    PlanePairGenerates P Q

/-- The two low even scales not covered by the strict endpoint inequality. -/
def PlaneKellerLowEvenLeadingScalesAtDegrees
    {K : Type*} [Field K] (m n : ℕ) : Prop :=
  PlaneKellerLeadingScaleAtDegrees (K := K) m n 0 ∧
    PlaneKellerLeadingScaleAtDegrees (K := K) m n 2

/-- Exact normalized source data for the `(4,6)` low-scale leaf. -/
def Normalized46LeadingCoreSource {K : Type*} [Field K]
    (P Q : MvPolynomial (Fin 2) K) (h : Polynomial K) (H : ℕ) : Prop :=
  h ≠ 0 ∧ h.natDegree = H ∧
  MvPolynomial.degreeOf 1 P = 4 ∧ MvPolynomial.degreeOf 1 Q = 6 ∧
  ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 4 = h ^ 2 ∧
  ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff 6 = h ^ 3 ∧
  IsPlaneKellerPair P Q

/-- The normalized `(4,6)` route at common-core degree zero or two. -/
def PlaneKellerNormalized46LowScaleRoute
    {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (h : Polynomial K) (H : ℕ),
    (H = 0 ∨ H = 2) → Normalized46LeadingCoreSource P Q h H →
    PlanePairGenerates P Q

/-- The sole scale-two interface left after the scale-zero exclusion. -/
def PlaneKellerNormalized46ScaleTwoRoute
    {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (h : Polynomial K),
    Normalized46LeadingCoreSource P Q h 2 → PlanePairGenerates P Q

/-- The normalized `(4,6)` scale-two route is proved internally. -/
theorem proved_planeKellerNormalized46ScaleTwoRoute
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] :
    PlaneKellerNormalized46ScaleTwoRoute (K := K) := by
  sorry

/-- Both normalized low scales for `(4,6)` are proved internally. -/
theorem proved_planeKellerNormalized46LowScaleRoute
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] :
    PlaneKellerNormalized46LowScaleRoute (K := K) := by
  sorry

/-- Exact normalized source data for consecutive reduced leading weights. -/
def NormalizedConsecutiveLeadingCoreSource {K : Type*} [Field K]
    (r : ℕ) (P Q : MvPolynomial (Fin 2) K) (h : Polynomial K) (H : ℕ) : Prop :=
  h ≠ 0 ∧ h.natDegree = H ∧
  MvPolynomial.degreeOf 1 P = 2 * r ∧
  MvPolynomial.degreeOf 1 Q = 2 * (r + 1) ∧
  ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff (2 * r) = h ^ r ∧
  ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff (2 * (r + 1)) =
    h ^ (r + 1) ∧
  IsPlaneKellerPair P Q

/-- The normalized low-scale route for consecutive reduced weights. -/
def PlaneKellerNormalizedConsecutiveLowScaleRoute
    {K : Type*} [Field K] (r : ℕ) : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (h : Polynomial K) (H : ℕ),
    (H = 0 ∨ H = 2) → NormalizedConsecutiveLeadingCoreSource r P Q h H →
    PlanePairGenerates P Q

/-- Normalized `(6,8)` source data. -/
abbrev Normalized68LeadingCoreSource {K : Type*} [Field K]
    (P Q : MvPolynomial (Fin 2) K) (h : Polynomial K) (H : ℕ) : Prop :=
  NormalizedConsecutiveLeadingCoreSource 3 P Q h H

/-- The normalized `(6,8)` low-scale route. -/
abbrev PlaneKellerNormalized68LowScaleRoute
    {K : Type*} [Field K] : Prop :=
  PlaneKellerNormalizedConsecutiveLowScaleRoute (K := K) 3

/-- Normalized `(8,10)` source data. -/
abbrev Normalized810LeadingCoreSource {K : Type*} [Field K]
    (P Q : MvPolynomial (Fin 2) K) (h : Polynomial K) (H : ℕ) : Prop :=
  NormalizedConsecutiveLeadingCoreSource 4 P Q h H

/-- The normalized `(8,10)` low-scale route. -/
abbrev PlaneKellerNormalized810LowScaleRoute
    {K : Type*} [Field K] : Prop :=
  PlaneKellerNormalizedConsecutiveLowScaleRoute (K := K) 4

/-- Exact normalized source data for arbitrary reduced leading weights. -/
def NormalizedCoprimeLeadingCoreSource {K : Type*} [Field K]
    (r s : ℕ) (P Q : MvPolynomial (Fin 2) K) (h : Polynomial K) (H : ℕ) : Prop :=
  h ≠ 0 ∧ h.natDegree = H ∧
  MvPolynomial.degreeOf 1 P = 2 * r ∧
  MvPolynomial.degreeOf 1 Q = 2 * s ∧
  ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff (2 * r) = h ^ r ∧
  ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff (2 * s) = h ^ s ∧
  IsPlaneKellerPair P Q

/-- The normalized low-scale route for reduced weights `(r,s)`. -/
def PlaneKellerNormalizedCoprimeLowScaleRoute
    {K : Type*} [Field K] (r s : ℕ) : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (h : Polynomial K) (H : ℕ),
    (H = 0 ∨ H = 2) → NormalizedCoprimeLeadingCoreSource r s P Q h H →
    PlanePairGenerates P Q

/-- Normalized `(4,10)` source data and low-scale route. -/
abbrev Normalized410LeadingCoreSource {K : Type*} [Field K]
    (P Q : MvPolynomial (Fin 2) K) (h : Polynomial K) (H : ℕ) : Prop :=
  NormalizedCoprimeLeadingCoreSource 2 5 P Q h H

abbrev PlaneKellerNormalized410LowScaleRoute
    {K : Type*} [Field K] : Prop :=
  PlaneKellerNormalizedCoprimeLowScaleRoute (K := K) 2 5

/-- Normalized `(6,10)` source data and low-scale route. -/
abbrev Normalized610LeadingCoreSource {K : Type*} [Field K]
    (P Q : MvPolynomial (Fin 2) K) (h : Polynomial K) (H : ℕ) : Prop :=
  NormalizedCoprimeLeadingCoreSource 3 5 P Q h H

abbrev PlaneKellerNormalized610LowScaleRoute
    {K : Type*} [Field K] : Prop :=
  PlaneKellerNormalizedCoprimeLowScaleRoute (K := K) 3 5

/-- Impossibility of the cube-core part of the historical
`(6,9), 3 ∣ deg h` residue. -/
def PlaneKeller69DivisibleCubeExclusion {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (h : Polynomial K),
    Normalized69Source P Q h → 3 ∣ h.natDegree →
      (∃ u : Polynomial K, h = u ^ 3) → False

/-- Impossibility of the noncube-core part of the historical
`(6,9), 3 ∣ deg h` residue. -/
def PlaneKeller69DivisibleNoncubeExclusion {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (h : Polynomial K),
    Normalized69Source P Q h → 3 ∣ h.natDegree →
      (¬ ∃ u : Polynomial K, h = u ^ 3) → False

/-- A genuine `(6,9)` Keller pair has square/cube leading coefficients with
one nonzero common polynomial core. -/
theorem planeKellerPair_69_commonCore {K : Type*}
    [Field K] [CharZero K] {P Q : MvPolynomial (Fin 2) K}
    (hP : MvPolynomial.degreeOf 1 P = 6)
    (hQ : MvPolynomial.degreeOf 1 Q = 9)
    (hKeller : IsPlaneKellerPair P Q) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (alpha beta : K) (h : Polynomial K),
      alpha ≠ 0 ∧ beta ≠ 0 ∧ h ≠ 0 ∧
        p.coeff 6 = Polynomial.C alpha * h ^ 2 ∧
        q.coeff 9 = Polynomial.C beta * h ^ 3 := by
  sorry

/-- If the first two coefficient rows of a genuine `(6,9)` pair are written
in cube-root weights `(6,5;9,8)`, the alignment discriminator `3A-2B` is a
constant polynomial. -/
theorem planeKellerPair_69_alignmentDiscriminator_constant {K : Type*}
    [Field K] [CharZero K] {P Q : MvPolynomial (Fin 2) K}
    {s A B : Polynomial K}
    (hP : MvPolynomial.degreeOf 1 P = 6)
    (hQ : MvPolynomial.degreeOf 1 Q = 9)
    (hKeller : IsPlaneKellerPair P Q)
    (hs : s ≠ 0)
    (hp6 : ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 6 = s ^ 6)
    (hq9 : ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff 9 = s ^ 9)
    (hp5 : ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 5 = s ^ 5 * A)
    (hq8 : ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff 8 = s ^ 8 * B) :
    ∃ c : K, (3 : Polynomial K) * A - (2 : Polynomial K) * B =
      Polynomial.C c := by
  sorry

/-- The denominator-cleared first alignment row for a genuine cube-core
`(6,9)` pair; no divisibility of the next coefficients is assumed. -/
theorem planeKellerPair_69_cubeDiscriminatorNumerator_eq_zero {K : Type*}
    [Field K] [CharZero K] {P Q : MvPolynomial (Fin 2) K}
    {s : Polynomial K}
    (hP : MvPolynomial.degreeOf 1 P = 6)
    (hQ : MvPolynomial.degreeOf 1 Q = 9)
    (hKeller : IsPlaneKellerPair P Q) (hs : s ≠ 0)
    (hp6 : ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 6 = s ^ 6)
    (hq9 : ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff 9 = s ^ 9) :
    let a := ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 5
    let b := ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff 8
    (3 : Polynomial K) * s ^ 4 * a.derivative -
        (15 : Polynomial K) * s ^ 3 * a * s.derivative -
      (2 : Polynomial K) * s * b.derivative +
        (16 : Polynomial K) * b * s.derivative = 0 := by
  sorry

/-- A genuine `(6,9)` Keller pair can be normalized so that its leading
coefficients are a literal square and cube of one nonzero polynomial, without
changing either the Keller property or coordinate generation. -/
theorem planeKellerPair_69_normalize {K : Type*}
    [Field K] [CharZero K] {P Q : MvPolynomial (Fin 2) K}
    (hP : MvPolynomial.degreeOf 1 P = 6)
    (hQ : MvPolynomial.degreeOf 1 Q = 9)
    (hKeller : IsPlaneKellerPair P Q) :
    ∃ (alpha beta : K) (h : Polynomial K),
      alpha ≠ 0 ∧ beta ≠ 0 ∧ h ≠ 0 ∧
      MvPolynomial.degreeOf 1 (targetRescale alpha⁻¹ P) = 6 ∧
      MvPolynomial.degreeOf 1 (targetRescale beta⁻¹ Q) = 9 ∧
      ((Polynomial.Bivariate.equivMvPolynomial K).symm
          (targetRescale alpha⁻¹ P)).coeff 6 = h ^ 2 ∧
      ((Polynomial.Bivariate.equivMvPolynomial K).symm
          (targetRescale beta⁻¹ Q)).coeff 9 = h ^ 3 ∧
      IsPlaneKellerPair (targetRescale alpha⁻¹ P)
        (targetRescale beta⁻¹ Q) ∧
      (PlanePairGenerates (targetRescale alpha⁻¹ P)
          (targetRescale beta⁻¹ Q) ↔ PlanePairGenerates P Q) := by
  sorry

/-- Every genuine `(6,9)` Keller pair normalizes into an exhaustive source
dichotomy: either a literal cube core satisfying its first denominator-cleared
row, or a noncube normalized core. -/
theorem planeKellerPair_69_sourceDichotomy {K : Type*}
    [Field K] [CharZero K] {P Q : MvPolynomial (Fin 2) K}
    (hP : MvPolynomial.degreeOf 1 P = 6)
    (hQ : MvPolynomial.degreeOf 1 Q = 9)
    (hKeller : IsPlaneKellerPair P Q) :
    ∃ (P0 Q0 : MvPolynomial (Fin 2) K) (h : Polynomial K),
      Normalized69Source P0 Q0 h ∧
      (PlanePairGenerates P0 Q0 ↔ PlanePairGenerates P Q) ∧
      ((∃ s : Polynomial K, h = s ^ 3 ∧ Cube69FirstRowSource P0 Q0 s) ∨
        ¬ ∃ s : Polynomial K, h = s ^ 3) := by
  sorry

/-- The two exhaustive normalized core branches imply the global genuine
partial-degree `(6,9)` Keller leaf. -/
theorem planeKellerAutomorphicAtDegrees_69_of_normalized_routes
    {K : Type*} [Field K] [CharZero K]
    (hcube : PlaneKeller69CubeRoute (K := K))
    (hnoncube : PlaneKeller69NoncubeRoute (K := K)) :
    PlaneKellerAutomorphicAtDegrees (K := K) 6 9 := by
  sorry

/-- Exclusion of the normalized cube branch implies its generation route. -/
theorem planeKeller69CubeRoute_of_exclusion {K : Type*} [Field K]
    (h : PlaneKeller69CubeExclusion (K := K)) :
    PlaneKeller69CubeRoute (K := K) := by
  sorry

/-- Exclusion of the normalized noncube branch implies its generation route. -/
theorem planeKeller69NoncubeRoute_of_exclusion {K : Type*} [Field K]
    (h : PlaneKeller69NoncubeExclusion (K := K)) :
    PlaneKeller69NoncubeRoute (K := K) := by
  sorry

/-- The history route and the divisible cube exclusion together close the
whole normalized cube branch. -/
theorem planeKeller69CubeRoute_of_history_and_divisible_exclusion
    {K : Type*} [Field K]
    (hhistory : PlaneKeller69NondivisibleCoreRoute (K := K))
    (hdivisible : PlaneKeller69DivisibleCubeExclusion (K := K)) :
    PlaneKeller69CubeRoute (K := K) := by
  sorry

/-- The history route and the divisible noncube exclusion together close the
whole normalized noncube branch. -/
theorem planeKeller69NoncubeRoute_of_history_and_divisible_exclusion
    {K : Type*} [Field K]
    (hhistory : PlaneKeller69NondivisibleCoreRoute (K := K))
    (hdivisible : PlaneKeller69DivisibleNoncubeExclusion (K := K)) :
    PlaneKeller69NoncubeRoute (K := K) := by
  sorry

/-- Concrete maximum-eleven composition in characteristic zero with the
zero, equal-degree, and divisibility routes proved internally. -/
theorem Max11PlaneKellerGenerationWithElementaryRoutes {K : Type*}
    [Field K] [CharZero K]
    (hgcd : ∀ m n, Nat.gcd m n ≤ 2 →
      PlaneKellerAutomorphicAtDegrees (K := K) m n)
    (h69 : PlaneKellerAutomorphicAtDegrees (K := K) 6 9) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      MvPolynomial.degreeOf 1 P ≤ 11 →
      MvPolynomial.degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  sorry

/-- Maximum-eleven composition with the exceptional leaf split into its
source-facing normalized cube and noncube branches. -/
theorem Max11PlaneKellerGenerationWithNormalized69Routes {K : Type*}
    [Field K] [CharZero K]
    (hgcd : ∀ m n, Nat.gcd m n ≤ 2 →
      PlaneKellerAutomorphicAtDegrees (K := K) m n)
    (hcube : PlaneKeller69CubeRoute (K := K))
    (hnoncube : PlaneKeller69NoncubeRoute (K := K)) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      MvPolynomial.degreeOf 1 P ≤ 11 →
      MvPolynomial.degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  sorry

/-- Maximum-eleven composition stated in the exclusion form supplied by the
cube and noncube trajectory projects. -/
theorem Max11PlaneKellerGenerationWithNormalized69Exclusions {K : Type*}
    [Field K] [CharZero K]
    (hgcd : ∀ m n, Nat.gcd m n ≤ 2 →
      PlaneKellerAutomorphicAtDegrees (K := K) m n)
    (hcube : PlaneKeller69CubeExclusion (K := K))
    (hnoncube : PlaneKeller69NoncubeExclusion (K := K)) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      MvPolynomial.degreeOf 1 P ≤ 11 →
      MvPolynomial.degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  sorry

/-- Source-honest maximum-eleven composition using exactly the historical
split at `(6,9)`: the nondivisible common-core route and the cube/noncube
exclusions on the divisible residue. -/
theorem Max11PlaneKellerGenerationWithHistoryAndDivisible69Exclusions
    {K : Type*} [Field K] [CharZero K]
    (hgcd : ∀ m n, Nat.gcd m n ≤ 2 →
      PlaneKellerAutomorphicAtDegrees (K := K) m n)
    (hhistory : PlaneKeller69NondivisibleCoreRoute (K := K))
    (hcube : PlaneKeller69DivisibleCubeExclusion (K := K))
    (hnoncube : PlaneKeller69DivisibleNoncubeExclusion (K := K)) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      MvPolynomial.degreeOf 1 P ≤ 11 →
      MvPolynomial.degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  sorry

/-- Every positive coprime partial-degree pair follows from the prime
total-degree-gcd route via a large source shear. -/
theorem planeKellerAutomorphicAtDegrees_of_coprime_and_primeTotalDegreeGCD
    {K : Type*} [Field K] [CharZero K]
    (m n : ℕ) (hmpos : 0 < m) (hnpos : 0 < n)
    (hcop : m.Coprime n)
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K)) :
    PlaneKellerAutomorphicAtDegrees (K := K) m n := by
  sorry

/-- At partial-degree gcd two, the prime route closes every odd common-scale
case, leaving only the even-scale interface. -/
theorem planeKellerAutomorphicAtDegrees_of_gcd_two_and_evenLeadingScale
    {K : Type*} [Field K] [CharZero K]
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K))
    (heven : PlaneKellerEvenLeadingScaleGCDTwoRoute (K := K)) :
    ∀ m n, Nat.gcd m n = 2 →
      PlaneKellerAutomorphicAtDegrees (K := K) m n := by
  sorry

/-- Maximum eleven from the prime total-degree route and only the even-scale
partial-degree gcd-two residue. -/
theorem Max11PlaneKellerGenerationWithEvenLeadingScaleGCDTwoRoute
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (heven : PlaneKellerEvenLeadingScaleGCDTwoRoute (K := K))
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K)) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      MvPolynomial.degreeOf 1 P ≤ 11 →
      MvPolynomial.degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  sorry

/-- Maximum eleven with the remaining gcd-two work localized to the five
primitive degree pairs. -/
theorem Max11PlaneKellerGenerationWithFiveEvenScaleGCDTwoLeaves
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K))
    (h46 : PlaneKellerEvenLeadingScaleAtDegrees (K := K) 4 6)
    (h410 : PlaneKellerEvenLeadingScaleAtDegrees (K := K) 4 10)
    (h68 : PlaneKellerEvenLeadingScaleAtDegrees (K := K) 6 8)
    (h610 : PlaneKellerEvenLeadingScaleAtDegrees (K := K) 6 10)
    (h810 : PlaneKellerEvenLeadingScaleAtDegrees (K := K) 8 10) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      MvPolynomial.degreeOf 1 P ≤ 11 →
      MvPolynomial.degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  sorry

/-- Maximum eleven after the standard-endpoint theorem reduces each of the
five gcd-two leaves to the literal common scales zero and two. -/
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
      MvPolynomial.degreeOf 1 P ≤ 11 →
      MvPolynomial.degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  sorry

/-- Max-11 from the literal numerical standard-endpoint obstruction and the
ten remaining low-scale leaves. -/
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
      MvPolynomial.degreeOf 1 P ≤ 11 →
      MvPolynomial.degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  sorry

/-- Max-11 after normalizing the `(4,6)` low-scale leaf to its literal
square/cube common-core source. -/
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
      MvPolynomial.degreeOf 1 P ≤ 11 →
      MvPolynomial.degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  sorry

/-- Max-11 after the complete normalized `(4,6)` low-scale exclusion. -/
theorem Max11PlaneKellerGenerationWithFourLowScaleLeaves
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K))
    (hendpoint : PlaneKellerStandardEndpointGCDObstruction (K := K))
    (h410 : PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 4 10)
    (h68 : PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 6 8)
    (h610 : PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 6 10)
    (h810 : PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 8 10) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      MvPolynomial.degreeOf 1 P ≤ 11 →
      MvPolynomial.degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  sorry

/-- Max-11 after normalizing the three leaves with consecutive reduced
weights; only `(4,10)` and `(6,10)` remain in coefficient-degree form. -/
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
      MvPolynomial.degreeOf 1 P ≤ 11 →
      MvPolynomial.degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  sorry

/-- Max-11 after normalizing all five primitive gcd-two leaves to exact
common-core sources at scale zero or two. -/
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
      MvPolynomial.degreeOf 1 P ≤ 11 →
      MvPolynomial.degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  sorry

/-- Maximum eleven conditional on the prime and strong arbitrary-pair
twice-prime total-degree routes. -/
theorem Max11PlaneKellerGenerationWithPrimeAndTwicePrimeTotalDegreeGCDRoutes
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (hprime : PlaneKellerPrimeTotalDegreeGCDRoute (K := K))
    (htwice : PlaneKellerTwicePrimeTotalDegreeGCDRoute (K := K)) :
    ∀ P Q : MvPolynomial (Fin 2) K,
      MvPolynomial.degreeOf 1 P ≤ 11 →
      MvPolynomial.degreeOf 1 Q ≤ 11 →
      IsPlaneKellerPair P Q → PlanePairGenerates P Q := by
  sorry

end Max11DegreeRoutes

/-- At maximum degree twelve, the same routes leave exactly `(8,12)` and
`(9,12)` as the first new primitive unordered pairs. -/
theorem Max12FirstPrimitives (m : ℕ) (hm : m ≤ 12) :
    (¬ (m = 0 ∨ Nat.gcd m 12 ≤ 2 ∨ m = 12 ∨ (m < 12 ∧ m ∣ 12))) ↔
      m = 8 ∨ m = 9 := by
  sorry
