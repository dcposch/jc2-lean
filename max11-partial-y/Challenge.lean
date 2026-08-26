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

end Max11DegreeRoutes

/-- At maximum degree twelve, the same routes leave exactly `(8,12)` and
`(9,12)` as the first new primitive unordered pairs. -/
theorem Max12FirstPrimitives (m : ℕ) (hm : m ≤ 12) :
    (¬ (m = 0 ∨ Nat.gcd m 12 ≤ 2 ∨ m = 12 ∨ (m < 12 ∧ m ∣ 12))) ↔
      m = 8 ∨ m = 9 := by
  sorry
