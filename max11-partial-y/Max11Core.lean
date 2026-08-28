/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch (direction), OpenAI Codex agent (formalization)
-/
import Mathlib

/-!
# Exact partial-degree closure through eleven

This module kernel-checks the finite degree-routing composition used after the
partial-degree `(6,9)` leaf is closed.
-/

/-- Through maximum degree eleven, the only ordered primitive after the
zero, gcd-at-most-two, equal-degree, and divisibility routes is `(6,9)`. -/
theorem Max11RouteClassification (m n : ℕ) (hmn : m ≤ n) (hn : n ≤ 11) :
    m = 0 ∨ Nat.gcd m n ≤ 2 ∨ m = n ∨ (m < n ∧ m ∣ n) ∨ (m = 6 ∧ n = 9) := by
  have hm : m ≤ 11 := hmn.trans hn
  interval_cases m <;> interval_cases n <;> norm_num at *

/-- Before the `(6,9)` theorem is supplied, `(6,9)` is the unique primitive
unordered pair through maximum degree eleven. -/
theorem Max11UniquePrimitive (m n : ℕ) (hmn : m ≤ n) (hn : n ≤ 11)
    (hzero : m ≠ 0) (hgcd : ¬ Nat.gcd m n ≤ 2) (hequal : m ≠ n)
    (hdiv : ¬ (m < n ∧ m ∣ n)) : m = 6 ∧ n = 9 := by
  rcases Max11RouteClassification m n hmn hn with h | h | h | h | h
  · exact False.elim (hzero h)
  · exact False.elim (hgcd h)
  · exact False.elim (hequal h)
  · exact False.elim (hdiv h)
  · exact h

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
  have hm : m ≤ 11 := hmn.trans hn
  interval_cases m <;> interval_cases n <;> norm_num [Max11GCDTwoPrimitive] at *

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
  intro m n hm hn
  generalize ht : m + n = t
  induction t using Nat.strong_induction_on generalizing m n with
  | h t ih =>
      by_cases hmn : m ≤ n
      · rcases Max11PrimeRouteClassification m n hmn hn with
          hzero' | hcop' | heq' | hdiv' | htwo | hspecial
        · subst m
          exact hzero n
        · exact hcop m n hcop'
        · subst n
          apply hequal m
          intro r hr
          exact ih (r + m) (by omega) r m (by omega) hm rfl
        · apply hdiv m n hdiv'.1 hdiv'.2
          intro r hr
          exact ih (m + r) (by omega) m r hm (by omega) rfl
        · rcases htwo with htwo | htwo | htwo | htwo | htwo
          · rcases htwo with ⟨rfl, rfl⟩; exact h46
          · rcases htwo with ⟨rfl, rfl⟩; exact h410
          · rcases htwo with ⟨rfl, rfl⟩; exact h68
          · rcases htwo with ⟨rfl, rfl⟩; exact h610
          · rcases htwo with ⟨rfl, rfl⟩; exact h810
        · rcases hspecial with ⟨rfl, rfl⟩
          exact h69
      · have hnm : n ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmn)
        apply hsymm n m
        rcases Max11PrimeRouteClassification n m hnm hm with
          hzero' | hcop' | heq' | hdiv' | htwo | hspecial
        · subst n
          exact hzero m
        · exact hcop n m hcop'
        · exact False.elim (hmn (heq' ▸ le_rfl))
        · apply hdiv n m hdiv'.1 hdiv'.2
          intro r hr
          exact ih (n + r) (by omega) n r hn (by omega) rfl
        · rcases htwo with htwo | htwo | htwo | htwo | htwo
          · rcases htwo with ⟨rfl, rfl⟩; exact h46
          · rcases htwo with ⟨rfl, rfl⟩; exact h410
          · rcases htwo with ⟨rfl, rfl⟩; exact h68
          · rcases htwo with ⟨rfl, rfl⟩; exact h610
          · rcases htwo with ⟨rfl, rfl⟩; exact h810
        · rcases hspecial with ⟨rfl, rfl⟩
          exact h69

/-- At maximum degree twelve, the same routes leave exactly `(8,12)` and
`(9,12)` as the first new primitive unordered pairs. -/
theorem Max12FirstPrimitives (m : ℕ) (hm : m ≤ 12) :
    (¬ (m = 0 ∨ Nat.gcd m 12 ≤ 2 ∨ m = 12 ∨ (m < 12 ∧ m ∣ 12))) ↔
      m = 8 ∨ m = 9 := by
  interval_cases m <;> norm_num at *

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
  intro m n hm hn
  generalize ht : m + n = t
  induction t using Nat.strong_induction_on generalizing m n with
  | h t ih =>
      by_cases hmn : m ≤ n
      · rcases Max11RouteClassification m n hmn hn with
          hzero' | hgcd' | heq' | hdiv' | hspecial
        · subst m
          exact hzero n
        · exact hgcd m n hgcd'
        · subst n
          apply hequal m
          intro r hr
          exact ih (r + m) (by omega) r m (by omega) hm rfl
        · apply hdiv m n hdiv'.1 hdiv'.2
          intro r hr
          exact ih (m + r) (by omega) m r hm (by omega) rfl
        · rcases hspecial with ⟨rfl, rfl⟩
          exact h69
      · have hnm : n ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmn)
        apply hsymm n m
        rcases Max11RouteClassification n m hnm hm with
          hzero' | hgcd' | heq' | hdiv' | hspecial
        · subst n
          exact hzero m
        · exact hgcd n m hgcd'
        · exact False.elim (hmn (heq' ▸ le_rfl))
        · apply hdiv n m hdiv'.1 hdiv'.2
          intro r hr
          exact ih (n + r) (by omega) n r hn (by omega) rfl
        · rcases hspecial with ⟨rfl, rfl⟩
          exact h69

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

/-- Swapping the target coordinates preserves the Keller condition, changing
the nonzero Jacobian constant only by sign. -/
theorem IsPlaneKellerPair.swap {K : Type*} [Field K]
    {P Q : MvPolynomial (Fin 2) K} (h : IsPlaneKellerPair P Q) :
    IsPlaneKellerPair Q P := by
  rcases h with ⟨j, hj, hjac⟩
  refine ⟨-j, neg_ne_zero.mpr hj, ?_⟩
  calc
    PlaneJacobian Q P = -PlaneJacobian P Q := by
      simp only [PlaneJacobian]
      ring
    _ = -(MvPolynomial.C j) := congrArg Neg.neg hjac
    _ = MvPolynomial.C (-j) := by simp

/-- Ring generation is symmetric in the two target coordinates. -/
theorem PlanePairGenerates.swap {K : Type*} [Field K]
    {P Q : MvPolynomial (Fin 2) K} (h : PlanePairGenerates P Q) :
    PlanePairGenerates Q P := by
  simpa [PlanePairGenerates, Set.pair_comm] using h

/-- The concrete degree predicate inherits target-swap symmetry. -/
theorem PlaneKellerAutomorphicAtDegrees.swap {K : Type*} [Field K]
    {m n : ℕ} (h : PlaneKellerAutomorphicAtDegrees (K := K) m n) :
    PlaneKellerAutomorphicAtDegrees (K := K) n m := by
  intro P Q hP hQ hKeller
  exact PlanePairGenerates.swap (h Q P hQ hP hKeller.swap)

/-- Concrete maximum-partial-`y`-degree-eleven composition.  Its conclusion
is the actual coordinate-ring equality for every bivariate Keller pair; its
hypotheses are precisely the four standard degree-route theorems and the
exceptional `(6,9)` leaf, now stated for that concrete predicate rather than
for an opaque `Good`. -/
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
  have hall := MaxPartialDegreeElevenClosure
    (PlaneKellerAutomorphicAtDegrees (K := K))
    (fun _ _ h => h.swap) hzero hgcd hdiv hequal h69
  intro P Q hPdegree hQdegree hKeller
  exact hall (MvPolynomial.degreeOf 1 P) (MvPolynomial.degreeOf 1 Q)
    hPdegree hQdegree P Q rfl rfl hKeller

#print axioms Max11RouteClassification
#print axioms Max11UniquePrimitive
#print axioms Max11PrimeRouteClassification
#print axioms MaxPartialDegreeElevenClosureWithFiveGCDTwoLeaves
#print axioms MaxPartialDegreeElevenClosure
#print axioms Max12FirstPrimitives
#print axioms IsPlaneKellerPair.swap
#print axioms PlanePairGenerates.swap
#print axioms PlaneKellerAutomorphicAtDegrees.swap
#print axioms Max11PlaneKellerGeneration
