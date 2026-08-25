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

#print axioms Max11RouteClassification
#print axioms Max11UniquePrimitive
#print axioms MaxPartialDegreeElevenClosure
#print axioms Max12FirstPrimitives
