/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
-/
import Mathlib

/-! A local, standalone copy of the weighted-ODE rigidity argument used by
the strip-block formalization.  This keeps the Palomar package Mathlib-only;
it does not depend on the sibling `theorem-a` package. -/

namespace StripBlock.Rigidity

open Polynomial

variable {F : Type*}

private theorem coeff_mul_of_natDegree_le' [CommRing F] {p q : Polynomial F}
    {m n : ℕ} (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n) :
    (p * q).coeff (m + n) = p.coeff m * q.coeff n := by
  rw [coeff_mul]
  apply Finset.sum_eq_single_of_mem (m, n)
    (Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl)
  rintro ⟨i, j⟩ hij hne
  simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  rcases Nat.lt_or_ge m i with him | him
  · rw [coeff_eq_zero_of_natDegree_lt (hp.trans_lt him), zero_mul]
  · have hj : n < j := by
      rcases Nat.lt_or_ge n j with h | h
      · exact h
      · exact absurd (show (i, j) = (m, n) by
          simp only [Prod.mk.injEq]; omega) hne
    rw [coeff_eq_zero_of_natDegree_lt (hq.trans_lt hj), mul_zero]

private theorem coeff_bracket [CommRing F] (k : ℕ) (A D : Polynomial F)
    {a d n : ℕ} (ha : A.natDegree ≤ a) (hd : D.natDegree ≤ d)
    (hn : a + d = n + 1) :
    (A * derivative D - (k : Polynomial F) * (derivative A * D)).coeff n
      = ((d : F) - (k : F) * (a : F)) * (A.coeff a * D.coeff d) := by
  have hAD : (A * derivative D).coeff n =
      (d : F) * (A.coeff a * D.coeff d) := by
    rcases d with _ | d'
    · have h0 : derivative D = 0 := by
        rw [Polynomial.eq_C_of_natDegree_le_zero hd]; simp
      simp [h0]
    · have hn' : n = a + d' := by omega
      subst hn'
      have hd' : (derivative D).natDegree ≤ d' := by
        have h := natDegree_derivative_le D
        omega
      rw [coeff_mul_of_natDegree_le' ha hd', coeff_derivative]
      push_cast
      ring
  have hAD2 : (derivative A * D).coeff n =
      (a : F) * (A.coeff a * D.coeff d) := by
    rcases a with _ | a'
    · have h0 : derivative A = 0 := by
        rw [Polynomial.eq_C_of_natDegree_le_zero ha]; simp
      simp [h0]
    · have hn' : n = a' + d := by omega
      subst hn'
      have ha' : (derivative A).natDegree ≤ a' := by
        have h := natDegree_derivative_le A
        omega
      rw [coeff_mul_of_natDegree_le' ha' hd, coeff_derivative]
      push_cast
      ring
  rw [coeff_sub, hAD, ← Polynomial.C_eq_natCast, coeff_C_mul, hAD2]
  ring

private theorem core [CommRing F] [IsDomain F] (k : ℕ) (hk : 1 ≤ k)
    (A C : Polynomial F) (c : F) (hc : c ≠ 0)
    (hode : A * derivative C - (k : Polynomial F) * (derivative A * C)
      = Polynomial.C c)
    (hcast : ∀ m : ℕ, m ≤ C.natDegree →
      ((m : F) = ((k * A.natDegree : ℕ) : F)) → m = k * A.natDegree) :
    A.natDegree ≤ 1 := by
  by_contra hdeg
  rw [not_le] at hdeg
  have hA0 : A ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hC0 : C ≠ 0 := by
    rintro rfl
    simp only [derivative_zero, mul_zero, sub_zero] at hode
    exact hc (Polynomial.C_eq_zero.mp hode.symm)
  have hlcA : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA0
  have hlcC : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hC0
  have hstep2 : C.natDegree = k * A.natDegree := by
    have hkey := coeff_bracket k A C (le_refl A.natDegree)
      (le_refl C.natDegree)
      (show A.natDegree + C.natDegree =
          (A.natDegree + C.natDegree - 1) + 1 by omega)
    rw [hode, coeff_C, if_neg (by omega)] at hkey
    have h0 : (C.natDegree : F) - (k : F) * (A.natDegree : F) = 0 := by
      rcases mul_eq_zero.mp hkey.symm with h | h
      · exact h
      · exact absurd h (mul_ne_zero (by rwa [coeff_natDegree])
          (by rwa [coeff_natDegree]))
    apply hcast _ le_rfl
    push_cast
    linear_combination h0
  obtain ⟨k', rfl⟩ : ∃ n : ℕ, k = n + 1 := ⟨k - 1, by omega⟩
  set D : Polynomial F := Polynomial.C (A.leadingCoeff ^ (k' + 1)) * C
      - Polynomial.C C.leadingCoeff * A ^ (k' + 1) with hDdef
  have h1 : A * derivative D - ((k' + 1 : ℕ) : Polynomial F) *
        (derivative A * D) =
      Polynomial.C (A.leadingCoeff ^ (k' + 1) * c) := by
    rw [hDdef, derivative_sub, derivative_C_mul, derivative_C_mul,
      derivative_pow_succ]
    simp only [map_mul, map_pow, map_add, map_natCast, map_one]
    push_cast at hode ⊢
    linear_combination (Polynomial.C A.leadingCoeff ^ (k' + 1)) * hode
  have hDcoeff : ∀ m : ℕ, C.natDegree ≤ m → D.coeff m = 0 := by
    intro m hm
    rw [hDdef, coeff_sub, coeff_C_mul, coeff_C_mul]
    rcases eq_or_lt_of_le hm with heq | hlt
    · subst heq
      rw [coeff_natDegree, hstep2, coeff_pow_mul_natDegree]
      ring
    · rw [coeff_eq_zero_of_natDegree_lt hlt, coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt (natDegree_pow_le.trans hstep2.ge) hlt)]
      ring
  rcases eq_or_ne D 0 with hD0 | hD0
  · rw [hD0] at h1
    simp only [derivative_zero, mul_zero, sub_zero] at h1
    rcases mul_eq_zero.mp (Polynomial.C_eq_zero.mp h1.symm) with h | h
    · exact pow_ne_zero _ hlcA h
    · exact hc h
  · have hdD : D.natDegree < C.natDegree := by
      by_contra hge
      rw [not_lt] at hge
      exact leadingCoeff_ne_zero.mpr hD0
        (by rw [← coeff_natDegree]; exact hDcoeff _ hge)
    have hkey := coeff_bracket (k' + 1) A D (le_refl A.natDegree)
      (le_refl D.natDegree)
      (show A.natDegree + D.natDegree =
          (A.natDegree + D.natDegree - 1) + 1 by omega)
    rw [h1, coeff_C, if_neg (by omega)] at hkey
    have h0 : (D.natDegree : F) - ((k' + 1 : ℕ) : F) *
        (A.natDegree : F) = 0 := by
      rcases mul_eq_zero.mp hkey.symm with h | h
      · exact h
      · exact absurd h (mul_ne_zero (by rwa [coeff_natDegree])
          (by rwa [coeff_natDegree, leadingCoeff_ne_zero]))
    have hDdeg : D.natDegree = (k' + 1) * A.natDegree :=
      hcast _ hdD.le (by push_cast at h0 ⊢; linear_combination h0)
    exact absurd (hDdeg.trans hstep2.symm) hdD.ne

/-- Weighted-ODE rigidity, included locally so this package is standalone. -/
theorem odeRigidity [CommRing F] [IsDomain F] [CharZero F]
    (k : ℕ) (hk : 1 ≤ k) (A C : Polynomial F) (c : F) (hc : c ≠ 0)
    (hode : A * derivative C - (k : Polynomial F) * (derivative A * C)
      = Polynomial.C c) :
    A.natDegree ≤ 1 :=
  core k hk A C c hc hode fun _ _ h => Nat.cast_injective h

end StripBlock.Rigidity
