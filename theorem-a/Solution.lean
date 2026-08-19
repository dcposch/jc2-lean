/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch (direction), Claude / Anthropic agents (proofs)
-/
import Mathlib

/-!
# Solution: proofs of `TheoremA` and `TheoremA_charP`

Follows the proof of Theorem `thm:ode` (“ODE rigidity, all weights”,
Section 6 of the campaign paper — Theorem 6.1 in the current compilation;
Theorem A in `MATHIEU.md` §5.1 of the archived theory bundle,
DOI 10.5281/zenodo.22002825).  Degree bookkeeping:

* `JC72108.coeff_bracket` (Step 1): for `natDegree A ≤ a`, `natDegree D ≤ d`
  and `a + d = n + 1`, the coefficient of `y^n` in `A·D′ − ν·A′·D` is
  `(d − ν·a)·(A_a·D_d)`; in particular nothing of higher degree occurs.
* `JC72108.core` (Steps 2–4): the shared rigidity argument over an integral
  domain, with the characteristic packaged as one cast-injectivity hypothesis.
  Step 2 forces `deg C = ν·deg A`; Steps 3–4 subtract the kernel element
  `A^ν` (denominators cleared: `D := lc(A)^ν·C − lc(C)·A^ν`) and read the
  top coefficient once more.
* `TheoremA`, `TheoremA_charP`: the two instantiations (characteristic zero,
  and characteristic `p` with `ν·deg A < p`, `deg C < p`).
-/

namespace JC72108

open Polynomial

variable {F : Type*}

/-- Coefficient of a product at the sum of degree bounds. -/
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

/-- **Step 1** (leading-coefficient bookkeeping).  If `natDegree A ≤ a`,
`natDegree D ≤ d` and `a + d = n + 1`, then the coefficient of `y^n` in the
weighted bracket `A·D′ − ν·A′·D` is `(d − ν·a)·(A_a·D_d)`.  Together with
`coeff_eq_zero_of_natDegree_lt` this is the statement that the bracket has
degree at most `a + d − 1`, with that coefficient explicit. -/
private theorem coeff_bracket [CommRing F] (ν : ℕ) (A D : Polynomial F)
    {a d n : ℕ} (ha : A.natDegree ≤ a) (hd : D.natDegree ≤ d)
    (hn : a + d = n + 1) :
    (A * derivative D - (ν : Polynomial F) * (derivative A * D)).coeff n
      = ((d : F) - (ν : F) * (a : F)) * (A.coeff a * D.coeff d) := by
  have hAD : (A * derivative D).coeff n = (d : F) * (A.coeff a * D.coeff d) := by
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
  have hAD2 : (derivative A * D).coeff n = (a : F) * (A.coeff a * D.coeff d) := by
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

/-- **Steps 2–4** of the paper proof, over an arbitrary integral domain; the
characteristic enters only through the cast hypothesis `hcast`. -/
private theorem core [CommRing F] [IsDomain F] (ν : ℕ) (hν : 1 ≤ ν)
    (A C : Polynomial F) (c : F) (hc : c ≠ 0)
    (hode : A * derivative C - (ν : Polynomial F) * (derivative A * C)
      = Polynomial.C c)
    (hcast : ∀ m : ℕ, m ≤ C.natDegree →
      ((m : F) = ((ν * A.natDegree : ℕ) : F)) → m = ν * A.natDegree) :
    A.natDegree ≤ 1 := by
  by_contra hdeg
  rw [not_le] at hdeg
  -- both `A` and `C` are nonzero
  have hA0 : A ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hC0 : C ≠ 0 := by
    rintro rfl
    simp only [derivative_zero, mul_zero, sub_zero] at hode
    exact hc (Polynomial.C_eq_zero.mp hode.symm)
  have hlcA : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA0
  have hlcC : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hC0
  -- Step 2: `deg C = ν·deg A`
  have hstep2 : C.natDegree = ν * A.natDegree := by
    have hkey := coeff_bracket ν A C (le_refl A.natDegree) (le_refl C.natDegree)
      (show A.natDegree + C.natDegree = (A.natDegree + C.natDegree - 1) + 1 by
        omega)
    rw [hode, coeff_C, if_neg (by omega)] at hkey
    have h0 : (C.natDegree : F) - (ν : F) * (A.natDegree : F) = 0 := by
      rcases mul_eq_zero.mp hkey.symm with h | h
      · exact h
      · exact absurd h (mul_ne_zero (by rwa [coeff_natDegree])
          (by rwa [coeff_natDegree]))
    apply hcast _ le_rfl
    push_cast
    linear_combination h0
  -- write `ν = ν' + 1`
  obtain ⟨ν', rfl⟩ : ∃ k : ℕ, ν = k + 1 := ⟨ν - 1, by omega⟩
  -- Steps 3–4: subtract the kernel element `A^ν`, denominators cleared
  set D : Polynomial F := Polynomial.C (A.leadingCoeff ^ (ν' + 1)) * C
      - Polynomial.C C.leadingCoeff * A ^ (ν' + 1) with hDdef
  -- Step 3: the bracket applied to `D` is still a nonzero constant
  have h1 : A * derivative D - ((ν' + 1 : ℕ) : Polynomial F) * (derivative A * D)
      = Polynomial.C (A.leadingCoeff ^ (ν' + 1) * c) := by
    rw [hDdef, derivative_sub, derivative_C_mul, derivative_C_mul,
      derivative_pow_succ]
    simp only [map_mul, map_pow, map_add, map_natCast, map_one]
    push_cast at hode ⊢
    linear_combination (Polynomial.C A.leadingCoeff ^ (ν' + 1)) * hode
  -- the leading terms cancel: all coefficients of `D` from `deg C` on vanish
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
  · -- if `D = 0`, the nonzero constant `lc(A)^ν·c` would vanish
    rw [hD0] at h1
    simp only [derivative_zero, mul_zero, sub_zero] at h1
    rcases mul_eq_zero.mp (Polynomial.C_eq_zero.mp h1.symm) with h | h
    · exact pow_ne_zero _ hlcA h
    · exact hc h
  · -- Step 4: if `D ≠ 0`, then `deg D < ν·deg A`, and Step 1 applies again
    have hd : D.natDegree < C.natDegree := by
      by_contra hge
      rw [not_lt] at hge
      exact leadingCoeff_ne_zero.mpr hD0
        (by rw [← coeff_natDegree]; exact hDcoeff _ hge)
    have hkey := coeff_bracket (ν' + 1) A D (le_refl A.natDegree)
      (le_refl D.natDegree)
      (show A.natDegree + D.natDegree = (A.natDegree + D.natDegree - 1) + 1 by
        omega)
    rw [h1, coeff_C, if_neg (by omega)] at hkey
    have h0 : (D.natDegree : F) - ((ν' + 1 : ℕ) : F) * (A.natDegree : F) = 0 := by
      rcases mul_eq_zero.mp hkey.symm with h | h
      · exact h
      · exact absurd h (mul_ne_zero (by rwa [coeff_natDegree])
          (by rwa [coeff_natDegree, leadingCoeff_ne_zero]))
    have hDdeg : D.natDegree = (ν' + 1) * A.natDegree :=
      hcast _ hd.le (by push_cast at h0 ⊢; linear_combination h0)
    exact absurd (hDdeg.trans hstep2.symm) hd.ne

end JC72108

/-- **Theorem A** (ODE rigidity, all weights; characteristic zero).
If polynomials `A, C` over an integral domain `F` of characteristic zero
satisfy `A·C′ − ν·A′·C = c` with integer weight `ν ≥ 1` and `c` a nonzero
constant, then `deg A ≤ 1`.  (Theorem `thm:ode`, “ODE rigidity, all
weights”, Section 6 of the campaign paper — Theorem 6.1 in the current
compilation; Theorem A in `MATHIEU.md` §5.1 of the archived bundle,
DOI 10.5281/zenodo.22002825.) -/
theorem TheoremA {F : Type*} [CommRing F] [IsDomain F] [CharZero F]
    (ν : ℕ) (hν : 1 ≤ ν) (A C : Polynomial F) (c : F) (hc : c ≠ 0)
    (hode : A * Polynomial.derivative C
        - (ν : Polynomial F) * (Polynomial.derivative A * C) = Polynomial.C c) :
    A.natDegree ≤ 1 :=
  JC72108.core ν hν A C c hc hode fun _ _ h => Nat.cast_injective h

/-- **Theorem A, positive characteristic.**  Over an integral domain of
characteristic `p`, the same rigidity holds provided `p` dominates the degree
data: `ν·deg A < p` and `deg C < p`.  (A standalone strengthening extracted
from the Section 6 proof and the closing positive-characteristic remark of
the campaign paper, cf. `MATHIEU.md` §5.4: in the application there `ν = k`,
`deg A ≤ d₂`, `deg C ≤ k·d₂`, so the recorded conservative bound
`p > (k+1)·d₂` implies both hypotheses.) -/
theorem TheoremA_charP {F : Type*} [CommRing F] [IsDomain F] (p : ℕ) [CharP F p]
    (ν : ℕ) (hν : 1 ≤ ν) (A C : Polynomial F) (c : F) (hc : c ≠ 0)
    (hνA : ν * A.natDegree < p) (hC : C.natDegree < p)
    (hode : A * Polynomial.derivative C
        - (ν : Polynomial F) * (Polynomial.derivative A * C) = Polynomial.C c) :
    A.natDegree ≤ 1 :=
  JC72108.core ν hν A C c hc hode fun _ hm h =>
    CharP.natCast_injOn_Iio F p (lt_of_le_of_lt hm hC) hνA h

-- Axiom audit: Palomar permits exactly `propext`, `Classical.choice`,
-- `Quot.sound`.  The two commands below print the axiom dependencies at
-- build time; `scripts/check_axioms.sh` verifies the output mechanically.
#print axioms TheoremA
#print axioms TheoremA_charP
