/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch (direction), Claude / Anthropic agent (formalization)
-/
import Mathlib

/-!
# The tame different: `v_𝔮(𝔇) = e_𝔮 - 1`

Mathlib provides only the floor `P ^ (e - 1) ∣ differentIdeal A B`
(`pow_sub_one_dvd_differentIdeal`).  This file supplies the missing `≤` half,
`¬ P ^ e ∣ differentIdeal A B`, under a tameness hypothesis, and packages the two
into the equality `v_P(𝔇) = e - 1`.

## Main results

* `KeystoneGraph.not_pow_dvd_differentIdeal`
* `KeystoneGraph.multiplicity_differentIdeal_eq`
-/

noncomputable section

open Algebra Module

namespace KeystoneGraph

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (A : Type*) {B : Type*} [CommRing A] [CommRing B]
  [IsDedekindDomain A] [IsDedekindDomain B] [Algebra A B]
  [Module.Finite A B] [Module.IsTorsionFree A B]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

/-- **The `≤` half of the tame different formula.**  If `P ^ e` is the exact power of
the maximal ideal `P` dividing `p B`, and the residue field `A ⧸ p` has characteristic
zero, then `P ^ e` does not divide the different.

The residue characteristic hypothesis is what makes the ramification tame: it is used
exactly once, to see that `dim_{A/p} (B / P ^ e) ≠ 0` in `A ⧸ p`. -/
theorem not_pow_dvd_differentIdeal_of_coprime
    {p : Ideal A} [p.IsMaximal] [CharZero (A ⧸ p)]
    {P Q : Ideal B} {e : ℕ} (he : e ≠ 0) (hPtop : P ≠ ⊤)
    (hQ : Ideal.map (algebraMap A B) p = P ^ e * Q) (hcop : IsCoprime P Q) :
    ¬ P ^ e ∣ differentIdeal A B := by
  classical
  let _ : Field (A ⧸ p) := Ideal.Quotient.field p
  -- residue algebras
  let : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap, hQ]; exact Ideal.mul_le_right)
  let : Algebra (A ⧸ p) (B ⧸ P ^ e) := Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap, hQ]; exact Ideal.mul_le_left)
  have : IsScalarTower A (A ⧸ p) (B ⧸ Q) := .of_algebraMap_eq' rfl
  have : IsScalarTower A (A ⧸ p) (B ⧸ P ^ e) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ Q) := Module.Finite.of_restrictScalars_finite A _ _
  have : Module.Finite (A ⧸ p) (B ⧸ P ^ e) := Module.Finite.of_restrictScalars_finite A _ _
  -- Chinese remainder splitting of the fibre
  let iso : (B ⧸ Ideal.map (algebraMap A B) p) ≃ₐ[A ⧸ p] ((B ⧸ P ^ e) × (B ⧸ Q)) :=
    { __ := (Ideal.quotEquivOfEq hQ).trans
        (Ideal.quotientMulEquivQuotientProd (P ^ e) Q hcop.pow_left),
      commutes' := Quotient.ind fun _ ↦ rfl }
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (iso.symm (1, 0))
  refine not_dvd_differentIdeal_of_intTrace_not_mem A (P ^ e) Q hQ.symm y ?_ ?_
  · have h2 := congr((iso $hy).2)
    simp only [AlgEquiv.apply_symm_apply] at h2
    simpa [iso, Ideal.Quotient.eq_zero_iff_mem] using h2
  · have hPetop : P ^ e ≠ ⊤ := fun h =>
      hPtop (top_le_iff.mp (h ▸ Ideal.pow_le_self he))
    have : Nontrivial (B ⧸ P ^ e) := Ideal.Quotient.nontrivial_iff.mpr hPetop
    have hpos : 0 < finrank (A ⧸ p) (B ⧸ P ^ e) := Module.finrank_pos
    have h1 : Algebra.trace (A ⧸ p) (B ⧸ P ^ e) 1
        = ((finrank (A ⧸ p) (B ⧸ P ^ e) : ℕ) : A ⧸ p) := by
      simpa using Algebra.trace_algebraMap (R := A ⧸ p) (S := B ⧸ P ^ e) 1
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Algebra.trace_quotient_eq_of_isDedekindDomain,
      hy, Algebra.trace_eq_of_algEquiv, Algebra.trace_prod_apply, map_zero, add_zero, h1]
    exact Nat.cast_ne_zero.mpr hpos.ne'

/-- **The `≤` half**, in terms of the exact power of `P` dividing `p B`. -/
theorem not_pow_dvd_differentIdeal
    {p : Ideal A} [p.IsMaximal] [CharZero (A ⧸ p)]
    {P : Ideal B} [P.IsMaximal] {e : ℕ} (he : e ≠ 0)
    (hdvd : P ^ e ∣ Ideal.map (algebraMap A B) p)
    (hnot : ¬ P ^ (e + 1) ∣ Ideal.map (algebraMap A B) p) :
    ¬ P ^ e ∣ differentIdeal A B := by
  obtain ⟨Q, hQ⟩ := hdvd
  have hPQ : ¬ P ∣ Q := by
    rintro ⟨Q', rfl⟩
    exact hnot ⟨Q', by rw [hQ]; ring⟩
  refine not_pow_dvd_differentIdeal_of_coprime A he ‹P.IsMaximal›.ne_top hQ ?_
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  exact hPQ (Ideal.dvd_iff_le.mpr
    (le_sup_right.trans_eq (‹P.IsMaximal›.eq_of_le hne le_sup_left).symm))

/-- **Tame different equality (`K1-L17`).**  `v_P(𝔇_{B/A}) = e - 1`, stated as the
exact divisibility `P ^ (e-1) ∥ differentIdeal A B`. -/
theorem multiplicity_differentIdeal_eq
    {p : Ideal A} [p.IsMaximal] [CharZero (A ⧸ p)] (hp : p ≠ ⊥)
    {P : Ideal B} [P.IsMaximal] {e : ℕ} (he : e ≠ 0)
    (hdvd : P ^ e ∣ Ideal.map (algebraMap A B) p)
    (hnot : ¬ P ^ (e + 1) ∣ Ideal.map (algebraMap A B) p) :
    multiplicity P (differentIdeal A B) = e - 1 := by
  refine multiplicity_eq_of_dvd_of_not_dvd
    (pow_sub_one_dvd_differentIdeal A P e hp hdvd) ?_
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he)]
  exact not_pow_dvd_differentIdeal A he hdvd hnot

/-- **`K1-L17` in `ramificationIdx` form**, the shape `K1-L18` consumes:
`v_P(𝔇_{B/A}) = e_P - 1` for a maximal ideal `P` of `B` lying over a maximal ideal `p`
of `A` whose residue field has characteristic zero. -/
theorem multiplicity_differentIdeal_eq_ramificationIdx_sub_one
    {p : Ideal A} [p.IsMaximal] [CharZero (A ⧸ p)] (hp : p ≠ ⊥)
    {P : Ideal B} [P.IsMaximal] [P.LiesOver p] :
    multiplicity P (differentIdeal A B) = P.ramificationIdx A - 1 := by
  classical
  have hpS : Ideal.map (algebraMap A B) p ≠ ⊥ := fun h =>
    hp ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective A B)).mp h)
  have hle : Ideal.map (algebraMap A B) p ≤ P :=
    Ideal.map_le_iff_le_comap.mpr (Ideal.over_def P p).le
  have hP0 : P ≠ ⊥ := by rintro rfl; exact hpS (le_bot_iff.mp hle)
  obtain ⟨Q, hsup, hQ⟩ := Ideal.eq_prime_pow_mul_coprime hpS P
  set n := Multiset.count P
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.map (algebraMap A B) p)) with hndef
  have hne : n ≠ 0 := by
    intro h0
    rw [h0, pow_zero, one_mul] at hQ
    rw [← hQ, sup_eq_left.mpr hle] at hsup
    exact ‹P.IsMaximal›.ne_top hsup
  have hidx : P.ramificationIdx A = n := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx p P hp]
    exact Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hpS inferInstance hP0
  rw [hidx]
  refine multiplicity_eq_of_dvd_of_not_dvd
    (pow_sub_one_dvd_differentIdeal A P n hp ⟨Q, hQ⟩) ?_
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hne)]
  exact not_pow_dvd_differentIdeal_of_coprime A hne ‹P.IsMaximal›.ne_top hQ
    (Ideal.isCoprime_iff_sup_eq.mpr hsup)

end KeystoneGraph
