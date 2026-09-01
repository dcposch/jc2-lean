/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch (direction), Claude / Anthropic agent (formalization)
-/
import Mathlib

/-!
# Local monogenicity of a finite extension of discrete valuation rings

Let `A ⊆ B` be discrete valuation rings with `B` finite over `A` and the residue
field extension separable.  Then `B = A[x]` for a single `x : B`.

This is the classical statement (Serre, *Corps Locaux*, ch. III §6 Prop. 12) that
a finite extension of DVRs with separable residue extension is *monogenic*.  It
is the missing prerequisite `K1-L17a` for the tame different computation.

Mathlib has `IsLocalRing.exists_adjoin_eq_top` in `RingTheory/LocalRing/Etale.lean`,
but that result assumes `Algebra.FormallyUnramified A B`, i.e. `m_A B = m_B`.  The
ramified case is genuinely different: the proof below produces a generator whose
value under a lift of the residue minimal polynomial is a *uniformizer* of `B`, and
then runs Nakayama against the `m_B`-adic filtration.

## Main results

* `KeystoneGraph.adjoin_eq_top_of_residue_gen_of_span_eq`: the Nakayama step.  If
  `residue B x` generates the residue field extension and `g` is a polynomial over
  `A` with `g(x)` generating `m_B`, then `A[x] = B`.
* `KeystoneGraph.exists_isUniformizer_aeval`: the construction of such an `x` and `g`.
* `KeystoneGraph.exists_adjoin_singleton_eq_top`: monogenicity.
-/

noncomputable section

open Polynomial IsLocalRing Algebra

namespace KeystoneGraph

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- In a discrete valuation ring, an element of `m ∖ m²` generates `m`. -/
theorem span_eq_maximalIdeal_of_mem_of_notMem_sq {y : R}
    (h1 : y ∈ maximalIdeal R) (h2 : y ∉ maximalIdeal R ^ 2) :
    Ideal.span {y} = maximalIdeal R := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [hϖ.maximalIdeal_eq] at h1 h2
  rw [Ideal.mem_span_singleton] at h1
  obtain ⟨c, rfl⟩ := h1
  have hc : IsUnit c := by
    by_contra hc
    have hcm : c ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal c).mpr hc
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hcm
    obtain ⟨d, rfl⟩ := hcm
    refine h2 ?_
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨d, by ring⟩
  have : Associated ϖ (ϖ * c) := ⟨hc.unit, by rw [IsUnit.unit_spec]⟩
  exact ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp
    (this.irreducible hϖ)).symm

end DVR

section Monogenic

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [Module.Finite A B] [FaithfulSMul A B]

/-- Taking residues commutes with evaluating a polynomial with coefficients in the base. -/
theorem residue_aeval (x : B) (q : A[X]) :
    residue B (aeval x q) = aeval (residue B x) (q.map (residue A)) :=
  map_aeval_eq_aeval_map (φ := residue A) (ψ := residue B) rfl q x

/-- If `residue B x` generates the residue field extension, every element of `B` agrees
with a polynomial in `x` modulo `m_B`. -/
theorem exists_aeval_sub_mem {x : B}
    (hx : Algebra.adjoin (ResidueField A) {residue B x} = ⊤) (u : B) :
    ∃ q : A[X], u - aeval x q ∈ maximalIdeal B := by
  have hmem : residue B u ∈ Algebra.adjoin (ResidueField A) {residue B x} := by
    rw [hx]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hmem
  obtain ⟨p, hp⟩ := hmem
  obtain ⟨q, rfl⟩ := Polynomial.map_surjective (residue A) residue_surjective p
  refine ⟨q, ?_⟩
  rw [← Ideal.Quotient.eq]
  exact hp.symm.trans (residue_aeval x q).symm

/-- **Nakayama step.**  Suppose the residue of `x : B` generates the residue field
extension, and some polynomial `g` over `A` has `g(x)` generating the maximal ideal
of `B`.  Then `A[x] = B`. -/
theorem adjoin_eq_top_of_residue_gen_of_span_eq {x : B}
    (hres : Algebra.adjoin (ResidueField A) {residue B x} = ⊤)
    {g : A[X]} (hg : Ideal.span {aeval x g} = maximalIdeal B) :
    Algebra.adjoin A {x} = ⊤ := by
  classical
  set C : Subalgebra A B := Algebra.adjoin A {x} with hC
  set N : Submodule A B := Subalgebra.toSubmodule C ⊔ maximalIdeal A • (⊤ : Submodule A B)
    with hN
  set ϖ : B := aeval x g with hϖdef
  -- membership facts inside `C`
  have hxC : x ∈ C := Algebra.self_mem_adjoin_singleton A x
  have haevalC : ∀ q : A[X], aeval x q ∈ C := by
    intro q
    rw [hC, Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨q, rfl⟩
  -- a uniformizer of `A`
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hπmem : π ∈ maximalIdeal A := by
    rw [hπ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self π
  have hmapmem : (algebraMap A B) π ∈ N := by
    refine Submodule.mem_sup_right ?_
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
    exact Ideal.mem_map_of_mem _ hπmem
  -- `ϖ` is a uniformizer of `B`
  have hϖirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hg.symm
  have hmB : ∀ n : ℕ, maximalIdeal B ^ n = Ideal.span {ϖ ^ n} := by
    intro n; rw [← hg, Ideal.span_singleton_pow]
  -- write `algebraMap π = unit * ϖ ^ e`
  have hπ0 : (algebraMap A B) π ≠ 0 := by
    simpa using fun h => hπ.ne_zero ((FaithfulSMul.algebraMap_injective A B) (by simpa using h))
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπ0 hϖirr
  -- downward induction along the `m_B`-adic filtration
  have key : ∀ j : ℕ, ∀ b : B, b ∈ maximalIdeal B ^ (e - j) → b ∈ N := by
    intro j
    induction j with
    | zero =>
      intro b hb
      rw [Nat.sub_zero, hmB, Ideal.mem_span_singleton] at hb
      obtain ⟨c, rfl⟩ := hb
      refine Submodule.mem_sup_right ?_
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
      have hrw : ϖ ^ e * c = (algebraMap A B) π * ((↑u⁻¹ : B) * c) := by
        rw [hu, show ((u : B) * ϖ ^ e) * ((↑u⁻¹ : B) * c)
              = ((u : B) * (↑u⁻¹ : B)) * (ϖ ^ e * c) from by ring]
        simp
      rw [hrw]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hπmem)
    | succ j ih =>
      rcases le_or_gt e j with hj | hj
      · intro b hb
        rw [Nat.sub_eq_zero_of_le (le_trans hj (Nat.le_succ j))] at hb
        exact ih b (by rwa [Nat.sub_eq_zero_of_le hj])
      · have hstep : e - j = (e - (j + 1)) + 1 := by omega
        intro b hb
        rw [hmB, Ideal.mem_span_singleton] at hb
        obtain ⟨w, rfl⟩ := hb
        obtain ⟨q, hq⟩ := exists_aeval_sub_mem hres w
        have hsplit : ϖ ^ (e - (j + 1)) * w =
            ϖ ^ (e - (j + 1)) * aeval x q + ϖ ^ (e - (j + 1)) * (w - aeval x q) := by ring
        rw [hsplit]
        refine Submodule.add_mem _ ?_ ?_
        · refine Submodule.mem_sup_left ?_
          exact Subalgebra.mul_mem C (Subalgebra.pow_mem C (haevalC g) _) (haevalC q)
        · refine ih _ ?_
          rw [hstep, hmB, Ideal.mem_span_singleton]
          obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp (by rwa [← hg] at hq)
          exact ⟨z, by rw [hz]; ring⟩
  -- Nakayama
  refine eq_top_iff.mpr <| Submodule.le_of_le_smul_of_le_jacobson_bot
    (Module.finite_def.mp inferInstance) (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    (?_ : ⊤ ≤ (Algebra.adjoin A {x}).toSubmodule ⊔ maximalIdeal A • ⊤)
  intro b _
  exact key e b (by simp)

/-- **Generator construction.**  If the residue field extension is separable there is an
`x : B` whose residue generates the residue field extension together with a monic
`g : A[X]` such that `g(x)` generates the maximal ideal of `B`.

The generator is a lift `β` of a primitive element of the residue extension, corrected
by a uniformizer of `B` when `g(β)` happens to lie in `m_B ^ 2`; the correction works
because separability makes `g'(β)` a unit. -/
theorem exists_residue_gen_and_span_eq
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    ∃ (x : B) (g : A[X]), Algebra.adjoin (ResidueField A) {residue B x} = ⊤ ∧
      g.Monic ∧ Ideal.span {aeval x g} = maximalIdeal B := by
  obtain ⟨β₀, hβ₀⟩ := Field.exists_primitive_element (ResidueField A) (ResidueField B)
  have hgen : Algebra.adjoin (ResidueField A) {β₀} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (IsAlgebraic.of_finite _ _), hβ₀, IntermediateField.top_toSubalgebra]
  obtain ⟨β, hβ⟩ := residue_surjective (R := B) β₀
  have hmon : (minpoly (ResidueField A) β₀).Monic :=
    minpoly.monic (Algebra.IsIntegral.isIntegral β₀)
  have hsep : (minpoly (ResidueField A) β₀).Separable :=
    Algebra.IsSeparable.isSeparable (ResidueField A) β₀
  obtain ⟨g, hgmap, -, hgmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (f := residue A) residue_surjective _) hmon
  -- `g` vanishes at any lift of `β₀`, and its derivative does not
  have hgval : ∀ y : B, residue B y = β₀ → residue B (aeval y g) = 0 := by
    intro y hy
    rw [residue_aeval, hgmap, hy]
    exact minpoly.aeval _ _
  have hgderiv : ∀ y : B, residue B y = β₀ → residue B (aeval y (derivative g)) ≠ 0 := by
    intro y hy
    rw [residue_aeval, ← Polynomial.derivative_map, hgmap, hy]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)
  -- it suffices to place `g(x)` outside `m_B ^ 2`
  suffices h : ∃ x : B, residue B x = β₀ ∧ aeval x g ∉ maximalIdeal B ^ 2 by
    obtain ⟨x, hx, hx2⟩ := h
    exact ⟨x, g, by rw [hx]; exact hgen, hgmonic,
      span_eq_maximalIdeal_of_mem_of_notMem_sq
        (Ideal.Quotient.eq_zero_iff_mem.mp (hgval x hx)) hx2⟩
  by_cases hcase : aeval β g ∈ maximalIdeal B ^ 2
  · -- correct `β` by a uniformizer
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
    have hϖm : ϖ ∈ maximalIdeal B := by
      rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ
    have hsq : maximalIdeal B ^ 2 = Ideal.span {ϖ ^ 2} := by
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
    have hϖ0 : residue B ϖ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hϖm
    have hresx : residue B (β + ϖ) = β₀ := by rw [map_add, hβ, hϖ0, add_zero]
    refine ⟨β + ϖ, hresx, ?_⟩
    have hev : ∀ (p : A[X]) (y : B), aeval y p = (p.map (algebraMap A B)).eval y := by
      intro p y; simp [Polynomial.aeval_def, Polynomial.eval_map]
    obtain ⟨c, hc⟩ := (g.map (algebraMap A B)).binomExpansion β ϖ
    have hsum : aeval (β + ϖ) g
        = aeval β g + aeval β (derivative g) * ϖ + c * ϖ ^ 2 := by
      rw [hev g (β + ϖ), hc, hev g β, hev (derivative g) β, Polynomial.derivative_map]
    rw [hsum]
    intro hmem
    have hZ : c * ϖ ^ 2 ∈ maximalIdeal B ^ 2 := by
      rw [hsq, Ideal.mem_span_singleton]; exact ⟨c, mul_comm _ _⟩
    have hY : aeval β (derivative g) * ϖ ∈ maximalIdeal B ^ 2 := by
      have h3 := Ideal.sub_mem _ (Ideal.sub_mem _ hmem hcase) hZ
      have h4 : aeval β g + aeval β (derivative g) * ϖ + c * ϖ ^ 2
          - aeval β g - c * ϖ ^ 2 = aeval β (derivative g) * ϖ := by ring
      rwa [h4] at h3
    rw [hsq, Ideal.mem_span_singleton] at hY
    obtain ⟨z, hz⟩ := hY
    have hd : aeval β (derivative g) = ϖ * z :=
      mul_right_cancel₀ hϖ.ne_zero (by rw [hz]; ring)
    refine hgderiv β hβ ?_
    rw [hd]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (by rw [hϖ.maximalIdeal_eq]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ))
  · exact ⟨β, hβ, hcase⟩

/-- **Local monogenicity (`K1-L17a`).**  A finite extension `B` of a discrete valuation
ring `A` by a discrete valuation ring, with separable residue field extension, is
generated over `A` by a single element: `B = A[x]`. -/
theorem exists_adjoin_singleton_eq_top
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    ∃ x : B, Algebra.adjoin A {x} = ⊤ := by
  obtain ⟨x, g, hres, -, hspan⟩ :=
    exists_residue_gen_and_span_eq (A := A) (B := B)
  exact ⟨x, adjoin_eq_top_of_residue_gen_of_span_eq hres hspan⟩

/-- Monogenicity in `PowerBasis` form: `B` admits a power basis over `A`. -/
theorem nonempty_powerBasis
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    Nonempty (PowerBasis A B) := by
  have htf : Module.IsTorsionFree A B := by
    refine ⟨fun {a} ha x y hxy => ?_⟩
    have h2 : algebraMap A B a * x = algebraMap A B a * y := by
      simpa [Algebra.smul_def] using hxy
    refine mul_left_cancel₀ (fun h => ha.ne_zero ?_) h2
    exact FaithfulSMul.algebraMap_injective A B (by simpa using h)
  have : Module.Free A B := Module.free_of_finite_type_torsion_free'
  obtain ⟨x, hx⟩ := exists_adjoin_singleton_eq_top (A := A) (B := B)
  exact ⟨(IsAdjoinRootMonic.mkOfAdjoinEqTop' hx).powerBasis⟩

end Monogenic

end KeystoneGraph
