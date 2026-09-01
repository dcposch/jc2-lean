/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch (direction), Claude / Anthropic and Grok / xAI
agents (formalization)
-/
import Mathlib
import KeystoneGraph.Setup
import KeystoneGraph.KellerUnramified

/-!
# Algebraic independence of a plane Keller pair

For a Keller pair `P, Q`, the coordinate subalgebra `k[P, Q] ⊆ k[x, y]` is a
polynomial ring in two variables, and the fraction-field extension
`k(x, y) / k(P, Q)` is finite. The argument is the Ω-plus-trdeg route of
survey A.8:

1. K1-L10 gives `Algebra.FormallyUnramified k[P,Q] k[x,y]`. Passing to
   fraction fields (unramified is preserved by localization, then by
   restricting scalars along `k[P,Q] → k(P,Q)`) yields
   `FormallyUnramified k(P,Q) k(x,y)`.
2. The extension `k(x,y) / k(P,Q)` is essentially of finite type, as a
   composite of the finite-type algebra `k[x,y] / k` with a localization.
   `Algebra.FormallyUnramified.iff_isSeparable` therefore supplies
   algebraic separability.
3. Transcendence-degree additivity (`trdeg_add_eq`, `trdeg_eq_zero_iff`)
   with `MvPolynomial.algebraicIndependent_X` (so `trdeg k k(x,y) = 2`)
   forces `trdeg k k(P,Q) = 2`, hence `P, Q` are algebraically independent.
4. The induced `k`-algebra equivalence `k[P,Q] ≃ₐ[k] k[X, Y]` is
   `AlgebraicIndependent.aevalEquiv`.
5. Algebraic + essentially finite type implies
   `FiniteDimensional k(P,Q) k(x,y)`; `kellerDegree` is that finrank.

The inequality `2 ≤ kellerDegree` is the Keystone noninvertibility
hypothesis and is **imported, not proved**.

Consumables: K1-L10, `Algebra.FormallyUnramified.iff_isSeparable`,
`Algebra.trdeg_add_eq`, `Algebra.trdeg_eq_zero_iff`,
`MvPolynomial.algebraicIndependent_X`, `Algebra.IsIntegral.finite`
(via `Algebra.finite_of_essFiniteType_of_isAlgebraic`).
-/

noncomputable section

namespace KeystoneGraph

open MvPolynomial Algebra
open scoped Cardinal nonZeroDivisors

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

variable {k : Type*} [Field k]

/-! ### Generators of `k[P, Q]` as a `Fin 2`-family -/

lemma range_pair (P Q : Plane k) :
    Set.range (![P, Q] : Fin 2 → Plane k) = {P, Q} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

/-- The pair `(P, Q)` as elements of the coordinate subalgebra. -/
def pairInCoord (P Q : Plane k) : Fin 2 → coordRing P Q :=
  fun i => ⟨![P, Q] i, by
    fin_cases i
    · simpa using mem_coordSubalgebra_P P Q
    · simpa using mem_coordSubalgebra_Q P Q⟩

lemma pairInCoord_val (P Q : Plane k) :
    Subtype.val ∘ pairInCoord P Q = ![P, Q] :=
  rfl

lemma range_pairInCoord (P Q : Plane k) :
    Set.range (pairInCoord P Q) =
      ((↑) : coordRing P Q → Plane k) ⁻¹' {P, Q} := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [pairInCoord]
  · intro hz
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h
    · exact ⟨0, Subtype.ext (by simp [pairInCoord, h])⟩
    · exact ⟨1, Subtype.ext (by simp [pairInCoord, h])⟩

lemma adjoin_pairInCoord_eq_top (P Q : Plane k) :
    Algebra.adjoin k (Set.range (pairInCoord P Q)) = ⊤ := by
  rw [range_pairInCoord]
  exact Algebra.adjoin_adjoin_coe_preimage (s := {P, Q})

/-! ### Fraction-field tower

`Algebra k (FractionRing _)` and `Algebra (coordRing P Q) (FractionRing (Plane k))`
are supplied by Ore localization. The remaining map is
`FractionRing.liftAlgebra : k(P,Q) → k(x,y)`. -/

variable {P Q : Plane k}

instance : Algebra (FractionRing (coordRing P Q)) (FractionRing (Plane k)) :=
  FractionRing.liftAlgebra (coordRing P Q) (FractionRing (Plane k))

instance : IsScalarTower (coordRing P Q) (FractionRing (coordRing P Q))
    (FractionRing (Plane k)) :=
  IsScalarTower.of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap
      (FaithfulSMul.algebraMap_injective (coordRing P Q)
        (FractionRing (Plane k))) x).symm

instance : IsScalarTower k (FractionRing (coordRing P Q)) (FractionRing (Plane k)) :=
  IsScalarTower.to₁₃₄ k (coordRing P Q) (FractionRing (coordRing P Q))
    (FractionRing (Plane k))

instance : FiniteType k (coordRing P Q) :=
  FiniteType.adjoin_of_finite (Set.toFinite ({P, Q} : Set (Plane k)))

/-! ### Formally unramified, then separable, at the fraction-field level -/

lemma IsKellerPair.formallyUnramified_fractionRingPlane {P Q : Plane k}
    (hPQ : IsKellerPair P Q) :
    FormallyUnramified (coordRing P Q) (FractionRing (Plane k)) := by
  have := hPQ.formallyUnramified
  have : FormallyUnramified (Plane k) (FractionRing (Plane k)) :=
    FormallyUnramified.of_isLocalization (nonZeroDivisors (Plane k))
  exact FormallyUnramified.comp (coordRing P Q) (Plane k) (FractionRing (Plane k))

lemma IsKellerPair.formallyUnramified_fractionRings {P Q : Plane k}
    (hPQ : IsKellerPair P Q) :
    FormallyUnramified (FractionRing (coordRing P Q)) (FractionRing (Plane k)) :=
  have := hPQ.formallyUnramified_fractionRingPlane
  FormallyUnramified.of_restrictScalars (coordRing P Q)
    (FractionRing (coordRing P Q)) (FractionRing (Plane k))

lemma essFiniteType_fractionRings (P Q : Plane k) :
    EssFiniteType (FractionRing (coordRing P Q)) (FractionRing (Plane k)) :=
  EssFiniteType.of_comp k (FractionRing (coordRing P Q)) (FractionRing (Plane k))

lemma IsKellerPair.isSeparable_fractionRings {P Q : Plane k}
    (hPQ : IsKellerPair P Q) :
    Algebra.IsSeparable (FractionRing (coordRing P Q)) (FractionRing (Plane k)) := by
  have := essFiniteType_fractionRings P Q
  exact (FormallyUnramified.iff_isSeparable (FractionRing (coordRing P Q))
      (FractionRing (Plane k))).mp hPQ.formallyUnramified_fractionRings

lemma IsKellerPair.isAlgebraic_fractionRings {P Q : Plane k}
    (hPQ : IsKellerPair P Q) :
    Algebra.IsAlgebraic (FractionRing (coordRing P Q)) (FractionRing (Plane k)) :=
  have := hPQ.isSeparable_fractionRings
  inferInstance

/-! ### Transcendence degrees -/

lemma trdeg_plane_eq_two : trdeg k (Plane k) = 2 := by
  simp [MvPolynomial.trdeg_of_isDomain (S := k) (ι := Fin 2)]

lemma isAlgebraic_plane_fractionRing :
    Algebra.IsAlgebraic (Plane k) (FractionRing (Plane k)) :=
  IsLocalization.isAlgebraic _ (nonZeroDivisors (Plane k))

lemma trdeg_fractionRingPlane_eq_two : trdeg k (FractionRing (Plane k)) = 2 := by
  have : Algebra.IsAlgebraic (Plane k) (FractionRing (Plane k)) :=
    isAlgebraic_plane_fractionRing
  have hsum := trdeg_add_eq (R := k) (S := Plane k) (A := FractionRing (Plane k))
  rw [trdeg_eq_zero_iff.mpr this, add_zero, trdeg_plane_eq_two] at hsum
  exact hsum.symm

lemma isAlgebraic_coordRing_fractionRing (P Q : Plane k) :
    Algebra.IsAlgebraic (coordRing P Q) (FractionRing (coordRing P Q)) :=
  IsLocalization.isAlgebraic _ (nonZeroDivisors (coordRing P Q))

lemma IsKellerPair.trdeg_fractionRingCoord_eq_two {P Q : Plane k}
    (hPQ : IsKellerPair P Q) :
    trdeg k (FractionRing (coordRing P Q)) = 2 := by
  have : Algebra.IsAlgebraic (FractionRing (coordRing P Q)) (FractionRing (Plane k)) :=
    hPQ.isAlgebraic_fractionRings
  have hsum := trdeg_add_eq (R := k) (S := FractionRing (coordRing P Q))
    (A := FractionRing (Plane k))
  rw [trdeg_eq_zero_iff.mpr this, add_zero, trdeg_fractionRingPlane_eq_two] at hsum
  exact hsum

lemma IsKellerPair.trdeg_coordRing_eq_two {P Q : Plane k} (hPQ : IsKellerPair P Q) :
    trdeg k (coordRing P Q) = 2 := by
  have : Algebra.IsAlgebraic (coordRing P Q) (FractionRing (coordRing P Q)) :=
    isAlgebraic_coordRing_fractionRing P Q
  have hsum := trdeg_add_eq (R := k) (S := coordRing P Q)
    (A := FractionRing (coordRing P Q))
  rw [trdeg_eq_zero_iff.mpr this, add_zero, hPQ.trdeg_fractionRingCoord_eq_two] at hsum
  exact hsum

/-! ### Algebraic independence and the polynomial identification -/

lemma isAlgebraic_adjoin_pairInCoord (P Q : Plane k) :
    Algebra.IsAlgebraic (Algebra.adjoin k (Set.range (pairInCoord P Q)))
      (coordRing P Q) := by
  refine ⟨fun x => ?_⟩
  have hx : x ∈ Algebra.adjoin k (Set.range (pairInCoord P Q)) := by
    rw [adjoin_pairInCoord_eq_top]
    exact Algebra.mem_top
  exact isAlgebraic_algebraMap
    (R := Algebra.adjoin k (Set.range (pairInCoord P Q))) ⟨x, hx⟩

lemma IsKellerPair.isTranscendenceBasis_pairInCoord {P Q : Plane k}
    (hPQ : IsKellerPair P Q) :
    IsTranscendenceBasis k (pairInCoord P Q) := by
  have := isAlgebraic_adjoin_pairInCoord P Q
  refine Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite
    (R := k) (x := pairInCoord P Q) ?_
  simp [hPQ.trdeg_coordRing_eq_two]

/-- A Keller pair is algebraically independent over `k`. -/
theorem IsKellerPair.algebraicIndependent {P Q : Plane k} (hPQ : IsKellerPair P Q) :
    AlgebraicIndependent k ![P, Q] := by
  have h := (hPQ.isTranscendenceBasis_pairInCoord).1.map'
    (f := (coordSubalgebra P Q).val) Subtype.val_injective
  simpa [pairInCoord_val] using h

/-- The coordinate subalgebra of a Keller pair is a polynomial ring in two
variables. -/
def IsKellerPair.coordRingEquivMvPolynomial {P Q : Plane k}
    (hPQ : IsKellerPair P Q) :
    coordRing P Q ≃ₐ[k] MvPolynomial (Fin 2) k :=
  (hPQ.algebraicIndependent.aevalEquiv.trans <|
      Subalgebra.equivOfEq _ _ (by rw [range_pair]; rfl)).symm

/-! ### Finite dimensionality and the geometric degree -/

/-- The fraction-field extension `k(x,y) / k(P,Q)` is finite-dimensional. -/
theorem IsKellerPair.finiteDimensional_fractionRings {P Q : Plane k}
    (hPQ : IsKellerPair P Q) :
    FiniteDimensional (FractionRing (coordRing P Q)) (FractionRing (Plane k)) := by
  have := hPQ.isAlgebraic_fractionRings
  have := essFiniteType_fractionRings P Q
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic
    (F := FractionRing (coordRing P Q)) (E := FractionRing (Plane k))

/-- Geometric degree `d = [k(x,y) : k(P,Q)]` of a Keller pair. -/
def IsKellerPair.kellerDegree {P Q : Plane k} (hPQ : IsKellerPair P Q) : ℕ :=
  have := hPQ.finiteDimensional_fractionRings
  Module.finrank (FractionRing (coordRing P Q)) (FractionRing (Plane k))

/-- Noninvertibility of a Keller pair: the fraction-field degree is at least 2.

This is an imported Keystone 1 hypothesis (the polynomial map is not an
automorphism of the plane). It is **not proved** in this lane. -/
def IsKellerPair.Noninvertible {P Q : Plane k} (hPQ : IsKellerPair P Q) : Prop :=
  2 ≤ hPQ.kellerDegree

theorem IsKellerPair.kellerDegree_eq_finrank {P Q : Plane k}
    (hPQ : IsKellerPair P Q) :
    hPQ.kellerDegree =
      Module.finrank (FractionRing (coordRing P Q)) (FractionRing (Plane k)) :=
  rfl

#print axioms IsKellerPair.algebraicIndependent
#print axioms IsKellerPair.coordRingEquivMvPolynomial
#print axioms IsKellerPair.finiteDimensional_fractionRings
#print axioms IsKellerPair.kellerDegree

end KeystoneGraph
