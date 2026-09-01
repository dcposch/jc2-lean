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
# K1-L15: the étale box is empty

Every prime of the graph algebra `B` that lies in the plane-ring locus — i.e.
every prime `q` at which `B_q` is isomorphic, as an `A`-algebra, to a
localization of the plane ring — has ramification index `1` over its
contraction to `A`. Equivalently, the four-box cell `(U, e > 1)` is empty.

The argument is the Ω-route of survey A.5 together with the ramification
consumables:

* K1-L10 supplies `Algebra.FormallyUnramified A k[x,y]`.
* `Algebra.FormallyUnramified.of_isLocalization` promotes this to any
  localization of the plane; `FormallyUnramified.of_equiv` transfers it
  along the plane-ring iso to `B_q`, which is `Algebra.IsUnramifiedAt A q`.
* `Ideal.ramificationIdx_eq_one_of_isUnramifiedAt` then gives `e(q|A) = 1`,
  granted `[EssFiniteType A B]` (available from K1-L12's `Module.Finite`
  via `Module.Finite.finiteType` and `EssFiniteType.of_finiteType`).

The plane-ring locus is the ring-theoretic form of the ZMT/open set `U`:
primes of `B` at which a localization of `k[x,y]` is isomorphic to `B_q`.
The `IsLocalization` packaging is recorded as an equivalent generator of
the same locus.
-/

noncomputable section

open Algebra

namespace KeystoneGraph

/-! ## Abstract plane-ring locus -/

section PlaneRingLocus

variable (A B R : Type*) [CommRing A] [CommRing B] [CommRing R]
variable [Algebra A B] [Algebra A R]

/-- A prime `q` of `B` lies in the **plane-ring locus** relative to an ambient
plane ring `R` when `B_q` receives an `A`-algebra isomorphism from some
localization of `R`.

In Keystone 1, `R = k[x,y]` and `B` is the integral closure of `A = k[P,Q]`
in the plane, so this is the ZMT/open locus `U ⊆ Spec B` on which the graph
algebra localizes to agree with the plane. -/
def IsPlaneRingLocus (q : Ideal B) [q.IsPrime] : Prop :=
  ∃ M : Submonoid R, Nonempty (Localization M ≃ₐ[A] Localization.AtPrime q)

/-- The plane-ring locus as a subset of `Spec B`. -/
def planeRingLocus : Set (PrimeSpectrum B) :=
  { q | IsPlaneRingLocus A B R q.asIdeal }

/-- The forbidden étale box: primes in the plane-ring locus with ramification
index strictly greater than one. -/
def etaleBox : Set (PrimeSpectrum B) :=
  { q | IsPlaneRingLocus A B R q.asIdeal ∧ 1 < q.asIdeal.ramificationIdx A }

/-- The `IsLocalization` packaging of the plane-ring locus: if `B_q` *is* a
localization of the plane ring, it receives the canonical iso from
`Localization M`. -/
theorem isPlaneRingLocus_of_isLocalization
    {q : Ideal B} [q.IsPrime] (M : Submonoid R)
    [Algebra R (Localization.AtPrime q)]
    [IsScalarTower A R (Localization.AtPrime q)]
    [IsLocalization M (Localization.AtPrime q)] :
    IsPlaneRingLocus A B R q :=
  ⟨M, ⟨(IsLocalization.algEquiv M (Localization M)
      (Localization.AtPrime q)).restrictScalars A⟩⟩

variable {A B R}

/-- Localizations of a formally unramified algebra remain formally unramified.
This is the explicit `of_isLocalization` + `comp` expansion of the library
instance. -/
theorem formallyUnramified_localization (M : Submonoid R)
    [FormallyUnramified A R] :
    FormallyUnramified A (Localization M) :=
  have : FormallyUnramified R (Localization M) :=
    FormallyUnramified.of_isLocalization (Rₘ := Localization M) M
  FormallyUnramified.comp A R (Localization M)

/-- If `B_q` receives an iso from a localization of a formally unramified
`A`-algebra, then `A` is unramified at `q`. -/
theorem isUnramifiedAt_of_localization_iso {q : Ideal B} [q.IsPrime]
    [FormallyUnramified A R] {M : Submonoid R}
    (e : Localization M ≃ₐ[A] Localization.AtPrime q) :
    IsUnramifiedAt A q :=
  have : FormallyUnramified A (Localization M) :=
    formallyUnramified_localization (A := A) (R := R) M
  FormallyUnramified.of_equiv e

/-- Plane-ring locus primes are unramified. -/
theorem isUnramifiedAt_of_isPlaneRingLocus {q : Ideal B} [q.IsPrime]
    [FormallyUnramified A R] (h : IsPlaneRingLocus A B R q) :
    IsUnramifiedAt A q := by
  obtain ⟨M, ⟨e⟩⟩ := h
  exact isUnramifiedAt_of_localization_iso (R := R) e

/-- **Ramification index 1 on the plane-ring locus.** -/
theorem ramificationIdx_eq_one_of_isPlaneRingLocus {q : Ideal B} [q.IsPrime]
    [FormallyUnramified A R] [EssFiniteType A B]
    (h : IsPlaneRingLocus A B R q) :
    q.ramificationIdx A = 1 := by
  have : IsUnramifiedAt A q := isUnramifiedAt_of_isPlaneRingLocus (R := R) h
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

/-- **The étale box `(U, e > 1)` is empty.** -/
theorem etaleBox_eq_empty [FormallyUnramified A R] [EssFiniteType A B] :
    etaleBox A B R = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro q ⟨hq, hlt⟩
  have hq1 := ramificationIdx_eq_one_of_isPlaneRingLocus (R := R) hq
  rw [hq1] at hlt
  exact Nat.lt_irrefl _ hlt

end PlaneRingLocus

/-! ## Keystone specialization: Keller pair

`A = k[P,Q]` is formally unramified in the plane by K1-L10. Instantiating
the abstract results at `R = k[x,y]` and an arbitrary `A`-algebra `B`
(in particular `B = integralClosure A k[x,y]`, finite over `A` by K1-L12)
empties the étale box. -/

section Keller

variable {k : Type*} [Field k] {P Q : Plane k}
variable {B : Type*} [CommRing B] [Algebra (coordSubalgebra P Q) B]

/-- Plane-ring-locus primes of any `k[P,Q]`-algebra have ramification index
`1` over `k[P,Q]`. -/
theorem IsKellerPair.ramificationIdx_eq_one_of_mem_planeRingLocus
    (hPQ : IsKellerPair P Q)
    [EssFiniteType (coordSubalgebra P Q) B]
    {q : Ideal B} [q.IsPrime]
    (h : KeystoneGraph.IsPlaneRingLocus (coordSubalgebra P Q) B (Plane k) q) :
    q.ramificationIdx (coordSubalgebra P Q) = 1 :=
  have := hPQ.formallyUnramified
  KeystoneGraph.ramificationIdx_eq_one_of_isPlaneRingLocus
    (A := coordSubalgebra P Q) (B := B) (R := Plane k) h

/-- Box `(U, e > 1)` is empty for a Keller pair. -/
theorem IsKellerPair.etaleBox_eq_empty (hPQ : IsKellerPair P Q)
    [EssFiniteType (coordSubalgebra P Q) B] :
    KeystoneGraph.etaleBox (coordSubalgebra P Q) B (Plane k) = ∅ :=
  have := hPQ.formallyUnramified
  KeystoneGraph.etaleBox_eq_empty
    (A := coordSubalgebra P Q) (B := B) (R := Plane k)

end Keller

#print axioms formallyUnramified_localization
#print axioms isUnramifiedAt_of_localization_iso
#print axioms isUnramifiedAt_of_isPlaneRingLocus
#print axioms ramificationIdx_eq_one_of_isPlaneRingLocus
#print axioms etaleBox_eq_empty
#print axioms isPlaneRingLocus_of_isLocalization
#print axioms IsKellerPair.ramificationIdx_eq_one_of_mem_planeRingLocus
#print axioms IsKellerPair.etaleBox_eq_empty

end KeystoneGraph
