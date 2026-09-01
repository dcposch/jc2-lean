/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch (direction), Claude / Anthropic and Grok / xAI
agents (formalization)
-/
import KeystoneGraph.Setup

/-!
# K1-L12: finiteness and normality of the integral closure

Let `A` be a Noetherian integrally closed domain with fraction field `K`,
let `L / K` be finite separable, and let `R` be an integrally closed
domain (in the plane case: a UFD) with fraction field `L` containing `A`.
Writing `B := integralClosure A R`, we obtain

* `A ⊆ B ⊆ R` (`B` lands in `R` because `R` is integrally closed in `L`);
* `B ≃ₐ[A] integralClosure A L`;
* `Module.Finite A B`, `IsNoetherian A B`, `IsNoetherianRing B`;
* `IsIntegrallyClosed B`; `IsFractionRing (integralClosure A L) L`
  (hence `IsFractionRing B L` via `equivIntegralClosure`).

The identification `k[P,Q] ≃ₐ MvPolynomial (Fin 2) k` is the K1-L11
(`ALGIND`) conclusion and is a **section hypothesis** on the Keystone
specialization, to be discharged when that lane lands. The core lemmas
run over an abstract Noetherian integrally closed base.

Consumables: `IsIntegralClosure.finite`, `IsIntegralClosure.isNoetherian`,
`IsIntegralClosure.isNoetherianRing`,
`UniqueFactorizationMonoid.instIsIntegrallyClosed`,
`MvPolynomial.uniqueFactorizationMonoid`,
`IsIntegralClosure.isFractionRing_of_finite_extension`.
-/

noncomputable section

open Algebra Polynomial
open scoped nonZeroDivisors

namespace KeystoneGraph

/-! ## The plane is a UFD, hence integrally closed -/

section PlaneUFD

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Multivariate polynomials over a field (in particular the plane) form a
UFD. This is `MvPolynomial.uniqueFactorizationMonoid`. -/
instance instUniqueFactorizationMonoid_plane : UniqueFactorizationMonoid (Plane k) :=
  inferInstance

/-- A UFD is integrally closed (`UniqueFactorizationMonoid.instIsIntegrallyClosed`). -/
instance instIsIntegrallyClosed_plane : IsIntegrallyClosed (Plane k) :=
  UniqueFactorizationMonoid.instIsIntegrallyClosed

end PlaneUFD

/-! ## Abstract landing: `B = integralClosure A R` inside a normal ambient -/

section Ambient

variable (A R L : Type*) [CommRing A] [CommRing R] [Field L]
variable [Algebra A R] [Algebra R L] [Algebra A L] [IsScalarTower A R L]
variable [IsFractionRing R L] [IsIntegrallyClosed R]

/-- The image of `A` in `R` lands in `B = integralClosure A R`. -/
theorem algebraMap_mem_integralClosure (x : A) :
    algebraMap A R x ∈ integralClosure A R :=
  Subalgebra.algebraMap_mem _ x

/-- `A ⊆ B` as subalgebras of `R`. -/
theorem bot_le_integralClosure : (⊥ : Subalgebra A R) ≤ integralClosure A R :=
  bot_le

/-- `B ⊆ R` as subalgebras of `R`. -/
theorem integralClosure_le_top : integralClosure A R ≤ ⊤ :=
  le_top

/-- Because `R` is integrally closed in `L`, an element of `L` integral over
`A` already lies in `R`. -/
theorem integralClosure_subset_range_algebraMap :
    (integralClosure A L : Set L) ⊆ Set.range (algebraMap R L) := by
  intro x hx
  have hxR : IsIntegral R x := IsIntegral.tower_top (A := R) hx
  obtain ⟨y, rfl⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := R) (A := L)).mp hxR
  exact ⟨y, rfl⟩

/-- Restriction of `R → L` to integral closures. -/
def toIntegralClosureHom :
    integralClosure A R →ₐ[A] integralClosure A L where
  toFun x := ⟨algebraMap R L (x : R), x.2.map (IsScalarTower.toAlgHom A R L)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)
  commutes' a :=
    Subtype.ext (IsScalarTower.algebraMap_apply A R L a).symm

theorem toIntegralClosureHom_apply (x : integralClosure A R) :
    (toIntegralClosureHom A R L x : L) = algebraMap R L (x : R) :=
  rfl

theorem toIntegralClosureHom_injective :
    Function.Injective (toIntegralClosureHom A R L) := by
  intro x y h
  refine Subtype.ext ?_
  exact IsFractionRing.injective R L (congrArg Subtype.val h)

theorem toIntegralClosureHom_surjective :
    Function.Surjective (toIntegralClosureHom A R L) := by
  intro y
  obtain ⟨r, hr⟩ := integralClosure_subset_range_algebraMap A R L y.2
  have hr_int : IsIntegral A r := by
    obtain ⟨p, hp, hpy⟩ := show IsIntegral A (algebraMap R L r) from hr ▸ y.2
    refine ⟨p, hp, ?_⟩
    exact (aeval_algebraMap_eq_zero_iff_of_injective
      (IsFractionRing.injective R L)).mp hpy
  refine ⟨⟨r, hr_int⟩, Subtype.ext ?_⟩
  simp [toIntegralClosureHom_apply, hr]

/-- Identification `integralClosure A R ≃ₐ[A] integralClosure A L`. -/
def equivIntegralClosure : integralClosure A R ≃ₐ[A] integralClosure A L :=
  AlgEquiv.ofBijective (toIntegralClosureHom A R L)
    ⟨toIntegralClosureHom_injective A R L, toIntegralClosureHom_surjective A R L⟩

end Ambient

/-! ## Finiteness and normality via the AKLB package on `integralClosure A L` -/

section FiniteNormal

variable (A K L R : Type*)
variable [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable [CommRing R] [IsDomain R] [Algebra A R]
variable [Algebra R L] [IsScalarTower A R L] [IsFractionRing R L]
variable [IsIntegrallyClosed R]

include K L
open IsIntegralClosure (isFractionRing_of_finite_extension)

/-- `B` is a finite `A`-module. -/
theorem moduleFinite_integralClosure : Module.Finite A (integralClosure A R) :=
  have : Module.Finite A (integralClosure A L) :=
    IsIntegralClosure.finite A K L (integralClosure A L)
  Module.Finite.equiv (equivIntegralClosure A R L).symm.toLinearEquiv

/-- `B` is Noetherian as an `A`-module. -/
theorem isNoetherian_integralClosure : IsNoetherian A (integralClosure A R) :=
  have : IsNoetherian A (integralClosure A L) :=
    IsIntegralClosure.isNoetherian A K L (integralClosure A L)
  (equivIntegralClosure A R L).toLinearEquiv.symm.isNoetherian_iff.mp this

/-- `B` is a Noetherian ring. -/
theorem isNoetherianRing_integralClosure : IsNoetherianRing (integralClosure A R) :=
  have : IsNoetherianRing (integralClosure A L) :=
    IsIntegralClosure.isNoetherianRing A K L (integralClosure A L)
  isNoetherianRing_of_ringEquiv (integralClosure A L)
    (equivIntegralClosure A R L).symm.toRingEquiv

/-- `B` is integrally closed. -/
theorem isIntegrallyClosed_integralClosure : IsIntegrallyClosed (integralClosure A R) :=
  have : IsIntegrallyClosed (integralClosure A L) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  IsIntegrallyClosed.of_equiv (equivIntegralClosure A R L).symm.toRingEquiv

/-- Algebra structure `B → L` through the ambient ring `R`. Priority is low so
the subtype algebra on `integralClosure A L` wins when both apply. -/
instance (priority := 50) algebra_integralClosure :
    Algebra (integralClosure A R) L :=
  ((algebraMap R L).comp (algebraMap (integralClosure A R) R)).toAlgebra

/-- `L` is the fraction field of `integralClosure A L`. Combined with
`equivIntegralClosure`, this is `IsFractionRing B L`. -/
theorem isFractionRing_integralClosure_in_L :
    IsFractionRing (integralClosure A L) L :=
  isFractionRing_of_finite_extension A K L (integralClosure A L)

end FiniteNormal

/-! ## K1-L11 hypotheses: `k[P,Q]` is a polynomial ring in two variables -/

section CoordFromL11

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
variable {P Q : Plane k}

/-- Transfer Noetherianity along the K1-L11 polynomial identification. -/
theorem coordRing_isNoetherianRing
    (e : coordRing P Q ≃ₐ[k] MvPolynomial (Fin 2) k) :
    IsNoetherianRing (coordRing P Q) :=
  isNoetherianRing_of_ringEquiv (MvPolynomial (Fin 2) k) e.symm.toRingEquiv

/-- Transfer unique factorization along the K1-L11 polynomial identification. -/
theorem coordRing_uniqueFactorizationMonoid
    (e : coordRing P Q ≃ₐ[k] MvPolynomial (Fin 2) k) :
    UniqueFactorizationMonoid (coordRing P Q) :=
  e.symm.toMulEquiv.uniqueFactorizationMonoid inferInstance

/-- Transfer integral closedness along the K1-L11 polynomial identification. -/
theorem coordRing_isIntegrallyClosed
    (e : coordRing P Q ≃ₐ[k] MvPolynomial (Fin 2) k) :
    IsIntegrallyClosed (coordRing P Q) :=
  IsIntegrallyClosed.of_equiv e.symm.toRingEquiv

end CoordFromL11

end KeystoneGraph

#print axioms KeystoneGraph.instUniqueFactorizationMonoid_plane
#print axioms KeystoneGraph.instIsIntegrallyClosed_plane
#print axioms KeystoneGraph.algebraMap_mem_integralClosure
#print axioms KeystoneGraph.bot_le_integralClosure
#print axioms KeystoneGraph.integralClosure_le_top
#print axioms KeystoneGraph.integralClosure_subset_range_algebraMap
#print axioms KeystoneGraph.toIntegralClosureHom
#print axioms KeystoneGraph.toIntegralClosureHom_injective
#print axioms KeystoneGraph.toIntegralClosureHom_surjective
#print axioms KeystoneGraph.equivIntegralClosure
#print axioms KeystoneGraph.moduleFinite_integralClosure
#print axioms KeystoneGraph.isNoetherian_integralClosure
#print axioms KeystoneGraph.isNoetherianRing_integralClosure
#print axioms KeystoneGraph.isIntegrallyClosed_integralClosure
#print axioms KeystoneGraph.algebra_integralClosure
#print axioms KeystoneGraph.isFractionRing_integralClosure_in_L
#print axioms KeystoneGraph.coordRing_isNoetherianRing
#print axioms KeystoneGraph.coordRing_uniqueFactorizationMonoid
#print axioms KeystoneGraph.coordRing_isIntegrallyClosed
