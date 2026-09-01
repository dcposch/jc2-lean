/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch (direction), Claude / Anthropic and Grok / xAI
agents (formalization)
-/
import KeystoneGraph.Setup
import KeystoneGraph.AlgebraicIndependence
import KeystoneGraph.IntegralClosureFinite

/-!
# K1-L13: height-one localization is a DVR; the graph is free of rank `d`

Let `A` be a Noetherian integrally closed domain and `𝔭` a height-one prime.
The localization `A_𝔭` is a discrete valuation ring: it is a Noetherian local
domain, not a field, integrally closed, of Krull dimension 1, hence Dedekind
and local, hence a DVR.

Writing `B_𝔭` for the localization of an `A`-algebra `B` at the image of
`A \ 𝔭` (equivalently, for the integral closure of `A_𝔭` in a finite
separable extension of `Frac(A)`), one obtains:

* `B_𝔭` is a finite free `A_𝔭`-module of rank `d = [L : K]`;
* `B_𝔭` is Noetherian, integrally closed, and a Dedekind domain.

Flatness of `B` over `A` at the generic point of a branch follows
immediately (`Module.Free` implies `Module.Flat`).

Consumables: `Ideal.eq_span_singleton_of_height_eq_one` /
`UniqueFactorizationMonoid.isPrincipal_of_height_eq_one` (UFD shortcut),
`IsDiscreteValuationRing.TFAE`, `isIntegrallyClosed_of_isLocalization`,
`IsLocalization.AtPrime.ringKrullDim_eq_height`,
`Module.free_of_finite_type_torsion_free'`,
`IsIntegralClosure.module_free`, `IsIntegralClosure.rank`,
`IsIntegralClosure.isDedekindDomain`.
-/

noncomputable section

open Algebra IsLocalRing
open scoped nonZeroDivisors

namespace KeystoneGraph

variable {A : Type*} [CommRing A] [IsDomain A]

/-! ## Localization of `B` as an `A_𝔭`-algebra -/

/-- Localization of an `A`-algebra `B` at the image of `A \ 𝔭`. This is the
standard `B_𝔭 := B ⊗[A] A_𝔭`. -/
abbrev locOver (B : Type*) [CommRing B] [Algebra A B] (p : Ideal A) [p.IsPrime] : Type _ :=
  Localization (Algebra.algebraMapSubmonoid B p.primeCompl)

/-! ## Height-one localization of a normal Noetherian domain is a DVR -/

/-- The unique nonzero prime of a height-one localization is the maximal
ideal. Used to feed `IsDiscreteValuationRing.TFAE` item 3. -/
theorem unique_nonzero_prime_locAt [IsNoetherianRing A]
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    ∃! P : Ideal (Localization.AtPrime p), P ≠ ⊥ ∧ P.IsPrime := by
  have hnf : ¬IsField (Localization.AtPrime p) :=
    IsLocalization.AtPrime.not_isField A (Ideal.ne_bot_of_height_eq_one hp) _
  haveI : Ring.KrullDimLE 1 (Localization.AtPrime p) := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height p
      (Localization.AtPrime p), hp]
    exact le_rfl
  refine ⟨maximalIdeal (Localization.AtPrime p),
    ⟨IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hnf, inferInstance⟩, ?_⟩
  intro Q hQ
  exact eq_maximalIdeal (hQ.2.isMaximal_of_ne_bot hQ.1)

/-- Height-one localization of a Noetherian integrally closed domain is a
discrete valuation ring.

Route: `A_𝔭` is a Noetherian local domain, not a field (height 1), integrally
closed (`isIntegrallyClosed_of_isLocalization`), of Krull dimension 1, hence
Dedekind; a local Dedekind domain that is not a field is a DVR. -/
theorem isDiscreteValuationRing_locAt [IsNoetherianRing A] [IsIntegrallyClosed A]
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  have hnf : ¬IsField (Localization.AtPrime p) :=
    IsLocalization.AtPrime.not_isField A (Ideal.ne_bot_of_height_eq_one hp) _
  haveI : IsIntegrallyClosed (Localization.AtPrime p) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime p) p.primeCompl
      p.primeCompl_le_nonZeroDivisors
  haveI : Ring.KrullDimLE 1 (Localization.AtPrime p) := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height p
      (Localization.AtPrime p), hp]
    exact le_rfl
  haveI : Ring.DimensionLEOne (Localization.AtPrime p) :=
    { maximalOfPrime := fun hne hprime => hprime.isMaximal_of_ne_bot hne }
  haveI : IsDedekindRing (Localization.AtPrime p) :=
    { toIsNoetherian := inferInstance
      toDimensionLEOne := inferInstance
      toIsIntegralClosure := inferInstance }
  haveI : IsDedekindDomain (Localization.AtPrime p) := inferInstance
  haveI : IsPrincipalIdealRing (Localization.AtPrime p) := inferInstance
  exact { not_a_field' := IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hnf }

/-- UFD shortcut: a height-one prime is principal
(`UniqueFactorizationMonoid.isPrincipal_of_height_eq_one`, via
`Ideal.eq_span_singleton_of_height_eq_one`), so the same conclusion holds
for a Noetherian UFD. -/
theorem isDiscreteValuationRing_locAt_of_ufd [IsNoetherianRing A]
    [UniqueFactorizationMonoid A] (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime p) :=
  isDiscreteValuationRing_locAt p hp

/-- A height-one localization of a normal Noetherian domain is a PID. -/
theorem isPrincipalIdealRing_locAt [IsNoetherianRing A] [IsIntegrallyClosed A]
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    IsPrincipalIdealRing (Localization.AtPrime p) :=
  have := isDiscreteValuationRing_locAt p hp
  inferInstance

/-- A height-one localization of a normal Noetherian domain is Dedekind. -/
theorem isDedekindDomain_locAt [IsNoetherianRing A] [IsIntegrallyClosed A]
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    IsDedekindDomain (Localization.AtPrime p) :=
  have := isDiscreteValuationRing_locAt p hp
  inferInstance

/-! ## `B_𝔭` is free of finite rank over the DVR `A_𝔭` -/

/-- The image of `A \ 𝔭` in `B` consists of non-zero-divisors, so the
localization `B_𝔭` is a domain. -/
theorem algebraMapSubmonoid_primeCompl_le_nonZeroDivisors
    {B : Type*} [CommRing B] [IsDomain B] [Algebra A B] [Module.IsTorsionFree A B]
    (p : Ideal A) [p.IsPrime] :
    Algebra.algebraMapSubmonoid B p.primeCompl ≤ nonZeroDivisors B :=
  Submonoid.map_le_of_le_comap _ <| p.primeCompl_le_nonZeroDivisors.trans
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (FaithfulSMul.algebraMap_injective A B))

/-- `B_𝔭` is a finite free module over the DVR `A_𝔭`. Finite type is
preserved by localization; torsion-freeness is preserved by localization;
a finite torsion-free module over a PID is free. -/
theorem moduleFree_locOver [IsNoetherianRing A] [IsIntegrallyClosed A]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    Module.Free (Localization.AtPrime p) (locOver (A := A) B p) := by
  haveI := isPrincipalIdealRing_locAt p hp
  exact Module.free_of_finite_type_torsion_free'

/-- Flatness of `B` over `A` at a height-one prime: free modules are flat. -/
theorem moduleFlat_locOver [IsNoetherianRing A] [IsIntegrallyClosed A]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    Module.Flat (Localization.AtPrime p) (locOver (A := A) B p) := by
  haveI := moduleFree_locOver (B := B) p hp
  exact inferInstance

/-- `B_𝔭` is a Noetherian ring. -/
theorem isNoetherianRing_locOver {B : Type*} [CommRing B] [IsDomain B] [Algebra A B]
    [IsNoetherianRing B] (p : Ideal A) [p.IsPrime] :
    IsNoetherianRing (locOver (A := A) B p) :=
  IsLocalization.isNoetherianRing (Algebra.algebraMapSubmonoid B p.primeCompl) _ ‹_›

/-- `B_𝔭` is integrally closed, as a localization of an integrally closed domain. -/
theorem isIntegrallyClosed_locOver {B : Type*} [CommRing B] [IsDomain B] [Algebra A B]
    [IsIntegrallyClosed B] [Module.IsTorsionFree A B]
    (p : Ideal A) [p.IsPrime] :
    IsIntegrallyClosed (locOver (A := A) B p) :=
  isIntegrallyClosed_of_isLocalization (locOver (A := A) B p)
    (Algebra.algebraMapSubmonoid B p.primeCompl)
    (algebraMapSubmonoid_primeCompl_le_nonZeroDivisors p)

/-- `B_𝔭` is a Dedekind domain: Noetherian, integrally closed, and of
dimension `≤ 1` as a finite (hence integral) algebra over the DVR `A_𝔭`. -/
theorem isDedekindDomain_locOver [IsNoetherianRing A] [IsIntegrallyClosed A]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B] [IsIntegrallyClosed B] [IsNoetherianRing B]
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    IsDedekindDomain (locOver (A := A) B p) := by
  haveI := isDiscreteValuationRing_locAt p hp
  haveI : IsDomain (locOver (A := A) B p) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _
      (algebraMapSubmonoid_primeCompl_le_nonZeroDivisors (B := B) p)
  haveI : IsNoetherianRing (locOver (A := A) B p) := isNoetherianRing_locOver (B := B) p
  haveI : IsIntegrallyClosed (locOver (A := A) B p) :=
    isIntegrallyClosed_locOver (B := B) p
  haveI : Algebra.IsIntegral (Localization.AtPrime p) (locOver (A := A) B p) :=
    inferInstance
  haveI : Ring.DimensionLEOne (locOver (A := A) B p) :=
    Ring.DimensionLEOne.of_isIntegral (Localization.AtPrime p) (locOver (A := A) B p)
  haveI : IsDedekindRing (locOver (A := A) B p) :=
    { toIsNoetherian := inferInstance
      toDimensionLEOne := inferInstance
      toIsIntegralClosure := inferInstance }
  exact inferInstance

/-! ## Integral closure of `A_𝔭` in a finite separable extension -/

section LocAKLB

variable (A : Type*) (K : Type*) (L : Type*)
variable [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable (p : Ideal A) [p.IsPrime]

/-- Units: elements of `A \ 𝔭` become units in the fraction field. -/
theorem locAt_map_units (y : p.primeCompl) : IsUnit (algebraMap A K y) :=
  IsLocalization.map_units (M := A⁰) K ⟨y, p.primeCompl_le_nonZeroDivisors y.2⟩

/-- Canonical algebra `A_𝔭 → K`. -/
def algebra_locAt_fraction : Algebra (Localization.AtPrime p) K :=
  (IsLocalization.lift (locAt_map_units A K p)).toAlgebra

/-- Canonical algebra `A_𝔭 → L` through `K`. -/
def algebra_locAt_extension : Algebra (Localization.AtPrime p) L :=
  letI := algebra_locAt_fraction A K p
  ((algebraMap K L).comp (algebraMap (Localization.AtPrime p) K)).toAlgebra

/-- The integral closure of `A_𝔭` in `L` is a free `A_𝔭`-module. -/
theorem moduleFree_integralClosure_locAt
    [Algebra (Localization.AtPrime p) K] [IsScalarTower A (Localization.AtPrime p) K]
    [Algebra (Localization.AtPrime p) L] [IsScalarTower (Localization.AtPrime p) K L]
    [IsScalarTower A (Localization.AtPrime p) L]
    [IsFractionRing (Localization.AtPrime p) K]
    (hp : p.height = 1) :
    Module.Free (Localization.AtPrime p) (integralClosure (Localization.AtPrime p) L) := by
  haveI := isDiscreteValuationRing_locAt p hp
  haveI : Module.IsTorsionFree (Localization.AtPrime p) L :=
    Module.IsTorsionFree.trans_faithfulSMul (R := Localization.AtPrime p) (A := K) (M := L)
  exact IsIntegralClosure.module_free (Localization.AtPrime p) K L
    (integralClosure (Localization.AtPrime p) L)

/-- The `A_𝔭`-rank of the integral closure equals `[L : K]`. -/
theorem finrank_integralClosure_locAt
    [Algebra (Localization.AtPrime p) K] [IsScalarTower A (Localization.AtPrime p) K]
    [Algebra (Localization.AtPrime p) L] [IsScalarTower (Localization.AtPrime p) K L]
    [IsScalarTower A (Localization.AtPrime p) L]
    [IsFractionRing (Localization.AtPrime p) K]
    (hp : p.height = 1) :
    Module.finrank (Localization.AtPrime p) (integralClosure (Localization.AtPrime p) L) =
      Module.finrank K L := by
  haveI := isDiscreteValuationRing_locAt p hp
  haveI : Module.IsTorsionFree (Localization.AtPrime p) L :=
    Module.IsTorsionFree.trans_faithfulSMul (R := Localization.AtPrime p) (A := K) (M := L)
  exact IsIntegralClosure.rank (Localization.AtPrime p) K L
    (integralClosure (Localization.AtPrime p) L)

/-- The integral closure of `A_𝔭` in `L` is a Dedekind domain. -/
theorem isDedekindDomain_integralClosure_locAt
    [Algebra (Localization.AtPrime p) K] [IsScalarTower A (Localization.AtPrime p) K]
    [Algebra (Localization.AtPrime p) L] [IsScalarTower (Localization.AtPrime p) K L]
    [IsScalarTower A (Localization.AtPrime p) L]
    [IsFractionRing (Localization.AtPrime p) K]
    (hp : p.height = 1) :
    IsDedekindDomain (integralClosure (Localization.AtPrime p) L) := by
  haveI := isDedekindDomain_locAt p hp
  exact IsIntegralClosure.isDedekindDomain (Localization.AtPrime p) K L
    (integralClosure (Localization.AtPrime p) L)

/-- The integral closure of `A_𝔭` in `L` is a Noetherian ring. -/
theorem isNoetherianRing_integralClosure_locAt
    [Algebra (Localization.AtPrime p) K] [IsScalarTower A (Localization.AtPrime p) K]
    [Algebra (Localization.AtPrime p) L] [IsScalarTower (Localization.AtPrime p) K L]
    [IsScalarTower A (Localization.AtPrime p) L]
    [IsFractionRing (Localization.AtPrime p) K]
    (hp : p.height = 1) :
    IsNoetherianRing (integralClosure (Localization.AtPrime p) L) := by
  haveI := isDiscreteValuationRing_locAt p hp
  exact IsIntegralClosure.isNoetherianRing (Localization.AtPrime p) K L
    (integralClosure (Localization.AtPrime p) L)

/-- The integral closure of `A_𝔭` in `L` is integrally closed. -/
theorem isIntegrallyClosed_integralClosure_locAt
    [Algebra (Localization.AtPrime p) K]
    [IsScalarTower A (Localization.AtPrime p) K]
    [Algebra (Localization.AtPrime p) L]
    [IsScalarTower (Localization.AtPrime p) K L]
    [IsFractionRing (Localization.AtPrime p) K] :
    IsIntegrallyClosed (integralClosure (Localization.AtPrime p) L) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension (K := K)

end LocAKLB

/-! ## Keystone specialization: `k[P,Q]_𝔭` is a DVR and `B_𝔭` is free of rank `d` -/

section Keller

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
variable {P Q : Plane k}

theorem IsKellerPair.isNoetherianRing_coordRing (hPQ : IsKellerPair P Q) :
    IsNoetherianRing (coordRing P Q) :=
  coordRing_isNoetherianRing (IsKellerPair.coordRingEquivMvPolynomial hPQ)

theorem IsKellerPair.isIntegrallyClosed_coordRing (hPQ : IsKellerPair P Q) :
    IsIntegrallyClosed (coordRing P Q) :=
  coordRing_isIntegrallyClosed (IsKellerPair.coordRingEquivMvPolynomial hPQ)

theorem IsKellerPair.uniqueFactorizationMonoid_coordRing (hPQ : IsKellerPair P Q) :
    UniqueFactorizationMonoid (coordRing P Q) :=
  coordRing_uniqueFactorizationMonoid (IsKellerPair.coordRingEquivMvPolynomial hPQ)

/-- Height-one localization of `k[P,Q]` is a DVR. -/
theorem IsKellerPair.isDiscreteValuationRing_locAt (hPQ : IsKellerPair P Q)
    (p : Ideal (coordRing P Q)) [p.IsPrime] (hp : p.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime p) :=
  have := IsKellerPair.isNoetherianRing_coordRing hPQ
  have := IsKellerPair.isIntegrallyClosed_coordRing hPQ
  KeystoneGraph.isDiscreteValuationRing_locAt p hp

/-- The localized graph algebra `B_𝔭` is free over `A_𝔭`. -/
theorem IsKellerPair.moduleFree_locOver (hPQ : IsKellerPair P Q)
    (p : Ideal (coordRing P Q)) [p.IsPrime] (hp : p.height = 1) :
    Module.Free (Localization.AtPrime p)
      (locOver (A := coordRing P Q) (integralClosureInPlane P Q) p) := by
  haveI := IsKellerPair.isNoetherianRing_coordRing hPQ
  haveI := IsKellerPair.isIntegrallyClosed_coordRing hPQ
  haveI := hPQ.finiteDimensional_fractionRings
  haveI := hPQ.isSeparable_fractionRings
  haveI : Module.Finite (coordRing P Q) (integralClosureInPlane P Q) :=
    moduleFinite_integralClosure (coordRing P Q) (FractionRing (coordRing P Q))
      (FractionRing (Plane k)) (Plane k)
  haveI : Module.IsTorsionFree (coordRing P Q) (integralClosureInPlane P Q) :=
    inferInstance
  exact KeystoneGraph.moduleFree_locOver (B := integralClosureInPlane P Q) p hp

/-- The localized graph algebra is a Dedekind domain. -/
theorem IsKellerPair.isDedekindDomain_locOver (hPQ : IsKellerPair P Q)
    (p : Ideal (coordRing P Q)) [p.IsPrime] (hp : p.height = 1) :
    IsDedekindDomain
      (locOver (A := coordRing P Q) (integralClosureInPlane P Q) p) := by
  haveI := IsKellerPair.isNoetherianRing_coordRing hPQ
  haveI := IsKellerPair.isIntegrallyClosed_coordRing hPQ
  haveI := hPQ.finiteDimensional_fractionRings
  haveI := hPQ.isSeparable_fractionRings
  haveI : Module.Finite (coordRing P Q) (integralClosureInPlane P Q) :=
    moduleFinite_integralClosure (coordRing P Q) (FractionRing (coordRing P Q))
      (FractionRing (Plane k)) (Plane k)
  haveI : IsNoetherianRing (integralClosureInPlane P Q) :=
    isNoetherianRing_integralClosure (coordRing P Q) (FractionRing (coordRing P Q))
      (FractionRing (Plane k)) (Plane k)
  haveI : IsIntegrallyClosed (integralClosureInPlane P Q) :=
    isIntegrallyClosed_integralClosure (coordRing P Q) (FractionRing (coordRing P Q))
      (FractionRing (Plane k)) (Plane k)
  haveI : Module.IsTorsionFree (coordRing P Q) (integralClosureInPlane P Q) :=
    inferInstance
  exact KeystoneGraph.isDedekindDomain_locOver (B := integralClosureInPlane P Q) p hp

/-- Rank of the localized integral closure equals the geometric degree `d`. -/
theorem IsKellerPair.finrank_integralClosure_locAt (hPQ : IsKellerPair P Q)
    (p : Ideal (coordRing P Q)) [p.IsPrime] (hp : p.height = 1) :
    letI : Algebra (Localization.AtPrime p) (FractionRing (Plane k)) :=
      ((algebraMap (FractionRing (coordRing P Q)) (FractionRing (Plane k))).comp
        (algebraMap (Localization.AtPrime p) (FractionRing (coordRing P Q)))).toAlgebra
    Module.finrank (Localization.AtPrime p)
        (integralClosure (Localization.AtPrime p) (FractionRing (Plane k))) =
      hPQ.kellerDegree := by
  letI : Algebra (Localization.AtPrime p) (FractionRing (Plane k)) :=
    ((algebraMap (FractionRing (coordRing P Q)) (FractionRing (Plane k))).comp
      (algebraMap (Localization.AtPrime p) (FractionRing (coordRing P Q)))).toAlgebra
  haveI := IsKellerPair.isNoetherianRing_coordRing hPQ
  haveI := IsKellerPair.isIntegrallyClosed_coordRing hPQ
  haveI := hPQ.finiteDimensional_fractionRings
  haveI := hPQ.isSeparable_fractionRings
  haveI : IsScalarTower (Localization.AtPrime p) (FractionRing (coordRing P Q))
      (FractionRing (Plane k)) := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (coordRing P Q) (Localization.AtPrime p)
      (FractionRing (Plane k)) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply (coordRing P Q) (FractionRing (coordRing P Q))
        (FractionRing (Plane k))]
      rw [IsScalarTower.algebraMap_apply (coordRing P Q) (Localization.AtPrime p)
        (FractionRing (coordRing P Q))]
      rfl
  exact (KeystoneGraph.finrank_integralClosure_locAt (coordRing P Q)
      (FractionRing (coordRing P Q)) (FractionRing (Plane k)) p hp).trans
    (IsKellerPair.kellerDegree_eq_finrank hPQ).symm

end Keller

end KeystoneGraph

#print axioms KeystoneGraph.unique_nonzero_prime_locAt
#print axioms KeystoneGraph.isDiscreteValuationRing_locAt
#print axioms KeystoneGraph.isDiscreteValuationRing_locAt_of_ufd
#print axioms KeystoneGraph.isPrincipalIdealRing_locAt
#print axioms KeystoneGraph.isDedekindDomain_locAt
#print axioms KeystoneGraph.moduleFree_locOver
#print axioms KeystoneGraph.moduleFlat_locOver
#print axioms KeystoneGraph.isNoetherianRing_locOver
#print axioms KeystoneGraph.isIntegrallyClosed_locOver
#print axioms KeystoneGraph.isDedekindDomain_locOver
#print axioms KeystoneGraph.moduleFree_integralClosure_locAt
#print axioms KeystoneGraph.finrank_integralClosure_locAt
#print axioms KeystoneGraph.isDedekindDomain_integralClosure_locAt
#print axioms KeystoneGraph.isNoetherianRing_integralClosure_locAt
#print axioms KeystoneGraph.isIntegrallyClosed_integralClosure_locAt
#print axioms KeystoneGraph.IsKellerPair.isDiscreteValuationRing_locAt
#print axioms KeystoneGraph.IsKellerPair.moduleFree_locOver
#print axioms KeystoneGraph.IsKellerPair.isDedekindDomain_locOver
#print axioms KeystoneGraph.IsKellerPair.finrank_integralClosure_locAt
