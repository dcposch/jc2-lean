/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch (direction), Claude / Anthropic and Grok / xAI
agents (formalization)
-/
import KeystoneGraph.HeightOneLocalization

/-!
# K1-L14: the sum-of-`e f` law at a height-one prime

Let `A` be a Noetherian integrally closed domain and `B` a finite torsion-free
`A`-algebra. For a height-one prime `𝔭` of `A`, the localization `A_𝔭` is a
DVR (K1-L13) and `B_𝔭` is a finite free — hence finite flat — `A_𝔭`-module.
The finite-flat form of the fundamental identity therefore applies with no
Dedekind hypothesis on `A` or `B`:

```
∑ 𝔮 ∈ m.primesOver B_𝔭, e_𝔮 · f_𝔮 = finrank A_𝔭 B_𝔭
```

where `m` is the maximal ideal of the DVR `A_𝔭` (the extension of `𝔭`).
The rank equals the geometric degree `d = [Frac(B) : Frac(A)]`. In the
Keller specialization, `Frac(B) = k(x,y)`
(`isFractionRing_integralClosureInPlane`), so this is `kellerDegree`.

Consumables: `Ideal.sum_ramification_inertia_eq_finrank`
(`RingTheory/RamificationInertia/Basic.lean`, finite-flat form),
`Algebra.QuasiFinite.finite_primesOver`, the
`[Module.Finite R S] : QuasiFinite` instance, K1-L13
(`moduleFree_locOver` / `moduleFlat_locOver`),
`IsFractionRing.finrank_eq`.
-/

noncomputable section

open Algebra IsLocalRing IsLocalization
open scoped nonZeroDivisors

namespace KeystoneGraph

variable {A : Type*} [CommRing A] [IsDomain A]

/-! ## Finite-flat Σ `e f` at a height-one prime -/

/-- The maximal ideal of `A_𝔭` is the extension of `𝔭`. -/
theorem maximalIdeal_locAt_eq_map (p : Ideal A) [p.IsPrime] :
    maximalIdeal (Localization.AtPrime p) =
      p.map (algebraMap A (Localization.AtPrime p)) :=
  (IsLocalization.AtPrime.map_eq_maximalIdeal p _).symm

/-- `B_𝔭` is a finite `A_𝔭`-module: localization preserves finite generation. -/
instance moduleFinite_locOver {B : Type*} [CommRing B] [Algebra A B] [Module.Finite A B]
    (p : Ideal A) [p.IsPrime] :
    Module.Finite (Localization.AtPrime p) (locOver (A := A) B p) :=
  inferInstance

/-- Primes of `B_𝔭` over the closed point of `A_𝔭` form a finite type.
Quasi-finiteness is the `[Module.Finite] : QuasiFinite` instance, so this
does not need height one. -/
instance instFintypePrimesOverLocOver {B : Type*} [CommRing B] [Algebra A B] [Module.Finite A B]
    (p : Ideal A) [p.IsPrime] :
    Fintype ((maximalIdeal (Localization.AtPrime p)).primesOver (locOver (A := A) B p)) :=
  have : Finite
      ((maximalIdeal (Localization.AtPrime p)).primesOver (locOver (A := A) B p)) :=
    Algebra.QuasiFinite.finite_primesOver _
  Fintype.ofFinite _

/-- **Finite-flat Σ `e f` law.** For a height-one prime `𝔭` of a normal
Noetherian domain `A` and a finite torsion-free `A`-algebra `B`,

```
∑ 𝔮, e(𝔮 | A_𝔭) · f(𝔮 | A_𝔭) = finrank_{A_𝔭} B_𝔭
```

the sum running over primes of `B_𝔭` lying over the maximal ideal of the
DVR `A_𝔭`. Free of finite rank (K1-L13) supplies both `Module.Finite` and
`Module.Flat`; quasi-finiteness of the fibre supplies `Fintype`. -/
theorem sum_ramification_inertia_locOver [IsNoetherianRing A] [IsIntegrallyClosed A]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    ∑ q : (maximalIdeal (Localization.AtPrime p)).primesOver (locOver (A := A) B p),
        q.1.ramificationIdx (Localization.AtPrime p) *
          q.1.inertiaDeg (Localization.AtPrime p) =
      Module.finrank (Localization.AtPrime p) (locOver (A := A) B p) := by
  have := isDiscreteValuationRing_locAt p hp
  have := moduleFree_locOver (B := B) p hp
  have : Module.Flat (Localization.AtPrime p) (locOver (A := A) B p) :=
    moduleFlat_locOver (B := B) p hp
  exact Ideal.sum_ramification_inertia_eq_finrank _ _

/-! ## Rank identification: `finrank A_𝔭 B_𝔭 = [Frac(B) : Frac(A)]` -/

section Rank

variable {B : Type*} [CommRing B] [IsDomain B] [Algebra A B]
variable [Module.Finite A B] [Module.IsTorsionFree A B]

attribute [local instance] FractionRing.liftAlgebra

/-- Algebra `B_𝔭 → Frac(B)` by localizing the identity at `A \ 𝔭 ⊆ B⁰`. -/
instance instAlgebraLocOverFractionRing (p : Ideal A) [p.IsPrime] :
    Algebra (locOver (A := A) B p) (FractionRing B) :=
  Localization.AtPrime.liftAlgebra (S := B) (P := p)

instance instIsScalarTowerLocOverFractionRing (p : Ideal A) [p.IsPrime] :
    IsScalarTower B (locOver (A := A) B p) (FractionRing B) :=
  localization_isScalarTower_of_submonoid_le _ _ _ _
    (algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _
      p.primeCompl_le_nonZeroDivisors)

instance instIsFractionRingLocOver (p : Ideal A) [p.IsPrime] :
    IsFractionRing (locOver (A := A) B p) (FractionRing B) :=
  have : IsDomain (locOver (A := A) B p) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _
      (algebraMapSubmonoid_primeCompl_le_nonZeroDivisors (B := B) p)
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Algebra.algebraMapSubmonoid B p.primeCompl) _ _

/-- Algebra `A_𝔭 → Frac(B)` by lifting `A → Frac(B)` along `A \ 𝔭`. -/
instance instAlgebraLocAtFractionRingB (p : Ideal A) [p.IsPrime] :
    Algebra (Localization.AtPrime p) (FractionRing B) :=
  (IsLocalization.lift (M := p.primeCompl) (g := algebraMap A (FractionRing B)) fun y =>
    isUnit_iff_ne_zero.mpr fun hy0 =>
      y.2 <| by
        have hy : (y : A) = 0 :=
          FaithfulSMul.algebraMap_injective A (FractionRing B)
            (hy0.trans (map_zero (algebraMap A (FractionRing B))).symm)
        exact hy ▸ p.zero_mem).toAlgebra

instance instIsScalarTowerLocAtFractionRingB (p : Ideal A) [p.IsPrime] :
    IsScalarTower A (Localization.AtPrime p) (FractionRing B) :=
  IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm

instance instIsScalarTowerLocAtFractionRingAB (p : Ideal A) [p.IsPrime] :
    IsScalarTower (Localization.AtPrime p) (FractionRing A) (FractionRing B) :=
  IsScalarTower.of_algebraMap_eq' <|
    IsLocalization.ringHom_ext p.primeCompl <| by
      ext x
      simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply]

instance instIsScalarTowerLocOverFractionRing' (p : Ideal A) [p.IsPrime] :
    IsScalarTower (Localization.AtPrime p) (locOver (A := A) B p) (FractionRing B) := by
  refine IsScalarTower.of_algebraMap_eq' <| IsLocalization.ringHom_ext p.primeCompl ?_
  rw [RingHom.comp_assoc,
    ← IsScalarTower.algebraMap_eq A (Localization.AtPrime p) (locOver (A := A) B p),
    IsScalarTower.algebraMap_eq A B (locOver (A := A) B p), ← RingHom.comp_assoc,
    ← IsScalarTower.algebraMap_eq B (locOver (A := A) B p) (FractionRing B),
    IsScalarTower.algebraMap_eq (Localization.AtPrime p) (FractionRing A) (FractionRing B),
    RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq,
    ← IsScalarTower.algebraMap_eq]

/-- The `A_𝔭`-rank of `B_𝔭` equals the fraction-field degree `[Frac(B) : Frac(A)]`. -/
theorem finrank_locOver_eq [IsNoetherianRing A] [IsIntegrallyClosed A]
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    Module.finrank (Localization.AtPrime p) (locOver (A := A) B p) =
      Module.finrank (FractionRing A) (FractionRing B) := by
  have := isDiscreteValuationRing_locAt p hp
  have := moduleFree_locOver (B := B) p hp
  exact (IsFractionRing.finrank_eq (Localization.AtPrime p) (FractionRing A)
      (locOver (A := A) B p) (FractionRing B)).symm

/-- Combined form: Σ `e f` equals the fraction-field degree. -/
theorem sum_ramification_inertia_eq_finrank_fractionRing
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    ∑ q : (maximalIdeal (Localization.AtPrime p)).primesOver (locOver (A := A) B p),
        q.1.ramificationIdx (Localization.AtPrime p) *
          q.1.inertiaDeg (Localization.AtPrime p) =
      Module.finrank (FractionRing A) (FractionRing B) :=
  (sum_ramification_inertia_locOver p hp).trans (finrank_locOver_eq p hp)

end Rank

/-! ## Keystone specialization -/

section Keller

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
variable {P Q : Plane k}

/-- `B = integralClosure A k[x,y]` is the integral closure of `A` in `k(x,y)`. -/
theorem IsKellerPair.isIntegralClosure_integralClosureInPlane (hPQ : IsKellerPair P Q) :
    IsIntegralClosure (integralClosureInPlane P Q) (coordRing P Q) (FractionRing (Plane k)) :=
  IsIntegralClosure.of_isIntegralClosure_of_isIntegrallyClosedIn
    (coordRing P Q) (integralClosureInPlane P Q) (Plane k) (FractionRing (Plane k))

/-- `B = integralClosure A k[x,y]` has fraction field `k(x,y)`. -/
theorem IsKellerPair.isFractionRing_integralClosureInPlane (hPQ : IsKellerPair P Q) :
    IsFractionRing (integralClosureInPlane P Q) (FractionRing (Plane k)) := by
  have := IsKellerPair.isNoetherianRing_coordRing hPQ
  have := IsKellerPair.isIntegrallyClosed_coordRing hPQ
  have := hPQ.finiteDimensional_fractionRings
  have := hPQ.isSeparable_fractionRings
  have := hPQ.isIntegralClosure_integralClosureInPlane
  exact IsIntegralClosure.isFractionRing_of_finite_extension (coordRing P Q)
    (FractionRing (coordRing P Q)) (FractionRing (Plane k))
    (integralClosureInPlane P Q)

/-- Finite generation of the graph algebra, packaged for typeclass use. -/
theorem IsKellerPair.moduleFinite_integralClosureInPlane (hPQ : IsKellerPair P Q) :
    Module.Finite (coordRing P Q) (integralClosureInPlane P Q) :=
  have := IsKellerPair.isNoetherianRing_coordRing hPQ
  have := IsKellerPair.isIntegrallyClosed_coordRing hPQ
  have := hPQ.finiteDimensional_fractionRings
  have := hPQ.isSeparable_fractionRings
  moduleFinite_integralClosure (coordRing P Q) (FractionRing (coordRing P Q))
    (FractionRing (Plane k)) (Plane k)

/-- **K1-L14, Keller form.** At a height-one prime `𝔭` of `k[P,Q]`,

```
∑ 𝔮 ∈ m.primesOver B_𝔭, e_𝔮 · f_𝔮 = finrank_{A_𝔭} B_𝔭
```

where `m` is the maximal ideal of the DVR `A_𝔭`. Combined with
`finrank_locOver_eq` and `isFractionRing_integralClosureInPlane`, the
right-hand side is the geometric degree `kellerDegree`. -/
theorem IsKellerPair.sum_ramification_inertia (hPQ : IsKellerPair P Q)
    (p : Ideal (coordRing P Q)) [p.IsPrime] (hp : p.height = 1) :
    have := IsKellerPair.isNoetherianRing_coordRing hPQ
    have := IsKellerPair.isIntegrallyClosed_coordRing hPQ
    have := hPQ.moduleFinite_integralClosureInPlane
    have : Module.IsTorsionFree (coordRing P Q) (integralClosureInPlane P Q) :=
      inferInstance
    ∑ q : (maximalIdeal (Localization.AtPrime p)).primesOver
        (locOver (A := coordRing P Q) (integralClosureInPlane P Q) p),
        q.1.ramificationIdx (Localization.AtPrime p) *
          q.1.inertiaDeg (Localization.AtPrime p) =
      Module.finrank (Localization.AtPrime p)
        (locOver (A := coordRing P Q) (integralClosureInPlane P Q) p) := by
  have := IsKellerPair.isNoetherianRing_coordRing hPQ
  have := IsKellerPair.isIntegrallyClosed_coordRing hPQ
  have := hPQ.moduleFinite_integralClosureInPlane
  have : Module.IsTorsionFree (coordRing P Q) (integralClosureInPlane P Q) :=
    inferInstance
  exact sum_ramification_inertia_locOver (B := integralClosureInPlane P Q) p hp

end Keller

end KeystoneGraph

#print axioms KeystoneGraph.maximalIdeal_locAt_eq_map
#print axioms KeystoneGraph.moduleFinite_locOver
#print axioms KeystoneGraph.instFintypePrimesOverLocOver
#print axioms KeystoneGraph.sum_ramification_inertia_locOver
#print axioms KeystoneGraph.finrank_locOver_eq
#print axioms KeystoneGraph.sum_ramification_inertia_eq_finrank_fractionRing
#print axioms KeystoneGraph.IsKellerPair.isIntegralClosure_integralClosureInPlane
#print axioms KeystoneGraph.IsKellerPair.isFractionRing_integralClosureInPlane
#print axioms KeystoneGraph.IsKellerPair.moduleFinite_integralClosureInPlane
#print axioms KeystoneGraph.IsKellerPair.sum_ramification_inertia
