/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch (direction), Claude / Anthropic and Grok / xAI
agents (formalization)
-/
import KeystoneGraph.TameDifferent
import KeystoneGraph.SumRamification

/-!
# K1-L18: the valuation formula `e = 1 + v(𝔇)`

K1(4) recast ring-theoretically: at every prime `𝔮` of `B_𝔭` lying over the
closed point of a height-one localization `A_𝔭` (the affine-image fibre of
L14), the ramification index equals one plus the `𝔮`-adic valuation of the
different,

```
e_𝔮 = 1 + v_𝔮(differentIdeal A_𝔭 B_𝔭)
```

i.e. `q.1.ramificationIdx A_𝔭 = 1 + multiplicity q.1 (differentIdeal A_𝔭 B_𝔭)`.

This is the rearrangement of K1-L17's
`multiplicity_differentIdeal_eq_ramificationIdx_sub_one`, instantiated at
the localized Dedekind extension `B_𝔭 / A_𝔭` supplied by K1-L13. The L17
residue-characteristic hypothesis `CharZero (A ⧸ p)` is **not** inherited
from ring characteristic zero (that implication is false: `ℤ ⊂ ℤ[i]` at
`(2)`). It is discharged from the `k`-algebra structure: every residue
field of an algebra over a characteristic-zero field `k` contains `k`.

The formula holds for every prime in the L14 fibre, hence in particular
for every boundary prime with affine image.

The Dedekind hypotheses on `A_𝔭` and `B_𝔭` are instance binders, discharged
by K1-L13 (`isDiscreteValuationRing_locAt`, `isDedekindDomain_locOver`,
`moduleFree_locOver`) at a height-one prime.

Consumables: K1-L17
(`multiplicity_differentIdeal_eq_ramificationIdx_sub_one`), K1-L13
(`isDiscreteValuationRing_locAt`, `isDedekindDomain_locOver`), K1-L14
(`moduleFinite_locOver`, `Ideal.ramificationIdx` fibre indexing),
`charZero_of_injective_algebraMap`, `RingHom.injective`.
-/

noncomputable section

open Algebra IsLocalRing IsLocalization
open scoped nonZeroDivisors

namespace KeystoneGraph

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-! ## Residue characteristic zero from a `k`-algebra structure -/

/-- **Residue characteristic zero, from the `k`-algebra structure.**  A
maximal quotient of a `k`-algebra, for `k` a field of characteristic zero,
has characteristic zero: the structure map `k → A ⧸ I` is a homomorphism
from a field to a nontrivial ring, hence injective, and characteristic
zero pushes forward along injective ring maps.

This is the discharge of L17's `[CharZero (A ⧸ p)]`. It does **not** follow
from `[CharZero A]`. -/
theorem charZero_quotient_of_algebra {k A : Type*} [Field k] [CharZero k]
    [CommRing A] [Algebra k A] {I : Ideal A} [I.IsMaximal] :
    CharZero (A ⧸ I) :=
  charZero_of_injective_algebraMap (RingHom.injective (algebraMap k (A ⧸ I)))

/-- Residue field of a prime localization of a `k`-algebra has characteristic
zero. -/
theorem charZero_residueField_locAt {k A : Type*} [Field k] [CharZero k]
    [CommRing A] [Algebra k A] (p : Ideal A) [p.IsPrime] :
    CharZero (Localization.AtPrime p ⧸ maximalIdeal (Localization.AtPrime p)) :=
  charZero_quotient_of_algebra (k := k) (A := Localization.AtPrime p)

/-! ## Rearrangement of L17: `e = 1 + v(𝔇)` -/

section DedekindRearrange

variable (A : Type*) {B : Type*} [CommRing A] [CommRing B]
  [IsDedekindDomain A] [IsDedekindDomain B] [Algebra A B]
  [Module.Finite A B] [Module.IsTorsionFree A B]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

/-- **K1(4), Dedekind form.** For a maximal ideal `P` of `B` lying over a
maximal ideal `p` of `A` with residue characteristic zero,

```
e_P = 1 + v_P(differentIdeal A B)
```

This is `multiplicity_differentIdeal_eq_ramificationIdx_sub_one` solved
for the ramification index. The inequality `1 ≤ e_P` is
`Ideal.ramificationIdx_pos`. -/
theorem ramificationIdx_eq_one_add_multiplicity_differentIdeal
    {p : Ideal A} [p.IsMaximal] [CharZero (A ⧸ p)] (hp : p ≠ ⊥)
    {P : Ideal B} [P.IsMaximal] [P.LiesOver p] :
    P.ramificationIdx A = 1 + multiplicity P (differentIdeal A B) := by
  have hpos : 1 ≤ P.ramificationIdx A :=
    Nat.succ_le_of_lt (P.ramificationIdx_pos A)
  rw [multiplicity_differentIdeal_eq_ramificationIdx_sub_one A hp,
    Nat.add_comm, Nat.sub_add_cancel hpos]

end DedekindRearrange

/-! ## Instantiation at `B_𝔭 / A_𝔭` (L13), L14 fibre indexing -/

section LocOver

set_option linter.overlappingInstances false

variable {A : Type*} [CommRing A] [IsDomain A]

/-- The maximal ideal of a height-one localization is nonzero: `A_𝔭` is a
DVR, hence not a field. -/
theorem maximalIdeal_locAt_ne_bot [IsNoetherianRing A] [IsIntegrallyClosed A]
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    maximalIdeal (Localization.AtPrime p) ≠ ⊥ := by
  have := isDiscreteValuationRing_locAt p hp
  exact IsDiscreteValuationRing.not_a_field _

/-- **K1(4) at a height-one fibre.** For a prime `𝔮` of `B_𝔭` over the
closed point of `A_𝔭`,

```
q.1.ramificationIdx A_𝔭 = 1 + multiplicity q.1 (differentIdeal A_𝔭 B_𝔭)
```

The Dedekind / freeness hypotheses on the localizations are the K1-L13
facts `isDiscreteValuationRing_locAt`, `isDedekindDomain_locOver` and
`moduleFree_locOver` (available at height one). Residue characteristic
zero is discharged from the `k`-algebra structure, not from ring
characteristic zero.

The fibre is indexed exactly as in L14. -/
theorem ramificationIdx_eq_one_add_multiplicity_differentIdeal_locOver
    {k : Type*} [Field k] [CharZero k] [Algebra k A]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra A B]
    (p : Ideal A) [p.IsPrime]
    (q : (maximalIdeal (Localization.AtPrime p)).primesOver (locOver (A := A) B p))
    [IsDiscreteValuationRing (Localization.AtPrime p)]
    [IsDedekindDomain (Localization.AtPrime p)]
    [IsDedekindDomain (locOver (A := A) B p)]
    [Module.Finite (Localization.AtPrime p) (locOver (A := A) B p)]
    [Module.IsTorsionFree (Localization.AtPrime p) (locOver (A := A) B p)]
    [Algebra.IsSeparable (FractionRing (Localization.AtPrime p))
      (FractionRing (locOver (A := A) B p))] :
    q.1.ramificationIdx (Localization.AtPrime p) =
      1 + multiplicity q.1
        (differentIdeal (Localization.AtPrime p) (locOver (A := A) B p)) := by
  have : CharZero (Localization.AtPrime p ⧸ maximalIdeal (Localization.AtPrime p)) :=
    charZero_residueField_locAt (k := k) p
  exact ramificationIdx_eq_one_add_multiplicity_differentIdeal
    (A := Localization.AtPrime p) (B := locOver (A := A) B p)
    (IsDiscreteValuationRing.not_a_field _) (P := q.1)

end LocOver

end KeystoneGraph

#print axioms KeystoneGraph.charZero_quotient_of_algebra
#print axioms KeystoneGraph.charZero_residueField_locAt
#print axioms KeystoneGraph.ramificationIdx_eq_one_add_multiplicity_differentIdeal
#print axioms KeystoneGraph.maximalIdeal_locAt_ne_bot
#print axioms KeystoneGraph.ramificationIdx_eq_one_add_multiplicity_differentIdeal_locOver
