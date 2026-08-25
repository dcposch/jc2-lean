/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
-/
import Mathlib

/-!
# Challenge: algebraic core of the uniform depth-two strip block

This module states four kernel-checkable pieces associated with Section 6 of
*A Vertex-Gap Obstruction for Low-Degree Strip Pairs in the Plane Jacobian
Conjecture*:

* an exact coefficient encoding of the weighted ODE;
* the resulting one-way inner-column rigidity theorem;
* the finite coefficient identity defining the log-residue functional; and
* the final logical assembly of the block variety, conditional on an explicit
  interface containing the inner- and outer-elimination equivalences.

The last theorem is deliberately **not** presented as a full formalization of
the paper's `thm:R`.  The lattice-to-block reduction, the triangular solve
identifying the actual extra keys with this coefficient encoding, the converse
on the normalized binomial locus, and the outer-column calculation are outside
the present package.  `DepthTwoBlockData` exposes those missing inputs as
fields rather than silently assuming them.
-/

open Polynomial

/-- The weighted differential expression `A C' - k A' C`. -/
noncomputable def weightedDerivation {F : Type*} [CommRing F] (k : ℕ)
    (A C : Polynomial F) : Polynomial F :=
  A * derivative C - (k : Polynomial F) * (derivative A * C)

/-- A coefficient-level encoding of a solved inner column.  It quantifies a
polynomial `C` with the source's support bound and asks all potentially
nonzero coefficients of the weighted derivation to equal those of `1`. -/
def innerBlockKeysVanish {F : Type*} [CommRing F] (k d : ℕ)
    (A : Polynomial F) : Prop :=
  ∃ C : Polynomial F,
    C.coeff 0 = 0 ∧ C.natDegree ≤ k * d ∧
      ∀ n < (k + 1) * d,
        (weightedDerivation k A C).coeff n = if n = 0 then 1 else 0

/-- The logarithmic-residue linear form `R_{k,d}`.  Terms below `k+2`
are included in the range but vanish because their binomial coefficient is
zero. -/
def logResidue {F : Type*} [CommRing F] (k d : ℕ) (a : F)
    (β : ℕ → F) : F :=
  ∑ j ∈ Finset.range (2 * d + 1),
    (-1 : F) ^ j * (Nat.choose j (k + 2) : F) * a ^ (2 * d - j) * β j

/-- A finite binomial transform whose coefficient at `k+2` is
`logResidue k d a β`. -/
noncomputable def residueTransform {F : Type*} [CommRing F] (d : ℕ) (a : F)
    (β : ℕ → F) : Polynomial F :=
  ∑ j ∈ Finset.range (2 * d + 1),
    C (((-1 : F) ^ j) * a ^ (2 * d - j) * β j) * (X + 1) ^ j

/-- The finite coefficient encoding is equivalent to the polynomial ODE.
The degree hypotheses show that no coefficient beyond the encoded range can
survive. -/
theorem BlockToODEBridge {F : Type*} [CommRing F]
    (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (A : Polynomial F) (hA : A.natDegree ≤ d) :
    innerBlockKeysVanish k d A ↔
      ∃ C : Polynomial F, C.coeff 0 = 0 ∧ C.natDegree ≤ k * d ∧
        weightedDerivation k A C = 1 := by
  sorry

/-- Vanishing of the encoded inner keys forces the first-column polynomial
to have degree at most one. -/
theorem InnerBlockRigidity {F : Type*} [CommRing F] [IsDomain F] [CharZero F]
    (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) (A : Polynomial F)
    (hA : A.natDegree ≤ d) (hinner : innerBlockKeysVanish k d A) :
    A.natDegree ≤ 1 := by
  sorry

/-- Exact finite coefficient identity behind the displayed log-residue
linear form. -/
theorem OuterResidueIdentity {F : Type*} [CommRing F]
    (k d : ℕ) (a : F) (β : ℕ → F) :
    (residueTransform d a β).coeff (k + 2) = logResidue k d a β := by
  sorry

/-- Interface for the two substantive elimination identifications needed to
turn the algebraic core into the paper's actual depth-two block theorem. -/
structure DepthTwoBlockData {F : Type*} [Field F]
    (k d : ℕ) (A : Polynomial F) (a : F) (β : ℕ → F) where
  innerExtrasVanish : Prop
  outerExtrasVanish : Prop
  inner_iff : innerExtrasVanish ↔ A.natDegree ≤ 1
  outer_iff : A.natDegree ≤ 1 →
    (outerExtrasVanish ↔ a ^ ((k - 1) * d) * logResidue k d a β = 0)

/-- The final variety-theoretic intersection, once the inner and outer
elimination equivalences are supplied through `DepthTwoBlockData`. -/
theorem LogResidueBlockVariety {F : Type*} [Field F]
    (k d : ℕ) (hk : 2 ≤ k) (hd : 2 ≤ d)
    (A : Polynomial F) (a : F) (β : ℕ → F)
    (block : DepthTwoBlockData k d A a β) :
    (block.innerExtrasVanish ∧ block.outerExtrasVanish) ↔
      A.natDegree ≤ 1 ∧ (a = 0 ∨ logResidue k d a β = 0) := by
  sorry
