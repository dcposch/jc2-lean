/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
-/
import Mathlib
import Rigidity

/-!
# The uniform depth-two strip block

This file formalizes the polynomial core of Section 6 of
*A Vertex-Gap Obstruction for Low-Degree Strip Pairs in the Plane Jacobian
Conjecture*.  It deliberately works at the already assembled block-column
level.  Thus the lattice-support enumeration and triangular elimination of
the original `P,Q` coefficients are outside this package, while the following
parts are kernel checked here:

* the coefficient-key formulation of the inner block is equivalent to the
  weighted ODE (`BlockToODEBridge`);
* inner-block vanishing forces the first column to be binomial
  (`InnerBlockRigidity`);
* the displayed logarithmic-residue sum is exactly a coefficient of a finite
  binomial transform (`OuterResidueIdentity`);
* the last variety-theoretic assembly, from the inner and outer block
  identifications, is valid uniformly (`LogResidueBlockVariety`).
-/

open Polynomial

/-- The weighted differential expression `A C' - k A' C`. -/
noncomputable def weightedDerivation {F : Type*} [CommRing F] (k : ℕ)
    (A C : Polynomial F) : Polynomial F :=
  A * derivative C - (k : Polynomial F) * (derivative A * C)

/-- All coefficient keys in the assembled inner column vanish, with constant
key normalized to one.  The support bound on `C` is the block-column bound. -/
def innerBlockKeysVanish {F : Type*} [CommRing F] (k d : ℕ)
    (A : Polynomial F) : Prop :=
  ∃ C : Polynomial F,
    C.coeff 0 = 0 ∧ C.natDegree ≤ k * d ∧
      ∀ n < (k + 1) * d,
        (weightedDerivation k A C).coeff n = if n = 0 then 1 else 0

/-- The paper's logarithmic-residue functional.  Writing it over `range`
instead of `Icc` only adds terms with a zero binomial coefficient. -/
def logResidue {F : Type*} [CommRing F] (k d : ℕ) (a : F)
    (β : ℕ → F) : F :=
  ∑ j ∈ Finset.range (2 * d + 1),
    (-1 : F) ^ j * (Nat.choose j (k + 2) : F) * a ^ (2 * d - j) * β j

/-- A finite binomial transform whose `(k+2)` coefficient is the residue
functional.  It is a denominator-free form of the coordinate expansion used
in the outer-column calculation. -/
noncomputable def residueTransform {F : Type*} [CommRing F] (d : ℕ) (a : F)
    (β : ℕ → F) : Polynomial F :=
  ∑ j ∈ Finset.range (2 * d + 1),
    C (((-1 : F) ^ j) * a ^ (2 * d - j) * β j) * (X + 1) ^ j

/-- The inner block coefficient conditions are exactly the polynomial ODE.
This is the block-to-ODE bridge after block-column assembly. -/
theorem BlockToODEBridge {F : Type*} [CommRing F]
    (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (A : Polynomial F) (hA : A.natDegree ≤ d) :
    innerBlockKeysVanish k d A ↔
      ∃ C : Polynomial F, C.coeff 0 = 0 ∧ C.natDegree ≤ k * d ∧
        weightedDerivation k A C = 1 := by
  constructor
  · rintro ⟨C, hC0, hCdeg, hkeys⟩
    refine ⟨C, hC0, hCdeg, ?_⟩
    have htotal : (k + 1) * d = k * d + d := by simp [Nat.add_mul]
    have hkd : 1 ≤ k * d := Nat.mul_pos hk hd
    have htotalPos : 1 ≤ (k + 1) * d := Nat.mul_pos (by omega) hd
    ext n
    by_cases hn : n < (k + 1) * d
    · rw [hkeys n hn]
      simp only [coeff_one]
    · have hderC : (derivative C).natDegree ≤ k * d - 1 :=
        (natDegree_derivative_le C).trans (Nat.sub_le_sub_right hCdeg 1)
      have hderA : (derivative A).natDegree ≤ d - 1 :=
        (natDegree_derivative_le A).trans (Nat.sub_le_sub_right hA 1)
      have hleft : (A * derivative C).natDegree ≤ (k + 1) * d - 1 := by
        refine natDegree_mul_le.trans ?_
        calc
          A.natDegree + (derivative C).natDegree ≤ d + (k * d - 1) :=
            Nat.add_le_add hA hderC
          _ ≤ (k + 1) * d - 1 := by omega
      have hright :
          ((k : Polynomial F) * (derivative A * C)).natDegree ≤
            (k + 1) * d - 1 := by
        have hin : (derivative A * C).natDegree ≤ (d - 1) + k * d :=
          natDegree_mul_le.trans (Nat.add_le_add hderA hCdeg)
        rw [← C_eq_natCast]
        refine (natDegree_C_mul_le _ _).trans (hin.trans ?_)
        omega
      have hdeg : (weightedDerivation k A C).natDegree ≤ (k + 1) * d - 1 :=
        (natDegree_sub_le _ _).trans (max_le hleft hright)
      have hn' : (k + 1) * d - 1 < n := by omega
      rw [coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hn')]
      have hn0 : n ≠ 0 := by omega
      simp [coeff_one, hn0]
  · rintro ⟨C, hC0, hCdeg, hode⟩
    refine ⟨C, hC0, hCdeg, ?_⟩
    intro n hn
    rw [hode]
    simp [coeff_one]

/-- Rigidity half of the block theorem: vanishing of the inner block keys
forces `A` to be binomial. -/
theorem InnerBlockRigidity {F : Type*} [CommRing F] [IsDomain F] [CharZero F]
    (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) (A : Polynomial F)
    (hA : A.natDegree ≤ d) (hinner : innerBlockKeysVanish k d A) :
    A.natDegree ≤ 1 := by
  obtain ⟨C, -, -, hode⟩ := (BlockToODEBridge k d hk hd A hA).mp hinner
  exact StripBlock.Rigidity.odeRigidity k hk A C 1 one_ne_zero
    (by simpa [weightedDerivation] using hode)

/-- Exact finite coefficient identity behind the logarithmic residue. -/
theorem OuterResidueIdentity {F : Type*} [CommRing F]
    (k d : ℕ) (a : F) (β : ℕ → F) :
    (residueTransform d a β).coeff (k + 2) = logResidue k d a β := by
  rw [residueTransform, logResidue, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j hj
  rw [coeff_C_mul, coeff_X_add_one_pow]
  ring

/-- Abstract assembled depth-two block data.  The two equivalences are
precisely the block-to-ODE/inner-solution identification and the outer-column
residue identity supplied by the triangular block elimination.  Keeping this
interface explicit prevents the formal theorem from silently assuming the
unformalized lattice-to-block reduction. -/
structure DepthTwoBlockData {F : Type*} [Field F]
    (k d : ℕ) (A : Polynomial F) (a : F) (β : ℕ → F) where
  innerExtrasVanish : Prop
  outerExtrasVanish : Prop
  inner_iff : innerExtrasVanish ↔ A.natDegree ≤ 1
  outer_iff : A.natDegree ≤ 1 →
    (outerExtrasVanish ↔ a ^ ((k - 1) * d) * logResidue k d a β = 0)

/-- Uniform log-residue description of the assembled depth-two block
variety.  This is the final logical intersection in `thm:R`. -/
theorem LogResidueBlockVariety {F : Type*} [Field F]
    (k d : ℕ) (hk : 2 ≤ k) (hd : 2 ≤ d)
    (A : Polynomial F) (a : F) (β : ℕ → F)
    (block : DepthTwoBlockData k d A a β) :
    (block.innerExtrasVanish ∧ block.outerExtrasVanish) ↔
      A.natDegree ≤ 1 ∧ (a = 0 ∨ logResidue k d a β = 0) := by
  have hexp : (k - 1) * d ≠ 0 :=
    Nat.mul_ne_zero (by omega) (by omega)
  rw [block.inner_iff]
  constructor
  · rintro ⟨hbin, hout⟩
    refine ⟨hbin, ?_⟩
    rw [block.outer_iff hbin] at hout
    rcases mul_eq_zero.mp hout with ha | hR
    · left
      exact eq_zero_of_pow_eq_zero ha
    · exact Or.inr hR
  · rintro ⟨hbin, ha | hR⟩
    · refine ⟨hbin, (block.outer_iff hbin).mpr ?_⟩
      simp [ha, hexp]
    · refine ⟨hbin, (block.outer_iff hbin).mpr ?_⟩
      simp [hR]

#print axioms BlockToODEBridge
#print axioms InnerBlockRigidity
#print axioms OuterResidueIdentity
#print axioms LogResidueBlockVariety
