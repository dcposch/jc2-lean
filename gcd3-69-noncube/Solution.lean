/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch (direction), OpenAI Codex agent (formalization)
-/
import Mathlib

/-!
# The lower-Pfaffian noncube gate at partial degrees `(6,9)`

This module proves algebraic implications and terminal identities used in the
aligned nontrivial cubic-Kummer branch.  The central theorem shows that every
field-valued solution of the four Kummer-forced invariant equations lies on
the zero-bracket sheet or the elliptic sheet displayed in the source report;
it does not prove converse inclusions or existence of either sheet.  The v2
theorems also close the shifted Davenport--Stothers sheet by deriving its
finite-place classification and one-point cube conclusion from the reduced
rational ODE.
-/

open Polynomial
open scoped BigOperators

/-- Every field-valued solution of the four lower-Pfaffian invariant equations
lies on one of the two displayed reduced sheets.  The first disjunct is the
zero-bracket sheet `P_A`; the second is the elliptic sheet `P_B`.  No converse
inclusion or existence statement is asserted. -/
theorem GCD369InvariantFibreDichotomy {K : Type*} [Field K] [CharZero K]
    (a0 a1 a2 a3 a4 kappa mu : K) :
    let A := 4 * a2 - a4 ^ 2
    let B := 2 * a1 - a3 * a4
    let w := 4 * a0 - a3 ^ 2
    let e4 :=
      64 * a0 * a2 - 16 * a0 * a4 ^ 2 + 32 * a1 ^ 2 - 32 * a1 * a3 * a4
        - 16 * a2 ^ 2 * a4 - 16 * a2 * a3 ^ 2 + 8 * a2 * a4 ^ 3
        + 12 * a3 ^ 2 * a4 ^ 2 - a4 ^ 5
    let e3 :=
      64 * a0 * a1 - 32 * a0 * a3 * a4 - 32 * a1 * a2 * a4 - 16 * a1 * a3 ^ 2
        + 8 * a1 * a4 ^ 3 - 16 * a2 ^ 2 * a3 + 24 * a2 * a3 * a4 ^ 2
        + 8 * a3 ^ 3 * a4 - 5 * a3 * a4 ^ 4
    let p4 := 3 * e4 + 32 * kappa * A
    let p3 := 3 * e3 + 64 * kappa * B
    let p2 :=
      1152 * a0 ^ 2 - 768 * a0 * a2 * a4 - 576 * a0 * a3 ^ 2 + 192 * a0 * a4 ^ 3
        + 1536 * a0 * kappa - 384 * a1 ^ 2 * a4 - 1152 * a1 * a2 * a3
        + 672 * a1 * a3 * a4 ^ 2 - 192 * a2 ^ 3 + 336 * a2 ^ 2 * a4 ^ 2
        + 768 * a2 * a3 ^ 2 * a4 - 132 * a2 * a4 ^ 4 - 512 * a2 * a4 * kappa
        + 72 * a3 ^ 4 - 288 * a3 ^ 2 * a4 ^ 3 - 384 * a3 ^ 2 * kappa
        + 15 * a4 ^ 6 + 128 * a4 ^ 3 * kappa - 512 * mu
    let p1 :=
      96 * a0 * a1 * a4 + 192 * a0 * a2 * a3 - 96 * a0 * a3 * a4 ^ 2
        + 96 * a1 ^ 2 * a3 + 144 * a1 * a2 ^ 2 - 120 * a1 * a2 * a4 ^ 2
        - 120 * a1 * a3 ^ 2 * a4 + 21 * a1 * a4 ^ 4 + 64 * a1 * a4 * kappa
        - 144 * a2 ^ 2 * a3 * a4 - 48 * a2 * a3 ^ 3 + 96 * a2 * a3 * a4 ^ 3
        + 128 * a2 * a3 * kappa + 48 * a3 ^ 3 * a4 ^ 2 - 15 * a3 * a4 ^ 5
        - 64 * a3 * a4 ^ 2 * kappa
    let EB :=
      384 * a2 ^ 3 - 432 * a2 ^ 2 * a4 ^ 2 + 144 * a2 * a4 ^ 4 - 15 * a4 ^ 6
        + 1024 * (kappa ^ 2 + mu)
    p4 = 0 → p3 = 0 → p2 = 0 → p1 = 0 →
      (A = 0 ∧ B = 0 ∧ 9 * w ^ 2 + 48 * kappa * w - 64 * mu = 0)
        ∨ (a3 = 0 ∧ a1 = 0 ∧ EB = 0
          ∧ 48 * a0 - 12 * a2 * a4 + 3 * a4 ^ 3 + 32 * kappa = 0) := by
  dsimp
  intro hp4 hp3 hp2 hp1
  by_cases hA : 4 * a2 - a4 ^ 2 = 0
  · left
    have hBsq : 24 * (2 * a1 - a3 * a4) ^ 2 = 0 := by
      linear_combination hp4
        - (3 * a4 ^ 3 - 12 * a3 ^ 2 - 12 * a2 * a4 + 48 * a0 + 32 * kappa) * hA
    have hB : 2 * a1 - a3 * a4 = 0 := by
      have h24 : (24 : K) ≠ 0 := by norm_num
      exact (pow_eq_zero_iff (by norm_num : (2 : Nat) ≠ 0)).mp
        ((mul_eq_zero.mp hBsq).resolve_left h24)
    refine ⟨hA, hB, ?_⟩
    linear_combination
      (1 / 8) * hp2
      - (1 / 8) * (-15 * a4 ^ 4 + 288 * a3 ^ 2 * a4 + 72 * a2 * a4 ^ 2
        - 48 * a2 ^ 2 - 480 * a1 * a3 - 192 * a0 * a4 - 128 * a4 * kappa) * hA
      - (1 / 8) * (384 * a2 * a3 - 192 * a1 * a4) * hB
  · right
    have hsplit : a3 * (4 * a2 - a4 ^ 2) ^ 4 = 0 := by
      linear_combination
        (-8 / 9 * a3 * a4 ^ 3 + 16 / 9 * a3 ^ 3 + 32 / 9 * a2 * a3 * a4
          - 64 / 9 * a0 * a3 - 128 / 27 * a3 * kappa) * hp4
        + (-7 / 9 * a4 ^ 4 + 8 / 9 * a3 ^ 2 * a4 + 40 / 9 * a2 * a4 ^ 2
          - 16 / 3 * a2 ^ 2 - 32 / 9 * a0 * a4 - 64 / 27 * a4 * kappa) * hp3
        + (8 / 9 * a4 ^ 3 - 16 / 9 * a3 ^ 2 - 32 / 9 * a2 * a4
          + 64 / 9 * a0 + 128 / 27 * kappa) * hp1
    have ha3 : a3 = 0 := by
      rcases mul_eq_zero.mp hsplit with h | h
      · exact h
      · exact False.elim ((pow_ne_zero 4 hA) h)
    have haux :
        2 * a1 * (4 * a2 - a4 ^ 2) ^ 2
          + a3 * (-16 * a2 ^ 2 * a4 + 8 * a2 * a4 ^ 3 - a4 ^ 5) = 0 := by
      linear_combination (-2 / 9 * a3) * hp4 + (-1 / 9 * a4) * hp3 + (2 / 9) * hp1
    have ha1 : a1 = 0 := by
      rw [ha3, zero_mul, add_zero] at haux
      have h2 : (2 : K) ≠ 0 := by norm_num
      rcases mul_eq_zero.mp haux with h | h
      · exact (mul_eq_zero.mp h).resolve_left h2
      · exact False.elim ((pow_ne_zero 2 hA) h)
    refine ⟨ha3, ha1, ?_, ?_⟩
    · have hlin : 48 * a0 - 12 * a2 * a4 + 3 * a4 ^ 3 + 32 * kappa = 0 := by
        have hprod :
            (4 * a2 - a4 ^ 2)
              * (48 * a0 - 12 * a2 * a4 + 3 * a4 ^ 3 + 32 * kappa) = 0 := by
          linear_combination hp4
            - (36 * a3 * a4 ^ 2 - 48 * a2 * a3 - 96 * a1 * a4) * ha3
            - (96 * a1) * ha1
        exact (mul_eq_zero.mp hprod).resolve_left hA
      linear_combination
        (-2) * hp2
        + 2 * (5 / 2 * a4 ^ 3 - 10 * a2 * a4 + 24 * a0 + 16 * kappa) * hlin
        + 2 * (-288 * a3 * a4 ^ 3 + 72 * a3 ^ 3 + 768 * a2 * a3 * a4
          + 672 * a1 * a4 ^ 2 - 1152 * a1 * a2 - 576 * a0 * a3
          - 384 * a3 * kappa) * ha3
        + 2 * (-384 * a1 * a4) * ha1
    · have hprod :
          (4 * a2 - a4 ^ 2)
            * (48 * a0 - 12 * a2 * a4 + 3 * a4 ^ 3 + 32 * kappa) = 0 := by
        linear_combination hp4
          - (36 * a3 * a4 ^ 2 - 48 * a2 * a3 - 96 * a1 * a4) * ha3
          - (96 * a1) * ha1
      exact (mul_eq_zero.mp hprod).resolve_left hA

/-- Every path on the first reduced sheet has zero source bracket.  This is
the coefficientwise differential identity behind the common-power sheet and
its two constant deformations. -/
theorem GCD369ZeroBracketSheet {K : Type*} [Field K] [CharZero K] [Differential K]
    (u v d kappa : K) (hd : Differential.deriv d = 0)
    (hk : Differential.deriv kappa = 0) :
    let K0 : K[X] := X ^ 3 + C (u / 2) * X + C (v / 2)
    let f := K0 ^ 2 + C d
    let g := K0 ^ 3 + C (kappa + 3 * d / 2) * K0
    Differential.mapCoeffs f * derivative g - derivative f * Differential.mapCoeffs g = 0 := by
  dsimp
  let K0 : K[X] := X ^ 3 + C (u / 2) * X + C (v / 2)
  let delta := Differential.mapCoeffs (A := K)
  have hdC : delta (C d) = 0 := by simp [delta, hd]
  have htwo : Differential.deriv (2 : K) = 0 := by
    have hcast : (2 : K) = ((2 : Nat) : K) := by norm_num
    rw [hcast]
    exact Differential.deriv.map_natCast 2
  have hthree : Differential.deriv (3 : K) = 0 := by
    have hcast : (3 : K) = ((3 : Nat) : K) := by norm_num
    rw [hcast]
    exact Differential.deriv.map_natCast 3
  have hrat : Differential.deriv (3 / 2 : K) = 0 := by
    rw [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv]
    rw [htwo, hthree]
    simp
  have hq : Differential.deriv (kappa + 3 * d / 2) = 0 := by
    rw [map_add, hk, zero_add, show 3 * d / 2 = (3 / 2) * d by ring,
      Derivation.leibniz, hrat, hd]
    simp
  have hqC : delta (C (kappa + 3 * d / 2)) = 0 := by
    rw [Differential.mapCoeffs_C]
    simpa only [map_zero] using congrArg C hq
  have hf : delta (K0 ^ 2 + C d) = 2 * K0 * delta K0 := by
    rw [map_add, Derivation.leibniz_pow, hdC]
    simp only [nsmul_eq_mul, add_zero]
    ring
  have hg : delta (K0 ^ 3 + C (kappa + 3 * d / 2) * K0)
      = (3 * K0 ^ 2 + C (kappa + 3 * d / 2)) * delta K0 := by
    rw [map_add, Derivation.leibniz_pow, Derivation.leibniz, hqC]
    simp only [nsmul_eq_mul]
    ring
  have hdf : derivative (K0 ^ 2 + C d) = 2 * K0 * derivative K0 := by
    simp only [derivative_add, derivative_pow, derivative_C, add_zero,
      C_eq_natCast]
    ring
  have hdg : derivative (K0 ^ 3 + C (kappa + 3 * d / 2) * K0)
      = (3 * K0 ^ 2 + C (kappa + 3 * d / 2)) * derivative K0 := by
    simp only [derivative_add, derivative_pow, derivative_mul, derivative_C,
      zero_mul, zero_add, C_eq_natCast]
    ring
  change delta (K0 ^ 2 + C d) * derivative (K0 ^ 3 + C (kappa + 3 * d / 2) * K0)
    - derivative (K0 ^ 2 + C d) * delta (K0 ^ 3 + C (kappa + 3 * d / 2) * K0) = 0
  rw [hf, hg, hdf, hdg]
  ring

/-- On the second reduced sheet, the coordinates `X=8a₂-2a₄²` and
`Y=3a₄X` satisfy the elliptic equation from the lower-Pfaffian calculation. -/
theorem GCD369EllipticSheetEquation {K : Type*} [Field K] [CharZero K]
    (a2 a4 kappa mu : K)
    (hEB : 384 * a2 ^ 3 - 432 * a2 ^ 2 * a4 ^ 2 + 144 * a2 * a4 ^ 4
      - 15 * a4 ^ 6 + 1024 * (kappa ^ 2 + mu) = 0) :
    let X := 8 * a2 - 2 * a4 ^ 2
    let Y := 3 * a4 * X
    let C0 := kappa ^ 2 + mu
    Y ^ 2 = 3 * X ^ 3 + 4096 * C0 := by
  dsimp
  linear_combination (-4) * hEB

/-- Polynomial form of the terminal one-form on the elliptic sheet.  The
tangent equation is the derivative of `Y²=3X³+4096C` with constant `C`. -/
theorem GCD369EllipticTerminalForm {K : Type*} [Field K] [CharZero K]
    (a2 a4 a2dot a4dot C0 : K) :
    let X := 8 * a2 - 2 * a4 ^ 2
    let Y := 3 * a4 * X
    let Xdot := 8 * a2dot - 4 * a4 * a4dot
    let Ydot := 3 * a4dot * X + 3 * a4 * Xdot
    let beta :=
      3 * (4 * a2 - 3 * a4 ^ 2) * (4 * a2 - a4 ^ 2) * (4 * a2 + a4 ^ 2)
          / 2048 * a4dot
        + 3 * a4 * (4 * a2 - a4 ^ 2) * (4 * a2 + a4 ^ 2) / 512 * a2dot
    Y ^ 2 = 3 * X ^ 3 + 4096 * C0 → 2 * Y * Ydot = 9 * X ^ 2 * Xdot →
      147456 * X * beta = (7 * Y ^ 2 - 12288 * C0) * Ydot := by
  dsimp
  intro hcurve htangent
  linear_combination
    (54 * a4 ^ 2 * a4dot - 72 * a4 * a2dot - 72 * a2 * a4dot) * hcurve

/-- At least one of the two finite forbidden-value numerators is
nonconstant whenever a polynomial numerator/denominator pair is nonconstant
as a pair. -/
theorem GCD369ForbiddenNumerator {K : Type*} [Field K] [CharZero K]
    (N D : K[X]) (t : K) (ht : t ≠ 0)
    (hnonconstant : 0 < N.natDegree ∨ 0 < D.natDegree) :
    0 < (N - C t * D).natDegree ∨ 0 < (N + C t * D).natDegree := by
  by_contra h
  push Not at h
  have hm : (N - C t * D).natDegree = 0 := Nat.eq_zero_of_le_zero h.1
  have hp : (N + C t * D).natDegree = 0 := Nat.eq_zero_of_le_zero h.2
  have em := eq_C_of_natDegree_le_zero (Nat.le_zero.mpr hm)
  have ep := eq_C_of_natDegree_le_zero (Nat.le_zero.mpr hp)
  have hDconst : C (2 * t) * D =
      C ((N + C t * D).coeff 0 - (N - C t * D).coeff 0) := by
    simp only [map_mul, map_ofNat, map_sub]
    linear_combination ep - em
  have hNconst : C 2 * N =
      C ((N + C t * D).coeff 0 + (N - C t * D).coeff 0) := by
    simp only [map_ofNat, map_add]
    linear_combination ep + em
  have h2t : IsUnit (2 * t) := (isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) ht))
  have h2 : IsUnit (2 : K) := (isUnit_iff_ne_zero.mpr (by norm_num))
  have hDdeg : D.natDegree = 0 := by
    rw [← natDegree_C_mul_of_isUnit h2t D, hDconst, natDegree_C]
  have hNdeg : N.natDegree = 0 := by
    rw [← natDegree_C_mul_of_isUnit h2 N, hNconst, natDegree_C]
  rcases hnonconstant with hN | hD
  · rw [hNdeg] at hN
    omega
  · rw [hDdeg] at hD
    omega

/-- A nonconstant reduced rational trajectory on the nonzero-`C` elliptic
sheet cannot satisfy the cleared terminal Keller equation.  This formalizes
the forbidden finite-value argument directly with a reduced polynomial
presentation `Y=N/D`; ramification is harmless because the vanishing forbidden
factor already contradicts the nonzero right side.  Constant trajectories are
not covered. -/
theorem GCD369EllipticNonzeroExclusion {K : Type*} [Field K] [CharZero K]
    [IsAlgClosed K] (C0 j t : K) (hC : C0 ≠ 0) (hj : j ≠ 0)
    (ht : 7 * t ^ 2 = 12288 * C0) (N D H : K[X])
    (hnonconstant : 0 < N.natDegree ∨ 0 < D.natDegree)
    (hcoprime : ∀ x : K, eval x N = 0 → eval x D ≠ 0)
    (hterminal : ∀ x : K, eval x D ≠ 0 →
      let Y := eval x N / eval x D
      let Ydot :=
        eval x (derivative N * D - N * derivative D) / (eval x D) ^ 2
      3 * eval x H * (7 * Y ^ 2 - 12288 * C0) ^ 3 * Ydot ^ 3
        = (147456 * j) ^ 3 * (Y ^ 2 - 4096 * C0)) : False := by
  have ht0 : t ≠ 0 := by
    intro htzero
    rw [htzero] at ht
    norm_num at ht
    exact hC ht
  rcases GCD369ForbiddenNumerator N D t ht0 hnonconstant with hm | hp
  · let P := N - C t * D
    have hdeg : P.degree ≠ 0 := ne_of_gt (natDegree_pos_iff_degree_pos.mp hm)
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root P hdeg
    have hxP : eval x P = 0 := hx
    have hxD : eval x D ≠ 0 := by
      intro hDz
      have hxN : eval x N = 0 := by simpa [P, hDz] using hxP
      exact (hcoprime x hxN) hDz
    have hY : eval x N / eval x D = t := by
      apply (div_eq_iff hxD).2
      have hxP' : eval x N - t * eval x D = 0 := by simpa [P] using hxP
      exact sub_eq_zero.mp hxP'
    have hterm := hterminal x hxD
    dsimp at hterm
    rw [hY] at hterm
    have hforbid : 7 * t ^ 2 - 12288 * C0 = 0 := sub_eq_zero.mpr ht
    have hother : t ^ 2 - 4096 * C0 ≠ 0 := by
      intro hzero
      have : (-16384 : K) * C0 = 0 := by
        linear_combination 7 * hzero - ht
      exact hC ((mul_eq_zero.mp this).resolve_left (by norm_num))
    rw [hforbid, zero_pow (by norm_num : (3 : Nat) ≠ 0), mul_zero, zero_mul] at hterm
    exact (mul_ne_zero (pow_ne_zero 3 (mul_ne_zero (by norm_num) hj)) hother) hterm.symm
  · let P := N + C t * D
    have hdeg : P.degree ≠ 0 := ne_of_gt (natDegree_pos_iff_degree_pos.mp hp)
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root P hdeg
    have hxP : eval x P = 0 := hx
    have hxD : eval x D ≠ 0 := by
      intro hDz
      have hxN : eval x N = 0 := by simpa [P, hDz] using hxP
      exact (hcoprime x hxN) hDz
    have hY : eval x N / eval x D = -t := by
      apply (div_eq_iff hxD).2
      have hxP' : eval x N + t * eval x D = 0 := by simpa [P] using hxP
      linear_combination hxP'
    have hterm := hterminal x hxD
    dsimp at hterm
    rw [hY] at hterm
    have hforbid : 7 * (-t) ^ 2 - 12288 * C0 = 0 := by
      rw [neg_sq]
      exact sub_eq_zero.mpr ht
    have hother : (-t) ^ 2 - 4096 * C0 ≠ 0 := by
      rw [neg_sq]
      intro hzero
      have : (-16384 : K) * C0 = 0 := by
        linear_combination 7 * hzero - ht
      exact hC ((mul_eq_zero.mp this).resolve_left (by norm_num))
    rw [hforbid, zero_pow (by norm_num : (3 : Nat) ≠ 0), mul_zero, zero_mul] at hterm
    exact (mul_ne_zero (pow_ne_zero 3 (mul_ne_zero (by norm_num) hj)) hother) hterm.symm

/-- On the special fibre `C=kappa²+mu=0`, the elliptic-sheet equation factors
without division into the zero-bracket intersection and the shifted
Davenport--Stothers sheet. -/
theorem GCD369SpecialFibreDichotomy {K : Type*} [Field K] [CharZero K]
    (a2 a4 kappa mu : K) (hC : kappa ^ 2 + mu = 0)
    (hEB : 384 * a2 ^ 3 - 432 * a2 ^ 2 * a4 ^ 2 + 144 * a2 * a4 ^ 4
      - 15 * a4 ^ 6 + 1024 * (kappa ^ 2 + mu) = 0) :
    let X := 8 * a2 - 2 * a4 ^ 2
    X = 0 ∨ X = 3 * a4 ^ 2 := by
  dsimp
  have hfactor :
      (3 / 4 : K) * (8 * a2 - 2 * a4 ^ 2) ^ 2
        * ((8 * a2 - 2 * a4 ^ 2) - 3 * a4 ^ 2) = 0 := by
    linear_combination hEB - 1024 * hC
  rcases mul_eq_zero.mp hfactor with h | hlast
  · have h34 : (3 / 4 : K) ≠ 0 := by norm_num
    exact Or.inl ((pow_eq_zero_iff (by norm_num : (2 : Nat) ≠ 0)).mp
      ((mul_eq_zero.mp h).resolve_left h34))
  · exact Or.inr (sub_eq_zero.mp hlast)

/-- Exact bracket of the shifted Davenport--Stothers trajectory, in the
denominator-free normalization obtained by doubling its degree-nine member. -/
theorem GCD369ShiftedDSBracket {K : Type*} [Field K] [CharZero K]
    (lambda kappa : K) :
    let f : K[X] :=
      X ^ 6 + C (4 * lambda) * X ^ 4 + C (10 * lambda ^ 2) * X ^ 2
        + C (6 * lambda ^ 3 - 2 * kappa / 3)
    let g : K[X] :=
      C 2 * X ^ 9 + C (12 * lambda) * X ^ 7 + C (42 * lambda ^ 2) * X ^ 5
        + C (70 * lambda ^ 3) * X ^ 3 + C (63 * lambda ^ 4) * X
    let fdot : K[X] :=
      C 4 * X ^ 4 + C (20 * lambda) * X ^ 2 + C (18 * lambda ^ 2)
    let gdot : K[X] :=
      C 12 * X ^ 7 + C (84 * lambda) * X ^ 5 + C (210 * lambda ^ 2) * X ^ 3
        + C (252 * lambda ^ 3) * X
    fdot * derivative g - derivative f * gdot = C (1134 * lambda ^ 6) := by
  dsimp
  simp only [derivative_add, derivative_mul, derivative_pow, derivative_X, derivative_C]
  simp only [zero_mul, add_zero, zero_add]
  simp only [C_mul, C_pow, C_ofNat, C_eq_natCast]
  ring

/-- The terminal equation on the shifted Davenport--Stothers sheet descends
exactly through `s³=h`, `lambda=s²q` to the rational weighted ODE used by the
valuation closure. -/
theorem GCD369ShiftedDSTerminalDescent {K : Type*} [Field K] [CharZero K]
    (s h lambda q sdot qdot hdot lambdaDot : K) (hs : s ^ 3 = h)
    (hlambda : lambda = s ^ 2 * q) (hhdot : hdot = 3 * s ^ 2 * sdot)
    (hlambdaDot : lambdaDot = 2 * s * sdot * q + s ^ 2 * qdot) :
    567 * s * lambda ^ 6 * lambdaDot
      = 189 * h ^ 4 * q ^ 6 * (2 * hdot * q + 3 * h * qdot) := by
  rw [hlambda, hlambdaDot, hhdot, ← hs]
  ring

/-- Local order calculation for the weighted Wronskian in the shifted
Davenport--Stothers ODE.  Away from the resonant equality `2e = 3m`, its
order is exactly `e + m - 1`; at resonance the order gains at least one.
This is the cancellation-sensitive step that was left implicit in version 1. -/
theorem GCD369WeightedWronskianLocal {K : Type*} [Field K] [CharZero K]
    (H B : K[X]) (x : K) (hH : H ≠ 0) (hB : B ≠ 0)
    (hW : 2 * derivative H * B - 3 * H * derivative B ≠ 0)
    (hsupport : 0 < H.rootMultiplicity x + B.rootMultiplicity x) :
    let e := H.rootMultiplicity x
    let m := B.rootMultiplicity x
    (((2 : K) * e ≠ 3 * m) →
        (2 * derivative H * B - 3 * H * derivative B).rootMultiplicity x
          = e + m - 1)
      ∧ (((2 : K) * e = 3 * m) →
        e + m ≤
          (2 * derivative H * B - 3 * H * derivative B).rootMultiplicity x) := by
  dsimp only
  let L : K[X] := X - C x
  let e := H.rootMultiplicity x
  let m := B.rootMultiplicity x
  let H₀ := H /ₘ L ^ e
  let B₀ := B /ₘ L ^ m
  let R : K[X] :=
    C (2 * (e : K) - 3 * (m : K)) * H₀ * B₀
      + L * (2 * derivative H₀ * B₀ - 3 * H₀ * derivative B₀)
  have hHL : L ^ e * H₀ = H := by
    simpa [L, e, H₀] using H.pow_mul_divByMonic_rootMultiplicity_eq x
  have hBL : L ^ m * B₀ = B := by
    simpa [L, m, B₀] using B.pow_mul_divByMonic_rootMultiplicity_eq x
  have hH₀eval : eval x H₀ ≠ 0 := by
    simpa [L, e, H₀] using H.eval_divByMonic_pow_rootMultiplicity_ne_zero x hH
  have hB₀eval : eval x B₀ ≠ 0 := by
    simpa [L, m, B₀] using B.eval_divByMonic_pow_rootMultiplicity_ne_zero x hB
  have hpowDerivative (n : Nat) :
      L * derivative (L ^ n) = C (n : K) * L ^ n := by
    cases n with
    | zero => simp
    | succ n =>
        simp only [derivative_pow, Nat.add_sub_cancel,
          Nat.cast_add, Nat.cast_one]
        rw [show derivative L = 1 by simp [L]]
        simp only [mul_one]
        rw [pow_succ]
        ring
  have hHDerivative :
      L * derivative H = L ^ e * (C (e : K) * H₀ + L * derivative H₀) := by
    rw [← hHL, derivative_mul]
    rw [mul_add, ← mul_assoc, hpowDerivative]
    ring
  have hBDerivative :
      L * derivative B = L ^ m * (C (m : K) * B₀ + L * derivative B₀) := by
    rw [← hBL, derivative_mul]
    rw [mul_add, ← mul_assoc, hpowDerivative]
    ring
  have hfactor :
      L * (2 * derivative H * B - 3 * H * derivative B) = L ^ (e + m) * R := by
    calc
      L * (2 * derivative H * B - 3 * H * derivative B)
          = 2 * (L * derivative H) * B - 3 * H * (L * derivative B) := by ring
      _ = 2 * (L ^ e * (C (e : K) * H₀ + L * derivative H₀)) * (L ^ m * B₀)
            - 3 * (L ^ e * H₀) * (L ^ m * (C (m : K) * B₀ + L * derivative B₀)) := by
          rw [hHDerivative, hBDerivative, hHL, hBL]
      _ = L ^ (e + m) * R := by
        rw [pow_add]
        dsimp [R]
        simp only [map_sub, map_mul, map_ofNat, map_natCast]
        ring
  have hL : L ≠ 0 := by simpa [L] using X_sub_C_ne_zero x
  have hLW : L * (2 * derivative H * B - 3 * H * derivative B) ≠ 0 :=
    mul_ne_zero hL hW
  have hpowR : L ^ (e + m) * R ≠ 0 := hfactor ▸ hLW
  have hR : R ≠ 0 := right_ne_zero_of_mul hpowR
  have hrmFactor := congrArg (rootMultiplicity x) hfactor
  rw [rootMultiplicity_mul hLW, rootMultiplicity_mul hpowR,
    rootMultiplicity_X_sub_C_self, rootMultiplicity_X_sub_C_pow] at hrmFactor
  constructor
  · intro hcoefficient
    have hReval : eval x R ≠ 0 := by
      dsimp [R, L]
      simp only [eval_add, eval_mul, eval_C, eval_sub, eval_X, sub_self, zero_mul,
        ]
      simpa only [add_zero] using
        mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hcoefficient) hH₀eval) hB₀eval
    have hRroot : ¬ R.IsRoot x := by simpa [IsRoot] using hReval
    have hRmult : R.rootMultiplicity x = 0 := rootMultiplicity_eq_zero hRroot
    rw [hRmult, add_zero] at hrmFactor
    omega
  · intro hcoefficient
    have hRroot : R.IsRoot x := by
      dsimp [R, L]
      simp only [IsRoot, eval_add, eval_mul, eval_C, eval_sub, eval_X, sub_self,
        zero_mul]
      rw [sub_eq_zero.mpr hcoefficient]
      simp
    have hRpos : 0 < R.rootMultiplicity x := (rootMultiplicity_pos hR).mpr hRroot
    omega

/-- Every finite point in the support of a polynomial solution of the cleared
shifted Davenport--Stothers ODE belongs simultaneously to the core and the
denominator.  Its two orders are necessarily `3 + 7k` and `2 + 5k` with
`k > 0`.  In particular, the resonant cancellation `2e = 3m` is impossible. -/
theorem GCD369ShiftedDSFinitePlace {K : Type*} [Field K] [CharZero K]
    (H B : K[X]) (c j : K) (hH : H ≠ 0) (hB : B ≠ 0) (hc : c ≠ 0) (hj : j ≠ 0)
    (hODE :
      C c * H ^ 4 * (2 * derivative H * B - 3 * H * derivative B)
        = C j * B ^ 8)
    (x : K) (hx : H.IsRoot x ∨ B.IsRoot x) :
    ∃ k : Nat, 0 < k ∧ H.rootMultiplicity x = 3 + 7 * k
      ∧ B.rootMultiplicity x = 2 + 5 * k := by
  let W := 2 * derivative H * B - 3 * H * derivative B
  have hB8 : B ^ 8 ≠ 0 := pow_ne_zero 8 hB
  have hjC : C j ≠ 0 := C_ne_zero.mpr hj
  have hright : C j * B ^ 8 ≠ 0 := mul_ne_zero hjC hB8
  have hW : W ≠ 0 := by
    intro hWzero
    change C c * H ^ 4 * W = C j * B ^ 8 at hODE
    rw [hWzero, mul_zero] at hODE
    exact hright hODE.symm
  let e := H.rootMultiplicity x
  let m := B.rootMultiplicity x
  have hsupport : 0 < e + m := by
    rcases hx with hxH | hxB
    · have : 0 < e := by simpa [e] using (rootMultiplicity_pos hH).mpr hxH
      omega
    · have : 0 < m := by simpa [m] using (rootMultiplicity_pos hB).mpr hxB
      omega
  have hpowMultiplicity (P : K[X]) (hP : P ≠ 0) (n : Nat) :
      (P ^ n).rootMultiplicity x = n * P.rootMultiplicity x := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hP) hP), ih]
        simp [Nat.succ_mul]
  have hcC : (C c : K[X]) ≠ 0 := C_ne_zero.mpr hc
  have hleftInner : C c * H ^ 4 ≠ 0 := mul_ne_zero hcC (pow_ne_zero 4 hH)
  have hleft : C c * H ^ 4 * W ≠ 0 := mul_ne_zero hleftInner hW
  have hmult := congrArg (rootMultiplicity x) hODE
  rw [rootMultiplicity_mul hleft, rootMultiplicity_mul hleftInner,
    rootMultiplicity_C, hpowMultiplicity H hH,
    rootMultiplicity_mul hright, rootMultiplicity_C,
    hpowMultiplicity B hB] at hmult
  simp only [zero_add] at hmult
  change 4 * e + W.rootMultiplicity x = 8 * m at hmult
  have hlocal := GCD369WeightedWronskianLocal H B x hH hB (by simpa [W] using hW)
    (by simpa [e, m] using hsupport)
  dsimp only at hlocal
  by_cases hresonant : (2 : K) * e = 3 * m
  · have hresonantNat : 2 * e = 3 * m := by exact_mod_cast hresonant
    have hlower : e + m ≤ W.rootMultiplicity x := by
      simpa [W, e, m] using hlocal.2 hresonant
    omega
  · have horder : W.rootMultiplicity x = e + m - 1 := by
      simpa [W, e, m] using hlocal.1 hresonant
    have harithmetic : 5 * e = 7 * m + 1 := by omega
    let k := e / 7
    have hremainder : e % 7 = 3 := by
      have hdecomp := Nat.mod_add_div e 7
      have hlt := Nat.mod_lt e (by norm_num : 0 < 7)
      omega
    have he : e = 3 + 7 * k := by
      have hdecomp := Nat.mod_add_div e 7
      dsimp [k]
      omega
    have hm : m = 2 + 5 * k := by omega
    have hresonantNat : 2 * e ≠ 3 * m := by
      intro h
      apply hresonant
      exact_mod_cast h
    have hk : 0 < k := by omega
    exact ⟨k, hk, by simpa [e] using he, by simpa [m] using hm⟩

/-- Degree at infinity of the weighted Wronskian.  The only possible leading
cancellation is the explicit resonance `2 deg(H) = 3 deg(B)`. -/
theorem GCD369WeightedWronskianDegree {K : Type*} [Field K] [CharZero K]
    (H B : K[X]) (hH : H ≠ 0) (hB : B ≠ 0)
    (hHdegree : 0 < H.natDegree) (hBdegree : 0 < B.natDegree)
    (hnonresonant :
      (2 : K) * (H.natDegree : K) ≠ 3 * (B.natDegree : K)) :
    (2 * derivative H * B - 3 * H * derivative B).natDegree
      = H.natDegree + B.natDegree - 1 := by
  let n := H.natDegree + B.natDegree - 1
  let W := 2 * derivative H * B - 3 * H * derivative B
  have hHderivativeDegree : (derivative H).natDegree = H.natDegree - 1 :=
    natDegree_derivative H
  have hBderivativeDegree : (derivative B).natDegree = B.natDegree - 1 :=
    natDegree_derivative B
  have hfirstCoeff :
      (derivative H * B).coeff n
        = H.leadingCoeff * (H.natDegree : K) * B.leadingCoeff := by
    calc
      (derivative H * B).coeff n =
          (derivative H * B).coeff ((derivative H).natDegree + B.natDegree) := by
            congr 1
            dsimp [n]
            omega
      _ = (derivative H).leadingCoeff * B.leadingCoeff :=
        coeff_mul_degree_add_degree _ _
      _ = H.leadingCoeff * (H.natDegree : K) * B.leadingCoeff := by
        rw [leadingCoeff_derivative]
  have hsecondCoeff :
      (H * derivative B).coeff n
        = H.leadingCoeff * B.leadingCoeff * (B.natDegree : K) := by
    calc
      (H * derivative B).coeff n =
          (H * derivative B).coeff (H.natDegree + (derivative B).natDegree) := by
            congr 1
            dsimp [n]
            omega
      _ = H.leadingCoeff * (derivative B).leadingCoeff :=
        coeff_mul_degree_add_degree _ _
      _ = H.leadingCoeff * B.leadingCoeff * (B.natDegree : K) := by
        rw [leadingCoeff_derivative]
        ring
  have hWform : W = C 2 * (derivative H * B) - C 3 * (H * derivative B) := by
    dsimp [W]
    norm_num [C_ofNat]
    ring
  have hcoefficient : W.coeff n ≠ 0 := by
    rw [hWform, coeff_sub, coeff_C_mul, coeff_C_mul, hfirstCoeff, hsecondCoeff]
    have hHleading : H.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hH
    have hBleading : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hB
    have hproduct :
        H.leadingCoeff * B.leadingCoeff
            * ((2 : K) * (H.natDegree : K) - 3 * (B.natDegree : K)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hHleading hBleading) (sub_ne_zero.mpr hnonresonant)
    convert hproduct using 1 <;> ring
  have hdegreeUpper : W.natDegree ≤ n := by
    rw [hWform]
    refine (natDegree_sub_le _ _).trans ?_
    rw [max_le_iff]
    constructor
    · refine (natDegree_C_mul_le _ _).trans ?_
      refine (natDegree_mul_le).trans ?_
      dsimp [n]
      omega
    · refine (natDegree_C_mul_le _ _).trans ?_
      refine (natDegree_mul_le).trans ?_
      dsimp [n]
      omega
  exact natDegree_eq_of_le_of_coeff_ne_zero hdegreeUpper hcoefficient

/-- Global closure of the cleared shifted Davenport--Stothers ODE.  Over an
algebraically closed characteristic-zero field, a nonconstant polynomial core
whose degree is divisible by three has exactly one finite zero; the local
orders are `3 + 7k` and `2 + 5k` with `k > 0`, and the core is a polynomial
cube.  No finite-place support or exponent classification is assumed. -/
theorem GCD369ShiftedDSPolynomialCube {K : Type*} [Field K] [CharZero K]
    [IsAlgClosed K] (H B : K[X]) (c j : K)
    (hH : H ≠ 0) (hB : B ≠ 0) (hc : c ≠ 0) (hj : j ≠ 0)
    (hHdegree : 0 < H.natDegree) (hdegreeDiv : 3 ∣ H.natDegree)
    (hODE :
      C c * H ^ 4 * (2 * derivative H * B - 3 * H * derivative B)
        = C j * B ^ 8) :
    ∃ a : K, ∃ k : Nat, ∃ u : K[X], 0 < k
      ∧ H = C H.leadingCoeff * (X - C a) ^ (3 + 7 * k)
      ∧ B = C B.leadingCoeff * (X - C a) ^ (2 + 5 * k)
      ∧ H = u ^ 3 := by
  classical
  let W := 2 * derivative H * B - 3 * H * derivative B
  have hB8 : B ^ 8 ≠ 0 := pow_ne_zero 8 hB
  have hjC : C j ≠ 0 := C_ne_zero.mpr hj
  have hright : C j * B ^ 8 ≠ 0 := mul_ne_zero hjC hB8
  have hW : W ≠ 0 := by
    intro hWzero
    change C c * H ^ 4 * W = C j * B ^ 8 at hODE
    rw [hWzero, mul_zero] at hODE
    exact hright hODE.symm
  have hHdegree' : H.degree ≠ 0 :=
    ne_of_gt (natDegree_pos_iff_degree_pos.mp hHdegree)
  obtain ⟨x₀, hx₀⟩ := IsAlgClosed.exists_root H hHdegree'
  have hx₀class :=
    GCD369ShiftedDSFinitePlace H B c j hH hB hc hj hODE x₀ (Or.inl hx₀)
  obtain ⟨k₀, hk₀, _, hx₀Bmult⟩ := hx₀class
  have hx₀B : B.IsRoot x₀ := by
    apply (rootMultiplicity_pos hB).mp
    rw [hx₀Bmult]
    omega
  have hBdegree : 0 < B.natDegree :=
    natDegree_pos_iff_degree_pos.mpr (degree_pos_of_root hB hx₀B)
  let S : Finset K := H.roots.toFinset ∪ B.roots.toFinset
  have hx₀S : x₀ ∈ S := by
    apply Finset.mem_union_left
    simpa [S] using (mem_roots hH).mpr hx₀
  have hSnonempty : S.Nonempty := ⟨x₀, hx₀S⟩
  have hclass (x : K) (hx : x ∈ S) :
      ∃ k : Nat, 0 < k ∧ H.rootMultiplicity x = 3 + 7 * k
        ∧ B.rootMultiplicity x = 2 + 5 * k := by
    have hx' : H.IsRoot x ∨ B.IsRoot x := by
      rw [Finset.mem_union] at hx
      rcases hx with hxH | hxB
      · exact Or.inl ((mem_roots hH).mp (by simpa [S] using hxH))
      · exact Or.inr ((mem_roots hB).mp (by simpa [S] using hxB))
    exact GCD369ShiftedDSFinitePlace H B c j hH hB hc hj hODE x hx'
  have hsumH : ∑ x ∈ S, H.rootMultiplicity x = H.natDegree := by
    calc
      ∑ x ∈ S, H.rootMultiplicity x = ∑ x ∈ S, H.roots.count x := by
        apply Finset.sum_congr rfl
        intro x _
        exact (count_roots H).symm
      _ = H.roots.card := by
        apply Multiset.sum_count_eq_card
        intro x hx
        apply Finset.mem_union_left
        simpa [S] using hx
      _ = H.natDegree := (IsAlgClosed.splits H).natDegree_eq_card_roots.symm
  have hsumB : ∑ x ∈ S, B.rootMultiplicity x = B.natDegree := by
    calc
      ∑ x ∈ S, B.rootMultiplicity x = ∑ x ∈ S, B.roots.count x := by
        apply Finset.sum_congr rfl
        intro x _
        exact (count_roots B).symm
      _ = B.roots.card := by
        apply Multiset.sum_count_eq_card
        intro x hx
        apply Finset.mem_union_right
        simpa [S] using hx
      _ = B.natDegree := (IsAlgClosed.splits B).natDegree_eq_card_roots.symm
  have hpointEquation (x : K) (hx : x ∈ S) :
      5 * H.rootMultiplicity x = 7 * B.rootMultiplicity x + 1 := by
    obtain ⟨k, _, he, hm⟩ := hclass x hx
    omega
  have hpointStrict (x : K) (hx : x ∈ S) :
      2 * H.rootMultiplicity x < 3 * B.rootMultiplicity x := by
    obtain ⟨k, hk, he, hm⟩ := hclass x hx
    omega
  have hsumEquation : 5 * H.natDegree = 7 * B.natDegree + S.card := by
    have hsum := Finset.sum_congr rfl hpointEquation
    rw [Finset.sum_add_distrib] at hsum
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
    have hfive : (∑ x ∈ S, 5 * H.rootMultiplicity x) = 5 * H.natDegree := by
      rw [← Finset.mul_sum, hsumH]
    have hseven : (∑ x ∈ S, 7 * B.rootMultiplicity x) = 7 * B.natDegree := by
      rw [← Finset.mul_sum, hsumB]
    rw [hfive, hseven] at hsum
    exact hsum
  have hdegreeStrict : 2 * H.natDegree < 3 * B.natDegree := by
    have hsumStrict := Finset.sum_lt_sum_of_nonempty hSnonempty hpointStrict
    rw [← Finset.mul_sum, ← Finset.mul_sum, hsumH, hsumB] at hsumStrict
    exact hsumStrict
  have hdegreeNonresonant :
      (2 : K) * (H.natDegree : K) ≠ 3 * (B.natDegree : K) := by
    have hne : 2 * H.natDegree ≠ 3 * B.natDegree := ne_of_lt hdegreeStrict
    exact_mod_cast hne
  have hWdegree : W.natDegree = H.natDegree + B.natDegree - 1 := by
    simpa [W] using GCD369WeightedWronskianDegree H B hH hB hHdegree hBdegree
      hdegreeNonresonant
  have hcC : C c ≠ (0 : K[X]) := C_ne_zero.mpr hc
  have hleftInner : C c * H ^ 4 ≠ 0 := mul_ne_zero hcC (pow_ne_zero 4 hH)
  have hleft : C c * H ^ 4 * W ≠ 0 := mul_ne_zero hleftInner hW
  have hdegreeODE := congrArg natDegree hODE
  rw [natDegree_mul hleftInner hW, natDegree_mul hcC (pow_ne_zero 4 hH),
    natDegree_C, natDegree_pow, natDegree_mul hjC hB8, natDegree_C,
    natDegree_pow] at hdegreeODE
  simp only [zero_add] at hdegreeODE
  change 4 * H.natDegree + W.natDegree = 8 * B.natDegree at hdegreeODE
  have hdegreeEquation : 5 * H.natDegree = 7 * B.natDegree + 1 := by omega
  have hScard : S.card = 1 := by omega
  obtain ⟨a, hS⟩ := Finset.card_eq_one.mp hScard
  have haS : a ∈ S := by simp [hS]
  obtain ⟨k, hk, haHmult, haBmult⟩ := hclass a haS
  have hrootsH : H.roots = Multiset.replicate H.roots.card a := by
    apply Multiset.eq_replicate_of_mem
    intro b hb
    have hbS : b ∈ S := by
      apply Finset.mem_union_left
      simpa [S] using hb
    rw [hS] at hbS
    simpa using hbS
  have hrootsB : B.roots = Multiset.replicate B.roots.card a := by
    apply Multiset.eq_replicate_of_mem
    intro b hb
    have hbS : b ∈ S := by
      apply Finset.mem_union_right
      simpa [S] using hb
    rw [hS] at hbS
    simpa using hbS
  have hHcard : H.roots.card = H.rootMultiplicity a := by
    rw [← count_roots H, hrootsH]
    simp
  have hBcard : B.roots.card = B.rootMultiplicity a := by
    rw [← count_roots B, hrootsB]
    simp
  have hHform : H = C H.leadingCoeff * (X - C a) ^ (3 + 7 * k) := by
    calc
      H = C H.leadingCoeff * (H.roots.map fun x => X - C x).prod :=
        (IsAlgClosed.splits H).eq_prod_roots
      _ = C H.leadingCoeff * (X - C a) ^ (3 + 7 * k) := by
        rw [hrootsH]
        simp only [Multiset.map_replicate, Multiset.prod_replicate]
        rw [hHcard, haHmult]
  have hBform : B = C B.leadingCoeff * (X - C a) ^ (2 + 5 * k) := by
    calc
      B = C B.leadingCoeff * (B.roots.map fun x => X - C x).prod :=
        (IsAlgClosed.splits B).eq_prod_roots
      _ = C B.leadingCoeff * (X - C a) ^ (2 + 5 * k) := by
        rw [hrootsB]
        simp only [Multiset.map_replicate, Multiset.prod_replicate]
        rw [hBcard, haBmult]
  have hdivLocal : 3 ∣ 3 + 7 * k := by
    rw [← haHmult, ← hHcard, ← (IsAlgClosed.splits H).natDegree_eq_card_roots]
    exact hdegreeDiv
  obtain ⟨ell, hkMultiple⟩ : ∃ ell : Nat, k = 3 * ell := by
    have hprod : 3 ∣ 7 * k := (Nat.dvd_add_iff_right (dvd_refl 3)).mpr hdivLocal
    have hkdiv : 3 ∣ k :=
      (by norm_num : Nat.Coprime 3 7).dvd_of_dvd_mul_left hprod
    rcases hkdiv with ⟨ell, rfl⟩
    exact ⟨ell, rfl⟩
  obtain ⟨root, hroot⟩ :=
    IsAlgClosed.exists_pow_nat_eq H.leadingCoeff (by norm_num : 0 < 3)
  let u : K[X] := C root * (X - C a) ^ (1 + 7 * ell)
  have hu : C H.leadingCoeff * (X - C a) ^ (3 + 7 * k) = u ^ 3 := by
    dsimp [u]
    rw [hkMultiple, mul_pow, ← C_pow, hroot]
    congr 1
    rw [← pow_mul]
    congr 1
    omega
  exact ⟨a, k, u, hk, hHform, hBform, hHform.trans hu⟩

/-- In a reduced presentation `q = N / B` with `B ≠ 0`, the cleared shifted
Davenport--Stothers ODE forces the numerator `N` to be constant.  A root of a
nonconstant numerator would annihilate the left side while reducedness keeps
the right side nonzero. -/
theorem GCD369ShiftedDSNumeratorConstant {K : Type*} [Field K] [CharZero K]
    [IsAlgClosed K] (H N B : K[X]) (j : K)
    (hB : B ≠ 0) (hj : j ≠ 0)
    (hreduced : ∀ x : K, eval x N = 0 → eval x B ≠ 0)
    (hODE :
      C 189 * H ^ 4 * N ^ 6
          * (2 * derivative H * N * B
            + 3 * H * (derivative N * B - N * derivative B))
        = C j * B ^ 8) :
    N.natDegree = 0 := by
  by_contra hdegree
  have hdegreePos : 0 < N.degree := by
    rw [← natDegree_pos_iff_degree_pos]
    omega
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root N (ne_of_gt hdegreePos)
  have hxB : eval x B ≠ 0 := hreduced x hx
  have heval := congrArg (eval x) hODE
  simp only [eval_mul, eval_pow, eval_C] at heval
  rw [hx, zero_pow (by norm_num : (6 : Nat) ≠ 0), mul_zero, zero_mul] at heval
  have hright : j * eval x B ^ 8 ≠ 0 := mul_ne_zero hj (pow_ne_zero 8 hxB)
  exact hright heval.symm

/-- Complete valuation closure for a reduced rational trajectory
`q = N / B`.  The ODE itself makes `N` constant, identifies the unique common
finite support point and both local exponents, and proves that a core of
degree divisible by three is a cube. -/
theorem GCD369ShiftedDSRationalCube {K : Type*} [Field K] [CharZero K]
    [IsAlgClosed K] (H N B : K[X]) (j : K)
    (hH : H ≠ 0) (hN : N ≠ 0) (hB : B ≠ 0) (hj : j ≠ 0)
    (hHdegree : 0 < H.natDegree) (hdegreeDiv : 3 ∣ H.natDegree)
    (hreduced : ∀ x : K, eval x N = 0 → eval x B ≠ 0)
    (hODE :
      C 189 * H ^ 4 * N ^ 6
          * (2 * derivative H * N * B
            + 3 * H * (derivative N * B - N * derivative B))
        = C j * B ^ 8) :
    ∃ n a : K, ∃ k : Nat, ∃ u : K[X], n ≠ 0 ∧ N = C n ∧ 0 < k
      ∧ H = C H.leadingCoeff * (X - C a) ^ (3 + 7 * k)
      ∧ B = C B.leadingCoeff * (X - C a) ^ (2 + 5 * k)
      ∧ H = u ^ 3 := by
  have hNdegree :=
    GCD369ShiftedDSNumeratorConstant H N B j hB hj hreduced hODE
  let n := N.coeff 0
  have hNconstant : N = C n := by
    exact eq_C_of_natDegree_le_zero (Nat.le_zero.mpr hNdegree)
  have hn : n ≠ 0 := by
    intro hnzero
    rw [hNconstant, hnzero, C_0] at hN
    exact hN rfl
  let W := 2 * derivative H * B - 3 * H * derivative B
  have hODE' : C (189 * n ^ 7) * H ^ 4 * W = C j * B ^ 8 := by
    rw [hNconstant] at hODE
    dsimp [W]
    simp only [derivative_C, zero_mul, zero_sub, C_mul, C_pow] at hODE ⊢
    convert hODE using 1 <;> ring
  have hc : 189 * n ^ 7 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 7 hn)
  obtain ⟨a, k, u, hk, hHform, hBform, hcube⟩ :=
    GCD369ShiftedDSPolynomialCube H B (189 * n ^ 7) j hH hB hc hj hHdegree
      hdegreeDiv hODE'
  exact ⟨n, a, k, u, hn, hNconstant, hk, hHform, hBform, hcube⟩

/-- The shifted Davenport--Stothers sheet has no reduced rational trajectory
in the noncube Kummer branch.  Unlike version 1, this theorem assumes neither
the finite-place exponent classification nor the one-point support result:
both are derived from the cleared ODE by the preceding theorems. -/
theorem GCD369ShiftedDSNoncubeExclusion {K : Type*} [Field K] [CharZero K]
    [IsAlgClosed K] (H N B : K[X]) (j : K)
    (hH : H ≠ 0) (hN : N ≠ 0) (hB : B ≠ 0) (hj : j ≠ 0)
    (hdegreeDiv : 3 ∣ H.natDegree)
    (hnoncube : ¬ ∃ u : K[X], H = u ^ 3)
    (hreduced : ∀ x : K, eval x N = 0 → eval x B ≠ 0)
    (hODE :
      C 189 * H ^ 4 * N ^ 6
          * (2 * derivative H * N * B
            + 3 * H * (derivative N * B - N * derivative B))
        = C j * B ^ 8) : False := by
  have hHdegree : 0 < H.natDegree := by
    by_contra hnotPositive
    have hdegreeZero : H.natDegree = 0 := by omega
    have hconstant : H = C (H.coeff 0) :=
      eq_C_of_natDegree_le_zero (Nat.le_zero.mpr hdegreeZero)
    obtain ⟨root, hroot⟩ :=
      IsAlgClosed.exists_pow_nat_eq (H.coeff 0) (by norm_num : 0 < 3)
    apply hnoncube
    refine ⟨C root, ?_⟩
    rw [hconstant, ← C_pow, hroot]
  obtain ⟨_, _, _, u, _, _, _, _, _, hcube⟩ :=
    GCD369ShiftedDSRationalCube H N B j hH hN hB hj hHdegree hdegreeDiv
      hreduced hODE
  exact hnoncube ⟨u, hcube⟩

/-- The infinity-degree arithmetic in the shifted Davenport--Stothers
valuation classification forces a single finite support point. -/
theorem GCD369DSInfinitySupport (r totalK Hdeg Bdeg : Nat)
    (hH : Hdeg = 3 * r + 7 * totalK) (hB : Bdeg = 2 * r + 5 * totalK)
    (hdegree : 5 * Hdeg = 7 * Bdeg + 1) : r = 1 := by
  omega

/-- Once the one-point valuation classification has exponent `3+7k`, the
historical divisibility by three makes the polynomial Kummer core a cube.
The algebraic-closedness hypothesis is used only to extract a cube root of
the leading scalar. -/
theorem GCD369DSOneRootCube {K : Type*} [Field K] [IsAlgClosed K]
    (c a : K) (k : Nat) (hdiv : 3 ∣ 3 + 7 * k) :
    ∃ u : K[X], C c * (X - C a) ^ (3 + 7 * k) = u ^ 3 := by
  obtain ⟨ell, hk⟩ : ∃ ell : Nat, k = 3 * ell := by
    have hprod : 3 ∣ 7 * k := (Nat.dvd_add_iff_right (dvd_refl 3)).mpr hdiv
    have hkdiv : 3 ∣ k :=
      (by norm_num : Nat.Coprime 3 7).dvd_of_dvd_mul_left hprod
    rcases hkdiv with ⟨ell, rfl⟩
    exact ⟨ell, rfl⟩
  obtain ⟨root, hroot⟩ := IsAlgClosed.exists_pow_nat_eq c (by norm_num : 0 < 3)
  refine ⟨C root * (X - C a) ^ (1 + 7 * ell), ?_⟩
  rw [hk, mul_pow, ← C_pow, hroot]
  congr 1
  rw [← pow_mul]
  congr 1
  omega

#print axioms GCD369InvariantFibreDichotomy
#print axioms GCD369ZeroBracketSheet
#print axioms GCD369EllipticSheetEquation
#print axioms GCD369EllipticTerminalForm
#print axioms GCD369ForbiddenNumerator
#print axioms GCD369EllipticNonzeroExclusion
#print axioms GCD369SpecialFibreDichotomy
#print axioms GCD369ShiftedDSBracket
#print axioms GCD369ShiftedDSTerminalDescent
#print axioms GCD369WeightedWronskianLocal
#print axioms GCD369ShiftedDSFinitePlace
#print axioms GCD369WeightedWronskianDegree
#print axioms GCD369ShiftedDSPolynomialCube
#print axioms GCD369ShiftedDSNumeratorConstant
#print axioms GCD369ShiftedDSRationalCube
#print axioms GCD369ShiftedDSNoncubeExclusion
#print axioms GCD369DSInfinitySupport
#print axioms GCD369DSOneRootCube
