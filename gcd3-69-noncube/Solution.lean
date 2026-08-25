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
it does not prove converse inclusions or existence of either sheet.
-/

open Polynomial

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
#print axioms GCD369DSInfinitySupport
#print axioms GCD369DSOneRootCube
