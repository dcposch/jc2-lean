/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch (direction), OpenAI Codex agent (formalization)
-/
import Mathlib

/-!
# Polynomial-cube `(6,9)` trajectory certificates

Kernel-checked algebraic certificates from the polynomial-cube branch of the
partial-degree `(6,9)` reduction.
-/

open Polynomial

/-- The five polynomial parts multiplying the derivatives of the first five
negative Laurent coefficients form a triangular basis.  Consequently a
constant terminal row is equivalent to four first integrals and the displayed
fifth derivative. -/
theorem GCD369CubeLowerRowTriangularity {K : Type*} [Field K] [CharZero K]
    (a2 a3 a4 u1 u2 u3 u4 u5 q : K) :
    let A1 : K[X] :=
      monomial 4 6 + monomial 2 (3 * a4) + monomial 1 (2 * a3)
        + monomial 0 (a2 - a4 ^ 2 / 12)
    let A2 : K[X] := monomial 3 6 + monomial 1 (2 * a4) + monomial 0 a3
    let A3 : K[X] := monomial 2 6 + monomial 0 a4
    let A4 : K[X] := monomial 1 6
    let A5 : K[X] := monomial 0 6
    u1 • A1 + u2 • A2 + u3 • A3 + u4 • A4 + u5 • A5 = C q ↔
      u1 = 0 ∧ u2 = 0 ∧ u3 = 0 ∧ u4 = 0 ∧ 6 * u5 = q := by
  dsimp
  constructor
  · intro h
    have h4 := congrArg (fun p : K[X] => p.coeff 4) h
    have h3 := congrArg (fun p : K[X] => p.coeff 3) h
    have h2 := congrArg (fun p : K[X] => p.coeff 2) h
    have h1 := congrArg (fun p : K[X] => p.coeff 1) h
    have h0 := congrArg (fun p : K[X] => p.coeff 0) h
    norm_num [coeff_add, coeff_smul, coeff_monomial] at h4 h3 h2 h1 h0
    have hu1 : u1 = 0 := h4
    have hu2 : u2 = 0 := h3
    have hu3 : u3 = 0 := by
      rw [hu1] at h2
      norm_num at h2
      exact h2
    have hu4 : u4 = 0 := by
      rw [hu1, hu2] at h1
      norm_num at h1
      exact h1
    refine ⟨hu1, hu2, hu3, hu4, ?_⟩
    simpa [hu1, hu2, hu3, hu4, mul_comm] using h0
  · rintro ⟨rfl, rfl, rfl, rfl, h5⟩
    simp only [zero_smul, zero_add]
    simpa [mul_comm] using congrArg C h5

/-- The common-cubic `P_A` sheet has identically zero source bracket, for an
arbitrary moving cubic and arbitrary constant deformation. -/
theorem GCD369CubeZeroSheetBracket {K : Type*} [Field K] [CharZero K]
    (Kpoly Kdot : K[X]) (eta : K) :
    let f := Kpoly ^ 2 + C eta
    let g := Kpoly ^ 3 + C (3 * eta / 2) * Kpoly
    let fdot := C 2 * Kpoly * Kdot
    let gdot := (C 3 * Kpoly ^ 2 + C (3 * eta / 2)) * Kdot
    fdot * derivative g - derivative f * gdot = 0 := by
  dsimp
  simp only [derivative_add, derivative_pow, derivative_C, derivative_mul]
  norm_num [C_div, C_mul, C_ofNat, C_eq_natCast]
  ring_nf

/-- The normalized Davenport--Stothers trajectory has the exact nonzero
bracket used by the cube-core terminal analysis. -/
theorem GCD369CubeDSBracket {K : Type*} [Field K] [CharZero K] (lambda : K) :
    let f : K[X] :=
      X ^ 6 + C (4 * lambda) * X ^ 4 + C (10 * lambda ^ 2) * X ^ 2
        + C (6 * lambda ^ 3)
    let g : K[X] :=
      X ^ 9 + C (6 * lambda) * X ^ 7 + C (21 * lambda ^ 2) * X ^ 5
        + C (35 * lambda ^ 3) * X ^ 3 + C (63 * lambda ^ 4 / 2) * X
    let fdot : K[X] :=
      C 4 * X ^ 4 + C (20 * lambda) * X ^ 2 + C (18 * lambda ^ 2)
    let gdot : K[X] :=
      C 6 * X ^ 7 + C (42 * lambda) * X ^ 5
        + C (105 * lambda ^ 2) * X ^ 3 + C (126 * lambda ^ 3) * X
    fdot * derivative g - derivative f * gdot = C (567 * lambda ^ 6) := by
  dsimp
  simp only [derivative_add, derivative_pow, derivative_X, derivative_C,
    derivative_mul, zero_mul, add_zero]
  apply Polynomial.funext
  intro z
  simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X,
    eval_zero, eval_one]
  ring

/-- A short Bezout certificate for the normalized DS boundary polynomials.
In particular, they have no common root over any characteristic-zero field. -/
theorem GCD369CubeDSBoundaryBezout {K : Type*} [Field K] [CharZero K] :
    let f : K[X] := X ^ 6 + C 4 * X ^ 4 + C 10 * X ^ 2 + C 6
    let g : K[X] :=
      X ^ 9 + C 6 * X ^ 7 + C 21 * X ^ 5 + C 35 * X ^ 3 + C (63 / 2) * X
    let U : K[X] := C 6 * X ^ 8 + C 28 * X ^ 6 + C 70 * X ^ 4
      + C 70 * X ^ 2 + C 21
    let V : K[X] := -(C 6 * X ^ 5 + C 16 * X ^ 3 + C 20 * X)
    U * f + V * g = C 126 ∧
      ∀ z : K, eval z f = 0 → eval z g = 0 → False := by
  dsimp
  constructor
  · apply Polynomial.funext
    intro z
    simp only [eval_add, eval_mul, eval_neg, eval_pow, eval_C, eval_X]
    ring
  · intro z hf hg
    have hbez :
        eval z
          ((C 6 * X ^ 8 + C 28 * X ^ 6 + C 70 * X ^ 4 + C 70 * X ^ 2 + C 21) *
              (X ^ 6 + C 4 * X ^ 4 + C 10 * X ^ 2 + C 6) +
            (-(C 6 * X ^ 5 + C 16 * X ^ 3 + C 20 * X)) *
              (X ^ 9 + C 6 * X ^ 7 + C 21 * X ^ 5 + C 35 * X ^ 3 +
                C (63 / 2) * X)) = eval z (C 126 : K[X]) := by
      congr 1
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_mul, eval_neg, eval_pow, eval_C, eval_X]
      ring
    simp only [eval_add, eval_mul, eval_neg, hf, hg, mul_zero, add_zero,
      eval_C] at hbez
    norm_num at hbez

/-- The unique double-root projective normal has an unavoidable third
invariant coefficient `-1/16`, independently of every next coefficient. -/
theorem GCD369CubeDoubleRootNormalObstruction {K : Type*} [Field K] [CharZero K]
    (S : K) :
    ¬ (3 * S / 4 = 0 ∧ 3 * S / 4 = 0 ∧ (-1 / 16 : K) = 0 ∧
      -(4 * S + 3) / 16 = 0) := by
  norm_num

/-- A point on the exceptional `d != 0` orbit polynomial cannot lie on the
double-root discriminant, except at the excluded affine origin. -/
theorem GCD369CubeExceptionalOrbitSquarefree {K : Type*} [Field K] [CharZero K]
    (u v : K) (hprojective : u ≠ 0 ∨ v ≠ 0)
    (horbit : 2 * u ^ 6 - 90 * u ^ 3 * v ^ 2 + 135 * v ^ 4 = 0) :
    4 * u ^ 3 + 27 * v ^ 2 ≠ 0 := by
  intro hdisc
  have hv4 : (6669 : K) * v ^ 4 = 0 := by
    linear_combination 8 * horbit - (4 * u ^ 3 - 207 * v ^ 2) * hdisc
  have hvpow : v ^ 4 = 0 := by
    have hc : (6669 : K) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hv4).resolve_left hc
  have hv : v = 0 := by
    by_contra hv
    exact (pow_ne_zero 4 hv) hvpow
  have hu3 : u ^ 3 = 0 := by
    rw [hv] at hdisc
    norm_num at hdisc ⊢
    exact hdisc
  have hu : u = 0 := by
    by_contra hu
    exact (pow_ne_zero 3 hu) hu3
  exact hprojective.elim (fun h => h hu) (fun h => h hv)

/-- The four forced quadratic rows for the normalized `d != 0` landing imply
the exact exceptional-orbit equation.  The proof is the explicit
ideal-membership certificate extracted from the deterministic Kuranishi
replay. -/
theorem GCD369CubeDExceptionalSupport {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K)
    (h1 :
      729 * u * Xn ^ 2 - 1458 * Xn * Zn - 729 * Yn ^ 2 +
          320 * u ^ 3 * v - 960 * v ^ 3 = 0)
    (h2 :
      -2187 * v * Xn ^ 2 - 4374 * u * Xn * Yn + 4374 * Yn * Zn +
          64 * u ^ 5 - 1440 * u ^ 2 * v ^ 2 = 0)
    (_h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (h4 :
      19683 * u * v * Xn ^ 2 + 13122 * u ^ 2 * Xn * Yn -
          26244 * v * Xn * Zn - 13122 * v * Yn ^ 2 -
          13122 * u * Yn * Zn + 160 * u ^ 6 - 5760 * u ^ 3 * v ^ 2 +
          6480 * v ^ 4 = 0) :
    2 * u ^ 6 - 90 * u ^ 3 * v ^ 2 + 135 * v ^ 4 = 0 := by
  linear_combination (-9 / 88 * v) * h1 + (3 / 176 * u) * h2 + (1 / 176) * h4

/-- Every nonzero projective point on the normalized `d != 0` exceptional
orbit has both common-cubic coordinates nonzero. -/
theorem GCD369CubeDExceptionalCoordinatesNonzero
    {K : Type*} [Field K] [CharZero K]
    (u v : K) (hprojective : u ≠ 0 ∨ v ≠ 0)
    (horbit : 2 * u ^ 6 - 90 * u ^ 3 * v ^ 2 + 135 * v ^ 4 = 0) :
    u ≠ 0 ∧ v ≠ 0 := by
  constructor
  · intro hu
    have hv4 : v ^ 4 = 0 := by
      rw [hu] at horbit
      norm_num at horbit ⊢
      exact horbit
    have hv : v = 0 := by
      by_contra hv
      exact (pow_ne_zero 4 hv) hv4
    exact hprojective.elim (fun h => h hu) (fun h => h hv)
  · intro hv
    have hu6 : u ^ 6 = 0 := by
      rw [hv] at horbit
      norm_num at horbit ⊢
      exact horbit
    have hu : u = 0 := by
      by_contra hu
      exact (pow_ne_zero 6 hu) hu6
    exact hprojective.elim (fun h => h hu) (fun h => h hv)

/-- On the normalized `d != 0` exceptional landing, the full forced terminal
coefficient cannot vanish on the `u != 0` chart.  Explicitly, vanishing would
force `u^11 = 0`. -/
theorem GCD369CubeDExceptionalTerminalNonzero
    {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K) (hu : u ≠ 0)
    (h1 :
      729 * u * Xn ^ 2 - 1458 * Xn * Zn - 729 * Yn ^ 2 +
          320 * u ^ 3 * v - 960 * v ^ 3 = 0)
    (h2 :
      -2187 * v * Xn ^ 2 - 4374 * u * Xn * Yn + 4374 * Yn * Zn +
          64 * u ^ 5 - 1440 * u ^ 2 * v ^ 2 = 0)
    (h4 :
      19683 * u * v * Xn ^ 2 + 13122 * u ^ 2 * Xn * Yn -
          26244 * v * Xn * Zn - 13122 * v * Yn ^ 2 -
          13122 * u * Yn * Zn + 160 * u ^ 6 - 5760 * u ^ 3 * v ^ 2 +
          6480 * v ^ 4 = 0) :
    -729 * u ^ 3 * Xn ^ 2 + 2187 * v ^ 2 * Xn ^ 2 +
        4374 * u * v * Xn * Yn + 1458 * u ^ 2 * Xn * Zn +
        729 * u ^ 2 * Yn ^ 2 - 4374 * v * Yn * Zn +
        320 * u ^ 5 * v - 2880 * u ^ 2 * v ^ 3 ≠ 0 := by
  intro hterminal
  have hu11 : u ^ 11 = 0 := by
    linear_combination
      (351 / 13376 * u ^ 5 * v + 1215 / 3344 * u ^ 2 * v ^ 3) * h1 +
      (3 / 352 * u ^ 6 - 45 / 13376 * u ^ 3 * v ^ 2 - 405 / 3344 * v ^ 4) * h2 +
      (1 / 352 * u ^ 5 - 45 / 1672 * u ^ 2 * v ^ 2) * h4 +
      (1035 / 13376 * u ^ 3 * v - 405 / 3344 * v ^ 3) * hterminal
  exact (pow_ne_zero 11 hu) hu11

/-- The localized unit certificate showing that the exceptional `d != 0`
normal cannot share a root with its common cubic. -/
theorem GCD369CubeDExceptionalNoCommonRootOnUChart
    {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn r Tin u v : K)
    (h1 :
      729 * u * Xn ^ 2 - 1458 * Xn * Zn - 729 * Yn ^ 2 +
          320 * u ^ 3 * v - 960 * v ^ 3 = 0)
    (h2 :
      -2187 * v * Xn ^ 2 - 4374 * u * Xn * Yn + 4374 * Yn * Zn +
          64 * u ^ 5 - 1440 * u ^ 2 * v ^ 2 = 0)
    (h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (h4 :
      19683 * u * v * Xn ^ 2 + 13122 * u ^ 2 * Xn * Yn -
          26244 * v * Xn * Zn - 13122 * v * Yn ^ 2 -
          13122 * u * Yn * Zn + 160 * u ^ 6 - 5760 * u ^ 3 * v ^ 2 +
          6480 * v ^ 4 = 0)
    (hK : r ^ 3 + u * r + v = 0)
    (hphi : Xn * r ^ 2 + Yn * r + Zn = 0)
    (hchart : Tin * u - 1 = 0) :
    False := by
  let C1 : K :=
    10935 / 43472 * r * Tin ^ 11 * v ^ 4 -
      405 / 1976 * Tin ^ 11 * u ^ 2 * v ^ 3 -
      27945 / 173888 * r * Tin ^ 8 * v ^ 2 +
      405 / 836 * Tin ^ 9 * v ^ 3 +
      1035 / 7904 * Tin ^ 8 * u ^ 2 * v - 9 / 176 * Tin ^ 6 * v
  let C2 : K :=
    -2025 / 21736 * r * Tin ^ 11 * u * v ^ 3 -
      1215 / 3952 * Tin ^ 11 * v ^ 4 +
      5175 / 86944 * r * Tin ^ 8 * u * v -
      135 / 1672 * Tin ^ 9 * u * v ^ 2 +
      3105 / 15808 * Tin ^ 8 * v ^ 2 + 3 / 352 * Tin ^ 6 * u
  let C3 : K :=
    885735 / 3952 * r ^ 2 * Tin ^ 11 * v ^ 3 +
      295245 / 3952 * Tin ^ 11 * u * v ^ 3 -
      2263545 / 15808 * r ^ 2 * Tin ^ 8 * v -
      754515 / 15808 * Tin ^ 8 * u * v
  let C4 : K :=
    405 / 10868 * r * Tin ^ 11 * v ^ 3 -
      1035 / 43472 * r * Tin ^ 8 * v -
      45 / 1672 * Tin ^ 9 * v ^ 2 + 1 / 352 * Tin ^ 6
  let C5 : K :=
    2657205 / 1976 * Xn * Yn * r ^ 2 * Tin ^ 11 * v ^ 3 -
      885735 / 1976 * Xn ^ 2 * r * Tin ^ 11 * u * v ^ 3 +
      2657205 / 1976 * Yn ^ 2 * r * Tin ^ 11 * v ^ 3 +
      2657205 / 3952 * Xn * Zn * r * Tin ^ 11 * v ^ 3 -
      2657205 / 3952 * Xn ^ 2 * Tin ^ 11 * v ^ 4 -
      885735 / 988 * Xn * Yn * Tin ^ 11 * u * v ^ 3 +
      7971615 / 3952 * Yn * Zn * Tin ^ 11 * v ^ 3 -
      6790635 / 7904 * Xn * Yn * r ^ 2 * Tin ^ 8 * v +
      2263545 / 7904 * Xn ^ 2 * r * Tin ^ 8 * u * v -
      6790635 / 7904 * Yn ^ 2 * r * Tin ^ 8 * v -
      6790635 / 15808 * Xn * Zn * r * Tin ^ 8 * v +
      6790635 / 15808 * Xn ^ 2 * Tin ^ 8 * v ^ 2 +
      2263545 / 3952 * Xn * Yn * Tin ^ 8 * u * v -
      20371905 / 15808 * Yn * Zn * Tin ^ 8 * v
  let C6 : K :=
    -2657205 / 1976 * Yn * r ^ 3 * Tin ^ 11 * v ^ 3 +
      885735 / 1976 * Xn * r ^ 2 * Tin ^ 11 * u * v ^ 3 -
      2657205 / 3952 * Zn * r ^ 2 * Tin ^ 11 * v ^ 3 +
      2657205 / 3952 * Xn * r * Tin ^ 11 * v ^ 4 -
      885735 / 988 * Yn * r * Tin ^ 11 * u * v ^ 3 +
      6790635 / 7904 * Yn * r ^ 3 * Tin ^ 8 * v -
      2657205 / 3952 * Yn * Tin ^ 11 * v ^ 4 -
      885735 / 3952 * Zn * Tin ^ 11 * u * v ^ 3 -
      2263545 / 7904 * Xn * r ^ 2 * Tin ^ 8 * u * v +
      6790635 / 15808 * Zn * r ^ 2 * Tin ^ 8 * v -
      6790635 / 15808 * Xn * r * Tin ^ 8 * v ^ 2 +
      2263545 / 3952 * Yn * r * Tin ^ 8 * u * v +
      6790635 / 15808 * Yn * Tin ^ 8 * v ^ 2 +
      2263545 / 15808 * Zn * Tin ^ 8 * u * v
  let C7 : K :=
    1620 / 19 * Tin ^ 10 * u ^ 4 * v ^ 4 -
      12150 / 19 * Tin ^ 10 * u * v ^ 6 +
      1620 / 19 * Tin ^ 9 * u ^ 3 * v ^ 4 -
      12150 / 19 * Tin ^ 9 * v ^ 6 +
      180 / 19 * Tin ^ 8 * u ^ 5 * v ^ 2 -
      6480 / 19 * Tin ^ 8 * u ^ 2 * v ^ 4 -
      45 * Tin ^ 7 * u ^ 4 * v ^ 2 + 135 / 2 * Tin ^ 7 * u * v ^ 4 -
      45 * Tin ^ 6 * u ^ 3 * v ^ 2 + 135 / 2 * Tin ^ 6 * v ^ 4 -
      Tin ^ 5 * u ^ 5 - Tin ^ 4 * u ^ 4 - Tin ^ 3 * u ^ 3 -
      Tin ^ 2 * u ^ 2 - Tin * u - 1
  have hone : (1 : K) = 0 := by
    linear_combination C1 * h1 + C2 * h2 + C3 * h3 + C4 * h4 +
      C5 * hK + C6 * hphi + C7 * hchart
  exact one_ne_zero hone

/-- The exceptional `d != 0` normal and its common cubic have no common
field-valued root on any nonzero projective landing. -/
theorem GCD369CubeDExceptionalNoCommonRoot
    {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K) (hu : u ≠ 0)
    (h1 :
      729 * u * Xn ^ 2 - 1458 * Xn * Zn - 729 * Yn ^ 2 +
          320 * u ^ 3 * v - 960 * v ^ 3 = 0)
    (h2 :
      -2187 * v * Xn ^ 2 - 4374 * u * Xn * Yn + 4374 * Yn * Zn +
          64 * u ^ 5 - 1440 * u ^ 2 * v ^ 2 = 0)
    (h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (h4 :
      19683 * u * v * Xn ^ 2 + 13122 * u ^ 2 * Xn * Yn -
          26244 * v * Xn * Zn - 13122 * v * Yn ^ 2 -
          13122 * u * Yn * Zn + 160 * u ^ 6 - 5760 * u ^ 3 * v ^ 2 +
          6480 * v ^ 4 = 0) :
    ∀ r : K, r ^ 3 + u * r + v = 0 →
      Xn * r ^ 2 + Yn * r + Zn = 0 → False := by
  intro r hK hphi
  exact GCD369CubeDExceptionalNoCommonRootOnUChart
    Xn Yn Zn r u⁻¹ u v h1 h2 h3 h4 hK hphi (by simp [hu])

/-- The first retained `c7` load is supported on exactly the candidate
projective divisor visible in its four Kuranishi rows. -/
theorem GCD369CubeC7Support {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K)
    (h1 :
      56 * u ^ 4 - 1008 * u * v ^ 2 + 729 * u * Xn ^ 2 -
          1458 * Xn * Zn - 729 * Yn ^ 2 = 0)
    (h2 :
      224 * u ^ 3 * v - 336 * v ^ 3 + 729 * v * Xn ^ 2 +
          1458 * u * Xn * Yn - 1458 * Yn * Zn = 0)
    (_h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (h4 :
      224 * u ^ 4 * v - 1008 * u * v ^ 3 - 2187 * u * v * Xn ^ 2 -
          1458 * u ^ 2 * Xn * Yn + 2916 * v * Xn * Zn +
          1458 * v * Yn ^ 2 + 1458 * u * Yn * Zn = 0) :
    u * v * (u ^ 3 - 6 * v ^ 2) = 0 := by
  linear_combination (1 / 280 * v) * h1 + (1 / 560 * u) * h2 + (1 / 560) * h4

/-- The full forced terminal coefficient on a first `c7` landing is nonzero
at every nonzero projective common-cubic point. -/
theorem GCD369CubeC7TerminalNonzero {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K) (hprojective : u ≠ 0 ∨ v ≠ 0)
    (h1 :
      56 * u ^ 4 - 1008 * u * v ^ 2 + 729 * u * Xn ^ 2 -
          1458 * Xn * Zn - 729 * Yn ^ 2 = 0)
    (h2 :
      224 * u ^ 3 * v - 336 * v ^ 3 + 729 * v * Xn ^ 2 +
          1458 * u * Xn * Yn - 1458 * Yn * Zn = 0)
    (h4 :
      224 * u ^ 4 * v - 1008 * u * v ^ 3 - 2187 * u * v * Xn ^ 2 -
          1458 * u ^ 2 * Xn * Yn + 2916 * v * Xn * Zn +
          1458 * v * Yn ^ 2 + 1458 * u * Yn * Zn = 0) :
    112 * u ^ 6 - 5040 * u ^ 3 * v ^ 2 + 4536 * v ^ 4 -
        2187 * u ^ 3 * Xn ^ 2 + 6561 * v ^ 2 * Xn ^ 2 +
        13122 * u * v * Xn * Yn + 4374 * u ^ 2 * Xn * Zn +
        2187 * u ^ 2 * Yn ^ 2 - 13122 * v * Yn * Zn ≠ 0 := by
  intro hterminal
  by_cases hu : u = 0
  · have hv : v ≠ 0 := hprojective.resolve_left (fun h => h hu)
    subst u
    have hv4 : v ^ 4 = 0 := by
      linear_combination (-1 / 840 * v) * h2 + (1 / 7560) * hterminal
    exact (pow_ne_zero 4 hv) hv4
  · have hu10 : u ^ 10 = 0 := by
      linear_combination
        (3 / 280 * u ^ 6 + 9 / 119 * u ^ 3 * v ^ 2 - 81 / 680 * v ^ 4) * h1 +
        (27 / 595 * u ^ 4 * v + 243 / 1360 * u * v ^ 3) * h2 +
        (369 / 4760 * u ^ 3 * v - 81 / 1360 * v ^ 3) * h4 +
        (1 / 280 * u ^ 4 - 9 / 340 * u * v ^ 2) * hterminal
    exact (pow_ne_zero 10 hu) hu10

/-- The `u=0`, `v!=0` chart certificate for a first-`c7` landing. -/
theorem GCD369CubeC7NoCommonRootOnUZeroChart
    {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn r Tin u v : K)
    (h1 :
      56 * u ^ 4 - 1008 * u * v ^ 2 + 729 * u * Xn ^ 2 -
          1458 * Xn * Zn - 729 * Yn ^ 2 = 0)
    (h2 :
      224 * u ^ 3 * v - 336 * v ^ 3 + 729 * v * Xn ^ 2 +
          1458 * u * Xn * Yn - 1458 * Yn * Zn = 0)
    (h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (_h4 :
      224 * u ^ 4 * v - 1008 * u * v ^ 3 - 2187 * u * v * Xn ^ 2 -
          1458 * u ^ 2 * Xn * Yn + 2916 * v * Xn * Zn +
          1458 * v * Yn ^ 2 + 1458 * u * Yn * Zn = 0)
    (hK : r ^ 3 + u * r + v = 0)
    (hphi : Xn * r ^ 2 + Yn * r + Zn = 0)
    (hu : u = 0) (hchart : Tin * v - 1 = 0) :
    False := by
  let C1 : K := -1 / 336 * r * Tin ^ 4 * v
  let C2 : K := -1 / 336 * Tin ^ 4 * v
  let C3 : K := -81 / 112 * r ^ 2 * Tin ^ 4
  let C5 : K :=
    -243 / 112 * Xn * Zn * r * Tin ^ 4 +
      243 / 112 * Xn ^ 2 * Tin ^ 4 * v - 243 / 112 * Yn * Zn * Tin ^ 4
  let C6 : K :=
    243 / 112 * Zn * r ^ 2 * Tin ^ 4 -
      243 / 112 * Xn * r * Tin ^ 4 * v - 243 / 112 * Yn * Tin ^ 4 * v
  let C7 : K :=
    81 / 56 * Xn ^ 2 * r ^ 2 * Tin ^ 4 * u +
      1 / 6 * r * Tin ^ 4 * u ^ 3 * v -
      81 / 56 * Yn ^ 2 * r ^ 2 * Tin ^ 4 -
      81 / 112 * Xn * Zn * r ^ 2 * Tin ^ 4 +
      2 / 3 * Tin ^ 4 * u ^ 2 * v ^ 2 - 3 * r * Tin ^ 4 * v ^ 3 +
      243 / 112 * Yn * Zn * r * Tin ^ 4 + 243 / 56 * Xn * Yn * Tin ^ 4 * v
  let C8 : K := -Tin ^ 3 * v ^ 3 - Tin ^ 2 * v ^ 2 - Tin * v - 1
  have hone : (1 : K) = 0 := by
    linear_combination C1 * h1 + C2 * h2 + C3 * h3 + C5 * hK +
      C6 * hphi + C7 * hu + C8 * hchart
  exact one_ne_zero hone

/-- The localized `u!=0` chart certificate for a first-`c7` landing. -/
theorem GCD369CubeC7NoCommonRootOnUChart
    {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn r Tin u v : K)
    (h1 :
      56 * u ^ 4 - 1008 * u * v ^ 2 + 729 * u * Xn ^ 2 -
          1458 * Xn * Zn - 729 * Yn ^ 2 = 0)
    (h2 :
      224 * u ^ 3 * v - 336 * v ^ 3 + 729 * v * Xn ^ 2 +
          1458 * u * Xn * Yn - 1458 * Yn * Zn = 0)
    (h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (h4 :
      224 * u ^ 4 * v - 1008 * u * v ^ 3 - 2187 * u * v * Xn ^ 2 -
          1458 * u ^ 2 * Xn * Yn + 2916 * v * Xn * Zn +
          1458 * v * Yn ^ 2 + 1458 * u * Yn * Zn = 0)
    (hK : r ^ 3 + u * r + v = 0)
    (hphi : Xn * r ^ 2 + Yn * r + Zn = 0)
    (hchart : Tin * u - 1 = 0) :
    False := by
  let C1 : K :=
    -81 / 680 * Tin ^ 10 * v ^ 4 + 27 / 170 * r * Tin ^ 9 * v ^ 3 +
      27 / 1190 * Tin ^ 7 * v ^ 2 - 3 / 140 * r * Tin ^ 6 * v +
      1 / 56 * Tin ^ 4
  let C2 : K :=
    -81 / 1360 * Tin ^ 10 * u * v ^ 3 -
      297 / 1360 * r * Tin ^ 9 * u * v ^ 2 + 81 / 136 * Tin ^ 9 * v ^ 3 +
      27 / 68 * r * Tin ^ 8 * v ^ 2 + 369 / 4760 * Tin ^ 7 * u * v +
      33 / 1120 * r * Tin ^ 6 * u - 9 / 112 * Tin ^ 6 * v -
      3 / 56 * r * Tin ^ 5
  let C3 : K :=
    19683 / 136 * r ^ 2 * Tin ^ 9 * v ^ 2 +
      6561 / 136 * Tin ^ 8 * v ^ 2 - 2187 / 112 * r ^ 2 * Tin ^ 6 -
      729 / 112 * Tin ^ 5
  let C4 : K :=
    -81 / 1360 * Tin ^ 10 * v ^ 3 - 297 / 1360 * r * Tin ^ 9 * v ^ 2 +
      369 / 4760 * Tin ^ 7 * v + 33 / 1120 * r * Tin ^ 6
  let C5 : K :=
    59049 / 136 * Xn * Zn * r * Tin ^ 9 * v ^ 2 -
      59049 / 136 * Xn ^ 2 * Tin ^ 9 * v ^ 3 -
      19683 / 68 * Xn ^ 2 * r * Tin ^ 8 * v ^ 2 +
      59049 / 136 * Yn * Zn * Tin ^ 9 * v ^ 2 -
      19683 / 34 * Xn * Yn * Tin ^ 8 * v ^ 2 -
      6561 / 112 * Xn * Zn * r * Tin ^ 6 +
      6561 / 112 * Xn ^ 2 * Tin ^ 6 * v +
      2187 / 56 * Xn ^ 2 * r * Tin ^ 5 -
      6561 / 112 * Yn * Zn * Tin ^ 6 + 2187 / 28 * Xn * Yn * Tin ^ 5
  let C6 : K :=
    -59049 / 136 * Zn * r ^ 2 * Tin ^ 9 * v ^ 2 +
      59049 / 136 * Xn * r * Tin ^ 9 * v ^ 3 +
      19683 / 68 * Xn * r ^ 2 * Tin ^ 8 * v ^ 2 -
      59049 / 136 * Zn * Tin ^ 9 * u * v ^ 2 +
      59049 / 136 * Yn * Tin ^ 9 * v ^ 3 +
      19683 / 68 * Yn * r * Tin ^ 8 * v ^ 2 +
      19683 / 68 * Zn * Tin ^ 8 * v ^ 2 +
      6561 / 112 * Zn * r ^ 2 * Tin ^ 6 -
      6561 / 112 * Xn * r * Tin ^ 6 * v -
      2187 / 56 * Xn * r ^ 2 * Tin ^ 5 +
      6561 / 112 * Zn * Tin ^ 6 * u - 6561 / 112 * Yn * Tin ^ 6 * v -
      2187 / 56 * Yn * r * Tin ^ 5 - 2187 / 56 * Zn * Tin ^ 5
  let C7 : K :=
    567 / 17 * Tin ^ 9 * u ^ 3 * v ^ 4 -
      19683 / 68 * Xn ^ 2 * r ^ 2 * Tin ^ 8 * u * v ^ 2 +
      1512 / 17 * r * Tin ^ 8 * u ^ 3 * v ^ 3 -
      3402 / 17 * Tin ^ 9 * v ^ 6 +
      19683 / 68 * Yn ^ 2 * r ^ 2 * Tin ^ 8 * v ^ 2 +
      19683 / 34 * Xn * Zn * r ^ 2 * Tin ^ 8 * v ^ 2 -
      1701 / 17 * Tin ^ 8 * u ^ 2 * v ^ 4 -
      2268 / 17 * r * Tin ^ 8 * v ^ 5 -
      59049 / 68 * Xn * Yn * Tin ^ 8 * v ^ 3 +
      59049 / 136 * Zn ^ 2 * Tin ^ 8 * v ^ 2 -
      6561 / 68 * Xn ^ 2 * Tin ^ 7 * u * v ^ 2 -
      1701 / 17 * Tin ^ 7 * u * v ^ 4 +
      6561 / 68 * Yn ^ 2 * Tin ^ 7 * v ^ 2 +
      6561 / 34 * Xn * Zn * Tin ^ 7 * v ^ 2 -
      36 * Tin ^ 6 * u ^ 3 * v ^ 2 +
      2187 / 56 * Xn ^ 2 * r ^ 2 * Tin ^ 5 * u -
      12 * r * Tin ^ 5 * u ^ 3 * v + 27 * Tin ^ 6 * v ^ 4 -
      2187 / 56 * Yn ^ 2 * r ^ 2 * Tin ^ 5 -
      2187 / 28 * Xn * Zn * r ^ 2 * Tin ^ 5 -
      18 * Tin ^ 5 * u ^ 2 * v ^ 2 + 18 * r * Tin ^ 5 * v ^ 3 +
      6561 / 56 * Xn * Yn * Tin ^ 5 * v -
      6561 / 112 * Zn ^ 2 * Tin ^ 5 + 729 / 56 * Xn ^ 2 * Tin ^ 4 * u -
      18 * Tin ^ 4 * u * v ^ 2 - 729 / 56 * Yn ^ 2 * Tin ^ 4 -
      729 / 28 * Xn * Zn * Tin ^ 4 - Tin ^ 3 * u ^ 3 -
      Tin ^ 2 * u ^ 2 - Tin * u - 1
  have hone : (1 : K) = 0 := by
    linear_combination C1 * h1 + C2 * h2 + C3 * h3 + C4 * h4 +
      C5 * hK + C6 * hphi + C7 * hchart
  exact one_ne_zero hone

/-- At every projective first-`c7` landing, the common cubic and its normal
have no common field-valued root. -/
theorem GCD369CubeC7NoCommonRoot {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K) (hprojective : u ≠ 0 ∨ v ≠ 0)
    (h1 :
      56 * u ^ 4 - 1008 * u * v ^ 2 + 729 * u * Xn ^ 2 -
          1458 * Xn * Zn - 729 * Yn ^ 2 = 0)
    (h2 :
      224 * u ^ 3 * v - 336 * v ^ 3 + 729 * v * Xn ^ 2 +
          1458 * u * Xn * Yn - 1458 * Yn * Zn = 0)
    (h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (h4 :
      224 * u ^ 4 * v - 1008 * u * v ^ 3 - 2187 * u * v * Xn ^ 2 -
          1458 * u ^ 2 * Xn * Yn + 2916 * v * Xn * Zn +
          1458 * v * Yn ^ 2 + 1458 * u * Yn * Zn = 0) :
    ∀ r : K, r ^ 3 + u * r + v = 0 →
      Xn * r ^ 2 + Yn * r + Zn = 0 → False := by
  intro r hK hphi
  by_cases hu : u = 0
  · have hv : v ≠ 0 := hprojective.resolve_left (fun h => h hu)
    exact GCD369CubeC7NoCommonRootOnUZeroChart
      Xn Yn Zn r v⁻¹ u v h1 h2 h3 h4 hK hphi hu (by simp [hv])
  · exact GCD369CubeC7NoCommonRootOnUChart
      Xn Yn Zn r u⁻¹ u v h1 h2 h3 h4 hK hphi (by simp [hu])

/-- The first retained `c5` load projects to
`v * (u^3 - 3*v^2) = 0`. -/
theorem GCD369CubeC5Support {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K)
    (h1 :
      40 * u ^ 3 - 360 * v ^ 2 + 243 * u * Xn ^ 2 -
          486 * Xn * Zn - 243 * Yn ^ 2 = 0)
    (h2 :
      40 * u ^ 2 * v + 81 * v * Xn ^ 2 + 162 * u * Xn * Yn -
          162 * Yn * Zn = 0)
    (_h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (h4 :
      40 * u ^ 3 * v - 80 * v ^ 3 - 243 * u * v * Xn ^ 2 -
          162 * u ^ 2 * Xn * Yn + 324 * v * Xn * Zn +
          162 * v * Yn ^ 2 + 162 * u * Yn * Zn = 0) :
    v * (u ^ 3 - 3 * v ^ 2) = 0 := by
  linear_combination (1 / 160 * v) * h1 + (3 / 320 * u) * h2 + (3 / 320) * h4

/-- The full forced terminal coefficient on a first `c5` landing is nonzero
at every nonzero projective common-cubic point. -/
theorem GCD369CubeC5TerminalNonzero {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K) (hprojective : u ≠ 0 ∨ v ≠ 0)
    (h1 :
      40 * u ^ 3 - 360 * v ^ 2 + 243 * u * Xn ^ 2 -
          486 * Xn * Zn - 243 * Yn ^ 2 = 0)
    (h2 :
      40 * u ^ 2 * v + 81 * v * Xn ^ 2 + 162 * u * Xn * Yn -
          162 * Yn * Zn = 0)
    (h4 :
      40 * u ^ 3 * v - 80 * v ^ 3 - 243 * u * v * Xn ^ 2 -
          162 * u ^ 2 * Xn * Yn + 324 * v * Xn * Zn +
          162 * v * Yn ^ 2 + 162 * u * Yn * Zn = 0) :
    8 * u ^ 5 - 240 * u ^ 2 * v ^ 2 - 81 * u ^ 3 * Xn ^ 2 +
        243 * v ^ 2 * Xn ^ 2 + 486 * u * v * Xn * Yn +
        162 * u ^ 2 * Xn * Zn + 81 * u ^ 2 * Yn ^ 2 -
        486 * v * Yn * Zn ≠ 0 := by
  intro hterminal
  by_cases hu : u = 0
  · have hv : v ≠ 0 := hprojective.resolve_left (fun h => h hu)
    subst u
    have hv3 : v ^ 3 = 0 := by
      linear_combination (-1 / 480 * v) * h1 + (-1 / 320) * h4
    exact (pow_ne_zero 3 hv) hv3
  · have hu8 : u ^ 8 = 0 := by
      linear_combination
        (1 / 64 * u ^ 5 + 45 / 416 * u ^ 2 * v ^ 2) * h1 +
        (171 / 1664 * u ^ 3 * v + 405 / 832 * v ^ 3) * h2 +
        (405 / 1664 * u ^ 2 * v) * h4 +
        (3 / 64 * u ^ 3 - 135 / 832 * v ^ 2) * hterminal
    exact (pow_ne_zero 8 hu) hu8

/-- The localized unit certificate showing that a first-`c5` normal cannot
share a root with its common cubic. -/
theorem GCD369CubeC5NoCommonRootOnUChart
    {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn r Tin u v : K)
    (h1 :
      40 * u ^ 3 - 360 * v ^ 2 + 243 * u * Xn ^ 2 -
          486 * Xn * Zn - 243 * Yn ^ 2 = 0)
    (h2 :
      40 * u ^ 2 * v + 81 * v * Xn ^ 2 + 162 * u * Xn * Yn -
          162 * Yn * Zn = 0)
    (h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (h4 :
      40 * u ^ 3 * v - 80 * v ^ 3 - 243 * u * v * Xn ^ 2 -
          162 * u ^ 2 * Xn * Yn + 324 * v * Xn * Zn +
          162 * v * Yn ^ 2 + 162 * u * Yn * Zn = 0)
    (hK : r ^ 3 + u * r + v = 0)
    (hphi : Xn * r ^ 2 + Yn * r + Zn = 0)
    (hchart : Tin * u - 1 = 0) :
    False := by
  let C1 : K :=
    81 / 832 * r * Tin ^ 8 * v ^ 3 - 9 / 104 * Tin ^ 8 * u ^ 2 * v ^ 2 -
      9 / 320 * r * Tin ^ 5 * v + 135 / 832 * Tin ^ 6 * v ^ 2 +
      1 / 40 * Tin ^ 5 * u ^ 2
  let C2 : K :=
    567 / 1664 * r * Tin ^ 8 * u * v ^ 2 + 243 / 208 * Tin ^ 8 * v ^ 3 -
      63 / 640 * r * Tin ^ 5 * u + 405 / 1664 * Tin ^ 6 * u * v -
      27 / 80 * Tin ^ 5 * v
  let C3 : K :=
    6561 / 208 * r ^ 2 * Tin ^ 8 * v ^ 2 +
      2187 / 208 * Tin ^ 8 * u * v ^ 2 - 729 / 80 * r ^ 2 * Tin ^ 5 -
      243 / 80 * Tin ^ 5 * u
  let C4 : K :=
    -729 / 1664 * r * Tin ^ 8 * v ^ 2 + 81 / 640 * r * Tin ^ 5 +
      405 / 1664 * Tin ^ 6 * v
  let C5 : K :=
    -6561 / 104 * Xn ^ 2 * r * Tin ^ 8 * u * v ^ 2 +
      19683 / 208 * Xn * Zn * r * Tin ^ 8 * v ^ 2 -
      19683 / 208 * Xn ^ 2 * Tin ^ 8 * v ^ 3 -
      6561 / 52 * Xn * Yn * Tin ^ 8 * u * v ^ 2 +
      19683 / 208 * Yn * Zn * Tin ^ 8 * v ^ 2 +
      729 / 40 * Xn ^ 2 * r * Tin ^ 5 * u -
      2187 / 80 * Xn * Zn * r * Tin ^ 5 +
      2187 / 80 * Xn ^ 2 * Tin ^ 5 * v +
      729 / 20 * Xn * Yn * Tin ^ 5 * u -
      2187 / 80 * Yn * Zn * Tin ^ 5
  let C6 : K :=
    6561 / 104 * Xn * r ^ 2 * Tin ^ 8 * u * v ^ 2 -
      19683 / 208 * Zn * r ^ 2 * Tin ^ 8 * v ^ 2 +
      19683 / 208 * Xn * r * Tin ^ 8 * v ^ 3 +
      6561 / 104 * Yn * r * Tin ^ 8 * u * v ^ 2 +
      19683 / 208 * Yn * Tin ^ 8 * v ^ 3 -
      6561 / 208 * Zn * Tin ^ 8 * u * v ^ 2 -
      729 / 40 * Xn * r ^ 2 * Tin ^ 5 * u +
      2187 / 80 * Zn * r ^ 2 * Tin ^ 5 -
      2187 / 80 * Xn * r * Tin ^ 5 * v -
      729 / 40 * Yn * r * Tin ^ 5 * u -
      2187 / 80 * Yn * Tin ^ 5 * v + 729 / 80 * Zn * Tin ^ 5 * u
  let C7 : K :=
    45 / 13 * Tin ^ 7 * u ^ 4 * v ^ 2 -
      2025 / 26 * Tin ^ 7 * u * v ^ 4 +
      45 / 13 * Tin ^ 6 * u ^ 3 * v ^ 2 -
      2025 / 26 * Tin ^ 6 * v ^ 4 - 45 / 2 * Tin ^ 5 * u ^ 2 * v ^ 2 -
      Tin ^ 4 * u ^ 4 - Tin ^ 3 * u ^ 3 - Tin ^ 2 * u ^ 2 - Tin * u - 1
  have hone : (1 : K) = 0 := by
    linear_combination C1 * h1 + C2 * h2 + C3 * h3 + C4 * h4 +
      C5 * hK + C6 * hphi + C7 * hchart
  exact one_ne_zero hone

/-- At every nonzero projective first-`c5` landing, the common cubic and its
normal have no common field-valued root. -/
theorem GCD369CubeC5NoCommonRoot {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K) (hprojective : u ≠ 0 ∨ v ≠ 0)
    (h1 :
      40 * u ^ 3 - 360 * v ^ 2 + 243 * u * Xn ^ 2 -
          486 * Xn * Zn - 243 * Yn ^ 2 = 0)
    (h2 :
      40 * u ^ 2 * v + 81 * v * Xn ^ 2 + 162 * u * Xn * Yn -
          162 * Yn * Zn = 0)
    (h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (h4 :
      40 * u ^ 3 * v - 80 * v ^ 3 - 243 * u * v * Xn ^ 2 -
          162 * u ^ 2 * Xn * Yn + 324 * v * Xn * Zn +
          162 * v * Yn ^ 2 + 162 * u * Yn * Zn = 0) :
    ∀ r : K, r ^ 3 + u * r + v = 0 →
      Xn * r ^ 2 + Yn * r + Zn = 0 → False := by
  have hsupport := GCD369CubeC5Support Xn Yn Zn u v h1 h2 h3 h4
  have hu : u ≠ 0 := by
    intro hu
    have hv : v ≠ 0 := hprojective.resolve_left (fun h => h hu)
    have hv3 : v ^ 3 = 0 := by
      rw [hu] at hsupport
      linear_combination (-1 / 3) * hsupport
    exact (pow_ne_zero 3 hv) hv3
  intro r hK hphi
  exact GCD369CubeC5NoCommonRootOnUChart
    Xn Yn Zn r u⁻¹ u v h1 h2 h3 h4 hK hphi (by simp [hu])

/-- The first retained `c4` load projects to
`u * (u^3 - 18*v^2) = 0`. -/
theorem GCD369CubeC4Support {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K)
    (h1 :
      32 * u * v - 27 * u * Xn ^ 2 + 54 * Xn * Zn + 27 * Yn ^ 2 = 0)
    (h2 :
      32 * u ^ 3 - 144 * v ^ 2 + 243 * v * Xn ^ 2 +
          486 * u * Xn * Yn - 486 * Yn * Zn = 0)
    (_h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (h4 :
      8 * u ^ 4 - 96 * u * v ^ 2 - 243 * u * v * Xn ^ 2 -
          162 * u ^ 2 * Xn * Yn + 324 * v * Xn * Zn +
          162 * v * Yn ^ 2 + 162 * u * Yn * Zn = 0) :
    u * (u ^ 3 - 18 * v ^ 2) = 0 := by
  linear_combination (-9 / 28 * v) * h1 + (1 / 56 * u) * h2 + (3 / 56) * h4

/-- The full forced terminal coefficient on a first `c4` landing is nonzero
at every nonzero projective common-cubic point. -/
theorem GCD369CubeC4TerminalNonzero {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K) (hprojective : u ≠ 0 ∨ v ≠ 0)
    (h1 : 32 * u * v - 27 * u * Xn ^ 2 + 54 * Xn * Zn + 27 * Yn ^ 2 = 0)
    (h2 :
      32 * u ^ 3 - 144 * v ^ 2 + 243 * v * Xn ^ 2 +
          486 * u * Xn * Yn - 486 * Yn * Zn = 0)
    (h4 :
      8 * u ^ 4 - 96 * u * v ^ 2 - 243 * u * v * Xn ^ 2 -
          162 * u ^ 2 * Xn * Yn + 324 * v * Xn * Zn +
          162 * v * Yn ^ 2 + 162 * u * Yn * Zn = 0) :
    32 * u ^ 3 * v - 64 * v ^ 3 + 27 * u ^ 3 * Xn ^ 2 -
        81 * v ^ 2 * Xn ^ 2 - 162 * u * v * Xn * Yn -
        54 * u ^ 2 * Xn * Zn - 27 * u ^ 2 * Yn ^ 2 +
        162 * v * Yn * Zn ≠ 0 := by
  intro hterminal
  by_cases hu : u = 0
  · have hv : v ≠ 0 := hprojective.resolve_left (fun h => h hu)
    subst u
    have hv3 : v ^ 3 = 0 := by
      linear_combination (-1 / 336 * v) * h2 + (-1 / 112) * hterminal
    exact (pow_ne_zero 3 hv) hv3
  · have hu7 : u ^ 7 = 0 := by
      linear_combination
        (-9 / 154 * u ^ 3 * v + 81 / 154 * v ^ 3) * h1 +
        (1 / 56 * u ^ 4 + 9 / 154 * u * v ^ 2) * h2 +
        (3 / 56 * u ^ 3 - 27 / 308 * v ^ 2) * h4 +
        (81 / 308 * u * v) * hterminal
    exact (pow_ne_zero 7 hu) hu7

/-- The `u=0`, `v!=0` chart certificate for a first-`c4` landing. -/
theorem GCD369CubeC4NoCommonRootOnUZeroChart
    {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn r Tin u v : K)
    (h1 : 32 * u * v - 27 * u * Xn ^ 2 + 54 * Xn * Zn + 27 * Yn ^ 2 = 0)
    (h2 :
      32 * u ^ 3 - 144 * v ^ 2 + 243 * v * Xn ^ 2 +
          486 * u * Xn * Yn - 486 * Yn * Zn = 0)
    (h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (_h4 :
      8 * u ^ 4 - 96 * u * v ^ 2 - 243 * u * v * Xn ^ 2 -
          162 * u ^ 2 * Xn * Yn + 324 * v * Xn * Zn +
          162 * v * Yn ^ 2 + 162 * u * Yn * Zn = 0)
    (hK : r ^ 3 + u * r + v = 0)
    (hphi : Xn * r ^ 2 + Yn * r + Zn = 0)
    (hu : u = 0) (hchart : Tin * v - 1 = 0) :
    False := by
  let C1 : K := 1 / 16 * r * Tin ^ 3 * v
  let C2 : K := 1 / 72 * r ^ 3 * Tin ^ 3 + 1 / 144 * Tin ^ 3 * v
  let C3 : K := -9 / 16 * r ^ 2 * Tin ^ 3
  let C5 : K :=
    -27 / 16 * Xn * Zn * r * Tin ^ 3 - 27 / 16 * Xn ^ 2 * Tin ^ 3 * v +
      81 / 16 * Yn * Zn * Tin ^ 3 + 2 * Tin ^ 3 * v ^ 2
  let C6 : K :=
    27 / 16 * Zn * r ^ 2 * Tin ^ 3 - 27 / 16 * Xn * r * Tin ^ 3 * v -
      27 / 16 * Yn * Tin ^ 3 * v
  let C7 : K :=
    -27 / 4 * Xn * Yn * r ^ 3 * Tin ^ 3 +
      9 / 8 * Xn ^ 2 * r ^ 2 * Tin ^ 3 * u -
      4 / 9 * r ^ 3 * Tin ^ 3 * u ^ 2 -
      9 / 8 * Yn ^ 2 * r ^ 2 * Tin ^ 3 -
      9 / 16 * Xn * Zn * r ^ 2 * Tin ^ 3 +
      27 / 8 * Xn ^ 2 * r * Tin ^ 3 * v -
      81 / 16 * Yn * Zn * r * Tin ^ 3 - 27 / 8 * Xn * Yn * Tin ^ 3 * v -
      2 / 9 * Tin ^ 3 * u ^ 2 * v - 4 * r * Tin ^ 3 * v ^ 2
  let C8 : K := -Tin ^ 2 * v ^ 2 - Tin * v - 1
  have hone : (1 : K) = 0 := by
    linear_combination C1 * h1 + C2 * h2 + C3 * h3 + C5 * hK +
      C6 * hphi + C7 * hu + C8 * hchart
  exact one_ne_zero hone

/-- The localized `u!=0` chart certificate for a first-`c4` landing. -/
theorem GCD369CubeC4NoCommonRootOnUChart
    {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn r Tin u v : K)
    (h1 : 32 * u * v - 27 * u * Xn ^ 2 + 54 * Xn * Zn + 27 * Yn ^ 2 = 0)
    (h2 :
      32 * u ^ 3 - 144 * v ^ 2 + 243 * v * Xn ^ 2 +
          486 * u * Xn * Yn - 486 * Yn * Zn = 0)
    (h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (h4 :
      8 * u ^ 4 - 96 * u * v ^ 2 - 243 * u * v * Xn ^ 2 -
          162 * u ^ 2 * Xn * Yn + 324 * v * Xn * Zn +
          162 * v * Yn ^ 2 + 162 * u * Yn * Zn = 0)
    (hK : r ^ 3 + u * r + v = 0)
    (hphi : Xn * r ^ 2 + Yn * r + Zn = 0)
    (hchart : Tin * u - 1 = 0) :
    False := by
  let C1 : K :=
    108 / 77 * r * Tin ^ 7 * u * v ^ 2 + 81 / 154 * Tin ^ 7 * v ^ 3 +
      9 / 22 * Tin ^ 6 * u ^ 2 * v - 81 / 44 * r * Tin ^ 6 * v ^ 2 -
      9 / 28 * Tin ^ 4 * v
  let C2 : K :=
    -6 / 77 * r * Tin ^ 7 * u ^ 2 * v - 9 / 308 * Tin ^ 7 * u * v ^ 2 +
      3 / 22 * r * Tin ^ 6 * u * v + 9 / 44 * Tin ^ 6 * v ^ 2 +
      1 / 56 * Tin ^ 4 * u
  let C3 : K :=
    729 / 44 * r ^ 2 * Tin ^ 6 * v + 243 / 44 * Tin ^ 6 * u * v
  let C4 : K :=
    -18 / 77 * r * Tin ^ 7 * u * v - 27 / 308 * Tin ^ 7 * v ^ 2 +
      3 / 56 * Tin ^ 4
  let C5 : K :=
    -729 / 22 * Xn ^ 2 * r * Tin ^ 6 * u * v +
      2187 / 44 * Xn * Zn * r * Tin ^ 6 * v -
      729 / 11 * Xn * Yn * Tin ^ 6 * u * v -
      2187 / 44 * Xn ^ 2 * Tin ^ 6 * v ^ 2 +
      2187 / 44 * Yn * Zn * Tin ^ 6 * v
  let C6 : K :=
    729 / 22 * Xn * r ^ 2 * Tin ^ 6 * u * v -
      2187 / 44 * Zn * r ^ 2 * Tin ^ 6 * v +
      729 / 22 * Yn * r * Tin ^ 6 * u * v +
      2187 / 44 * Xn * r * Tin ^ 6 * v ^ 2 -
      729 / 44 * Zn * Tin ^ 6 * u * v +
      2187 / 44 * Yn * Tin ^ 6 * v ^ 2
  let C7 : K :=
    48 / 11 * r * Tin ^ 6 * u ^ 4 * v +
      18 / 11 * Tin ^ 6 * u ^ 3 * v ^ 2 -
      864 / 11 * r * Tin ^ 6 * u * v ^ 3 -
      324 / 11 * Tin ^ 6 * v ^ 4 - 18 * Tin ^ 5 * u ^ 2 * v ^ 2 -
      18 * Tin ^ 4 * u * v ^ 2 - Tin ^ 3 * u ^ 3 - Tin ^ 2 * u ^ 2 -
      Tin * u - 1
  have hone : (1 : K) = 0 := by
    linear_combination C1 * h1 + C2 * h2 + C3 * h3 + C4 * h4 +
      C5 * hK + C6 * hphi + C7 * hchart
  exact one_ne_zero hone

/-- At every projective first-`c4` landing, the common cubic and its normal
have no common field-valued root. -/
theorem GCD369CubeC4NoCommonRoot {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K) (hprojective : u ≠ 0 ∨ v ≠ 0)
    (h1 : 32 * u * v - 27 * u * Xn ^ 2 + 54 * Xn * Zn + 27 * Yn ^ 2 = 0)
    (h2 :
      32 * u ^ 3 - 144 * v ^ 2 + 243 * v * Xn ^ 2 +
          486 * u * Xn * Yn - 486 * Yn * Zn = 0)
    (h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (h4 :
      8 * u ^ 4 - 96 * u * v ^ 2 - 243 * u * v * Xn ^ 2 -
          162 * u ^ 2 * Xn * Yn + 324 * v * Xn * Zn +
          162 * v * Yn ^ 2 + 162 * u * Yn * Zn = 0) :
    ∀ r : K, r ^ 3 + u * r + v = 0 →
      Xn * r ^ 2 + Yn * r + Zn = 0 → False := by
  intro r hK hphi
  by_cases hu : u = 0
  · have hv : v ≠ 0 := hprojective.resolve_left (fun h => h hu)
    exact GCD369CubeC4NoCommonRootOnUZeroChart
      Xn Yn Zn r v⁻¹ u v h1 h2 h3 h4 hK hphi hu (by simp [hv])
  · exact GCD369CubeC4NoCommonRootOnUChart
      Xn Yn Zn r u⁻¹ u v h1 h2 h3 h4 hK hphi (by simp [hu])

/-- The first retained `c2` load projects to `u^3 - 9*v^2 = 0`. -/
theorem GCD369CubeC2Support {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K)
    (h1 :
      -16 * v + 9 * u * Xn ^ 2 - 18 * Xn * Zn - 9 * Yn ^ 2 = 0)
    (h2 :
      8 * u ^ 2 + 27 * v * Xn ^ 2 + 54 * u * Xn * Yn -
          54 * Yn * Zn = 0)
    (_h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (h4 :
      16 * u ^ 3 - 72 * v ^ 2 - 243 * u * v * Xn ^ 2 -
          162 * u ^ 2 * Xn * Yn + 324 * v * Xn * Zn +
          162 * v * Yn ^ 2 + 162 * u * Yn * Zn = 0) :
    u ^ 3 - 9 * v ^ 2 = 0 := by
  linear_combination (9 / 20 * v) * h1 + (3 / 40 * u) * h2 + (1 / 40) * h4

/-- The full forced terminal coefficient on a first `c2` landing is nonzero
at every nonzero projective common-cubic point. -/
theorem GCD369CubeC2TerminalNonzero {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K) (hprojective : u ≠ 0 ∨ v ≠ 0)
    (h1 : -16 * v + 9 * u * Xn ^ 2 - 18 * Xn * Zn - 9 * Yn ^ 2 = 0)
    (h2 :
      8 * u ^ 2 + 27 * v * Xn ^ 2 + 54 * u * Xn * Yn -
          54 * Yn * Zn = 0)
    (h4 :
      16 * u ^ 3 - 72 * v ^ 2 - 243 * u * v * Xn ^ 2 -
          162 * u ^ 2 * Xn * Yn + 324 * v * Xn * Zn +
          162 * v * Yn ^ 2 + 162 * u * Yn * Zn = 0) :
    16 * u ^ 2 * v + 9 * u ^ 3 * Xn ^ 2 - 27 * v ^ 2 * Xn ^ 2 -
        54 * u * v * Xn * Yn - 18 * u ^ 2 * Xn * Zn -
        9 * u ^ 2 * Yn ^ 2 + 54 * v * Yn * Zn ≠ 0 := by
  intro hterminal
  by_cases hu : u = 0
  · have hv : v ≠ 0 := hprojective.resolve_left (fun h => h hu)
    subst u
    have hv2 : v ^ 2 = 0 := by
      linear_combination (-1 / 20 * v) * h1 + (-1 / 360) * h4
    exact (pow_ne_zero 2 hv) hv2
  · have hu5 : u ^ 5 = 0 := by
      linear_combination
        (9 / 40 * u ^ 2 * v) * h1 +
        (3 / 40 * u ^ 3 + 9 / 40 * v ^ 2) * h2 +
        (1 / 40 * u ^ 2) * h4 + (9 / 40 * v) * hterminal
    exact (pow_ne_zero 5 hu) hu5

/-- The localized `u!=0` chart certificate for a first-`c2` landing. -/
theorem GCD369CubeC2NoCommonRootOnUChart
    {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn r Tin u v : K)
    (h1 : -16 * v + 9 * u * Xn ^ 2 - 18 * Xn * Zn - 9 * Yn ^ 2 = 0)
    (h2 :
      8 * u ^ 2 + 27 * v * Xn ^ 2 + 54 * u * Xn * Yn -
          54 * Yn * Zn = 0)
    (h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (h4 :
      16 * u ^ 3 - 72 * v ^ 2 - 243 * u * v * Xn ^ 2 -
          162 * u ^ 2 * Xn * Yn + 324 * v * Xn * Zn +
          162 * v * Yn ^ 2 + 162 * u * Yn * Zn = 0)
    (hK : r ^ 3 + u * r + v = 0)
    (hphi : Xn * r ^ 2 + Yn * r + Zn = 0)
    (hchart : Tin * u - 1 = 0) :
    False := by
  let C1 : K :=
    -27 / 28 * r ^ 2 * Tin ^ 5 * u * v - 27 / 28 * Tin ^ 5 * u ^ 2 * v +
      81 / 280 * r * Tin ^ 5 * v ^ 2 + 27 / 28 * r ^ 2 * Tin ^ 4 * v +
      9 / 14 * Tin ^ 4 * u * v + 9 / 20 * Tin ^ 3 * v
  let C2 : K :=
    -27 / 140 * r * Tin ^ 5 * u * v + 27 / 56 * Tin ^ 5 * v ^ 2 +
      9 / 28 * r * Tin ^ 4 * v + 3 / 40 * Tin ^ 3 * u
  let C3 : K :=
    243 / 56 * r ^ 2 * Tin ^ 5 * v + 243 / 56 * Tin ^ 5 * u * v -
      81 / 28 * Tin ^ 4 * v
  let C4 : K := -9 / 140 * r * Tin ^ 5 * v + 1 / 40 * Tin ^ 3
  let C5 : K :=
    729 / 56 * Xn * Zn * r * Tin ^ 5 * v -
      729 / 56 * Xn ^ 2 * Tin ^ 5 * v ^ 2 -
      243 / 28 * Xn ^ 2 * r * Tin ^ 4 * v +
      729 / 56 * Yn * Zn * Tin ^ 5 * v - 243 / 14 * Xn * Yn * Tin ^ 4 * v
  let C6 : K :=
    -729 / 56 * Zn * r ^ 2 * Tin ^ 5 * v +
      729 / 56 * Xn * r * Tin ^ 5 * v ^ 2 +
      243 / 28 * Xn * r ^ 2 * Tin ^ 4 * v -
      729 / 56 * Zn * Tin ^ 5 * u * v +
      729 / 56 * Yn * Tin ^ 5 * v ^ 2 +
      243 / 28 * Yn * r * Tin ^ 4 * v + 243 / 28 * Zn * Tin ^ 4 * v
  let C7 : K :=
    18 / 7 * r * Tin ^ 4 * u ^ 2 * v - 108 / 7 * r ^ 2 * Tin ^ 4 * v ^ 2 -
      135 / 7 * Tin ^ 4 * u * v ^ 2 - 9 * Tin ^ 3 * v ^ 2 -
      Tin ^ 2 * u ^ 2 - Tin * u - 1
  have hone : (1 : K) = 0 := by
    linear_combination C1 * h1 + C2 * h2 + C3 * h3 + C4 * h4 +
      C5 * hK + C6 * hphi + C7 * hchart
  exact one_ne_zero hone

/-- At every projective first-`c2` landing, the common cubic and its normal
have no common field-valued root. -/
theorem GCD369CubeC2NoCommonRoot {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K) (hprojective : u ≠ 0 ∨ v ≠ 0)
    (h1 : -16 * v + 9 * u * Xn ^ 2 - 18 * Xn * Zn - 9 * Yn ^ 2 = 0)
    (h2 :
      8 * u ^ 2 + 27 * v * Xn ^ 2 + 54 * u * Xn * Yn -
          54 * Yn * Zn = 0)
    (h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (h4 :
      16 * u ^ 3 - 72 * v ^ 2 - 243 * u * v * Xn ^ 2 -
          162 * u ^ 2 * Xn * Yn + 324 * v * Xn * Zn +
          162 * v * Yn ^ 2 + 162 * u * Yn * Zn = 0) :
    ∀ r : K, r ^ 3 + u * r + v = 0 →
      Xn * r ^ 2 + Yn * r + Zn = 0 → False := by
  have hsupport := GCD369CubeC2Support Xn Yn Zn u v h1 h2 h3 h4
  have hu : u ≠ 0 := by
    intro hu
    rw [hu] at hsupport
    have hv2 : v ^ 2 = 0 := by
      linear_combination (-1 / 9) * hsupport
    have hv : v = 0 := by
      by_contra hv
      exact (pow_ne_zero 2 hv) hv2
    exact hprojective.elim (fun h => h hu) (fun h => h hv)
  intro r hK hphi
  exact GCD369CubeC2NoCommonRootOnUChart
    Xn Yn Zn r u⁻¹ u v h1 h2 h3 h4 hK hphi (by simp [hu])

/-- The first retained `c1` load projects to the two coordinate axes
`u*v = 0`. -/
theorem GCD369CubeC1Support {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K)
    (h1 : 8 * u - 9 * u * Xn ^ 2 + 18 * Xn * Zn + 9 * Yn ^ 2 = 0)
    (h2 :
      -8 * v + 9 * v * Xn ^ 2 + 18 * u * Xn * Yn - 18 * Yn * Zn = 0)
    (_h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (h4 :
      8 * u * v + 27 * u * v * Xn ^ 2 + 18 * u ^ 2 * Xn * Yn -
          36 * v * Xn * Zn - 18 * v * Yn ^ 2 - 18 * u * Yn * Zn = 0) :
    u * v = 0 := by
  linear_combination (1 / 16 * v) * h1 + (-1 / 32 * u) * h2 + (1 / 32) * h4

/-- The full forced terminal coefficient on a first `c1` landing is nonzero
at every nonzero projective common-cubic point. -/
theorem GCD369CubeC1TerminalNonzero {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K) (hprojective : u ≠ 0 ∨ v ≠ 0)
    (h1 : 8 * u - 9 * u * Xn ^ 2 + 18 * Xn * Zn + 9 * Yn ^ 2 = 0)
    (h2 :
      -8 * v + 9 * v * Xn ^ 2 + 18 * u * Xn * Yn - 18 * Yn * Zn = 0)
    (h4 :
      8 * u * v + 27 * u * v * Xn ^ 2 + 18 * u ^ 2 * Xn * Yn -
          36 * v * Xn * Zn - 18 * v * Yn ^ 2 - 18 * u * Yn * Zn = 0) :
    8 * u ^ 3 - 72 * v ^ 2 + 27 * u ^ 3 * Xn ^ 2 -
        81 * v ^ 2 * Xn ^ 2 - 162 * u * v * Xn * Yn -
        54 * u ^ 2 * Xn * Zn - 27 * u ^ 2 * Yn ^ 2 +
        162 * v * Yn * Zn ≠ 0 := by
  intro hterminal
  by_cases hu : u = 0
  · have hv : v ≠ 0 := hprojective.resolve_left (fun h => h hu)
    subst u
    have hv2 : v ^ 2 = 0 := by
      linear_combination (-1 / 16 * v) * h2 + (-1 / 144) * hterminal
    exact (pow_ne_zero 2 hv) hv2
  · have hu4 : u ^ 4 = 0 := by
      linear_combination
        (3 / 32 * u ^ 3 + 9 / 32 * v ^ 2) * h1 +
        (9 / 64 * u * v) * h2 + (9 / 64 * v) * h4 +
        (1 / 32 * u) * hterminal
    exact (pow_ne_zero 4 hu) hu4

/-- The `u=0`, `v!=0` chart certificate for a first-`c1` landing. -/
theorem GCD369CubeC1NoCommonRootOnUZeroChart
    {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn r Tin u v : K)
    (h1 : 8 * u - 9 * u * Xn ^ 2 + 18 * Xn * Zn + 9 * Yn ^ 2 = 0)
    (h2 :
      -8 * v + 9 * v * Xn ^ 2 + 18 * u * Xn * Yn - 18 * Yn * Zn = 0)
    (h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (_h4 :
      8 * u * v + 27 * u * v * Xn ^ 2 + 18 * u ^ 2 * Xn * Yn -
          36 * v * Xn * Zn - 18 * v * Yn ^ 2 - 18 * u * Yn * Zn = 0)
    (hK : r ^ 3 + u * r + v = 0)
    (hphi : Xn * r ^ 2 + Yn * r + Zn = 0)
    (hu : u = 0) (hchart : Tin * v - 1 = 0) :
    False := by
  let C1 : K := 1 / 8 * r * Tin ^ 2 * v
  let C2 : K := 1 / 4 * r ^ 3 * Tin ^ 2 + 1 / 8 * Tin ^ 2 * v
  let C3 : K := -3 / 8 * r ^ 2 * Tin ^ 2
  let C5 : K :=
    -9 / 8 * Xn * Zn * r * Tin ^ 2 - 9 / 8 * Xn ^ 2 * Tin ^ 2 * v +
      27 / 8 * Yn * Zn * Tin ^ 2 + 2 * Tin ^ 2 * v
  let C6 : K :=
    9 / 8 * Zn * r ^ 2 * Tin ^ 2 - 9 / 8 * Xn * r * Tin ^ 2 * v -
      9 / 8 * Yn * Tin ^ 2 * v
  let C7 : K :=
    -9 / 2 * Xn * Yn * r ^ 3 * Tin ^ 2 +
      3 / 4 * Xn ^ 2 * r ^ 2 * Tin ^ 2 * u -
      3 / 4 * Yn ^ 2 * r ^ 2 * Tin ^ 2 -
      3 / 8 * Xn * Zn * r ^ 2 * Tin ^ 2 +
      9 / 4 * Xn ^ 2 * r * Tin ^ 2 * v -
      27 / 8 * Yn * Zn * r * Tin ^ 2 - 9 / 4 * Xn * Yn * Tin ^ 2 * v -
      3 * r * Tin ^ 2 * v
  let C8 : K := -Tin * v - 1
  have hone : (1 : K) = 0 := by
    linear_combination C1 * h1 + C2 * h2 + C3 * h3 + C5 * hK +
      C6 * hphi + C7 * hu + C8 * hchart
  exact one_ne_zero hone

/-- The `v=0`, `u!=0` chart certificate for a first-`c1` landing. -/
theorem GCD369CubeC1NoCommonRootOnVZeroChart
    {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn r Tin u v : K)
    (h1 : 8 * u - 9 * u * Xn ^ 2 + 18 * Xn * Zn + 9 * Yn ^ 2 = 0)
    (h2 :
      -8 * v + 9 * v * Xn ^ 2 + 18 * u * Xn * Yn - 18 * Yn * Zn = 0)
    (h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (_h4 :
      8 * u * v + 27 * u * v * Xn ^ 2 + 18 * u ^ 2 * Xn * Yn -
          36 * v * Xn * Zn - 18 * v * Yn ^ 2 - 18 * u * Yn * Zn = 0)
    (hK : r ^ 3 + u * r + v = 0)
    (hphi : Xn * r ^ 2 + Yn * r + Zn = 0)
    (hv : v = 0) (hchart : Tin * u - 1 = 0) :
    False := by
  let C1 : K := 1 / 8 * Tin ^ 3 * u ^ 2
  let C2 : K := -3 / 8 * r ^ 3 * Tin ^ 3
  let C3 : K := 27 / 16 * r ^ 2 * Tin ^ 3 + 9 / 16 * Tin ^ 3 * u
  let C5 : K :=
    27 / 8 * Xn * Yn * r ^ 2 * Tin ^ 3 -
      27 / 8 * Xn ^ 2 * r * Tin ^ 3 * u +
      27 / 8 * Yn ^ 2 * r * Tin ^ 3 + 81 / 16 * Xn * Zn * r * Tin ^ 3 +
      27 / 16 * Yn * Zn * Tin ^ 3
  let C6 : K :=
    -27 / 8 * Yn * r ^ 3 * Tin ^ 3 +
      27 / 8 * Xn * r ^ 2 * Tin ^ 3 * u -
      81 / 16 * Zn * r ^ 2 * Tin ^ 3 - 27 / 16 * Zn * Tin ^ 3 * u
  let C7 : K :=
    27 / 8 * Xn ^ 2 * r ^ 3 * Tin ^ 3 +
      27 / 4 * Xn * Yn * r ^ 2 * Tin ^ 3 +
      27 / 8 * Xn ^ 2 * r * Tin ^ 3 * u -
      27 / 8 * Yn ^ 2 * r * Tin ^ 3 - 81 / 16 * Xn * Zn * r * Tin ^ 3 -
      3 * r ^ 3 * Tin ^ 3 + 27 / 8 * Xn * Yn * Tin ^ 3 * u -
      27 / 16 * Yn * Zn * Tin ^ 3
  let C8 : K := -Tin ^ 2 * u ^ 2 - Tin * u - 1
  have hone : (1 : K) = 0 := by
    linear_combination C1 * h1 + C2 * h2 + C3 * h3 + C5 * hK +
      C6 * hphi + C7 * hv + C8 * hchart
  exact one_ne_zero hone

/-- At every nonzero projective first-`c1` landing, the common cubic and its
normal have no common field-valued root. -/
theorem GCD369CubeC1NoCommonRoot {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K) (hprojective : u ≠ 0 ∨ v ≠ 0)
    (h1 : 8 * u - 9 * u * Xn ^ 2 + 18 * Xn * Zn + 9 * Yn ^ 2 = 0)
    (h2 :
      -8 * v + 9 * v * Xn ^ 2 + 18 * u * Xn * Yn - 18 * Yn * Zn = 0)
    (h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (h4 :
      8 * u * v + 27 * u * v * Xn ^ 2 + 18 * u ^ 2 * Xn * Yn -
          36 * v * Xn * Zn - 18 * v * Yn ^ 2 - 18 * u * Yn * Zn = 0) :
    ∀ r : K, r ^ 3 + u * r + v = 0 →
      Xn * r ^ 2 + Yn * r + Zn = 0 → False := by
  have hsupport := GCD369CubeC1Support Xn Yn Zn u v h1 h2 h3 h4
  intro r hK hphi
  by_cases hu : u = 0
  · have hv : v ≠ 0 := hprojective.resolve_left (fun h => h hu)
    exact GCD369CubeC1NoCommonRootOnUZeroChart
      Xn Yn Zn r v⁻¹ u v h1 h2 h3 h4 hK hphi hu (by simp [hv])
  · have hv : v = 0 := (mul_eq_zero.mp hsupport).resolve_left hu
    exact GCD369CubeC1NoCommonRootOnVZeroChart
      Xn Yn Zn r u⁻¹ u v h1 h2 h3 h4 hK hphi hv (by simp [hu])

/-- With all high constants zero, a first `rho1` load forces `v = 0`. -/
theorem GCD369CubeRhoOneSupport {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K)
    (h1 : 729 * u * Xn ^ 2 - 1458 * Xn * Zn - 729 * Yn ^ 2 + 1944 = 0)
    (h2 : -2187 * v * Xn ^ 2 - 4374 * u * Xn * Yn + 4374 * Yn * Zn = 0)
    (_h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (h4 :
      19683 * u * v * Xn ^ 2 + 13122 * u ^ 2 * Xn * Yn -
          26244 * v * Xn * Zn - 13122 * v * Yn ^ 2 -
          13122 * u * Yn * Zn = 0) :
    v = 0 := by
  linear_combination (1 / 1944 * v) * h1 + (-1 / 11664 * u) * h2 +
    (-1 / 34992) * h4

/-- On a projective first-`rho1` landing, the quadratic terminal coefficient
is nonzero.  The support equation forces `v=0`, after which the first row
identifies it with `1944*u^2`. -/
theorem GCD369CubeRhoOneTerminalNonzero {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K) (hprojective : u ≠ 0 ∨ v ≠ 0)
    (h1 : 729 * u * Xn ^ 2 - 1458 * Xn * Zn - 729 * Yn ^ 2 + 1944 = 0)
    (h2 : -2187 * v * Xn ^ 2 - 4374 * u * Xn * Yn + 4374 * Yn * Zn = 0)
    (h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (h4 :
      19683 * u * v * Xn ^ 2 + 13122 * u ^ 2 * Xn * Yn -
          26244 * v * Xn * Zn - 13122 * v * Yn ^ 2 -
          13122 * u * Yn * Zn = 0) :
    -729 * u ^ 3 * Xn ^ 2 + 2187 * v ^ 2 * Xn ^ 2 +
        4374 * u * v * Xn * Yn + 1458 * u ^ 2 * Xn * Zn +
        729 * u ^ 2 * Yn ^ 2 - 4374 * v * Yn * Zn ≠ 0 := by
  intro hterminal
  have hv : v = 0 := GCD369CubeRhoOneSupport Xn Yn Zn u v h1 h2 h3 h4
  have hu : u ≠ 0 := hprojective.resolve_right (fun h => h hv)
  subst v
  have hu2 : u ^ 2 = 0 := by
    linear_combination (1 / 1944 * u ^ 2) * h1 + (1 / 1944) * hterminal
  exact (pow_ne_zero 2 hu) hu2

/-- The `v=0`, `u!=0` chart certificate for a first-`rho1` landing. -/
theorem GCD369CubeRhoOneNoCommonRootOnVZeroChart
    {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn r Tin u v : K)
    (h1 : 729 * u * Xn ^ 2 - 1458 * Xn * Zn - 729 * Yn ^ 2 + 1944 = 0)
    (h2 : -2187 * v * Xn ^ 2 - 4374 * u * Xn * Yn + 4374 * Yn * Zn = 0)
    (h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (_h4 :
      19683 * u * v * Xn ^ 2 + 13122 * u ^ 2 * Xn * Yn -
          26244 * v * Xn * Zn - 13122 * v * Yn ^ 2 -
          13122 * u * Yn * Zn = 0)
    (hK : r ^ 3 + u * r + v = 0)
    (hphi : Xn * r ^ 2 + Yn * r + Zn = 0)
    (hv : v = 0) (hchart : Tin * u - 1 = 0) :
    False := by
  let C1 : K :=
    -1 / 1296 * r ^ 2 * Tin ^ 2 * u + 1 / 1296 * r ^ 2 * Tin +
      1 / 1944 * Tin * u
  let C2 : K := -1 / 1296 * r ^ 3 * Tin ^ 2 - 1 / 3888 * r * Tin
  let C3 : K := -9 / 16 * r ^ 2 * Tin ^ 2 - 3 / 16 * Tin
  let C5 : K :=
    -27 / 16 * Xn * Yn * r ^ 2 * Tin ^ 2 +
      27 / 16 * Xn ^ 2 * r * Tin ^ 2 * u -
      27 / 16 * Yn ^ 2 * r * Tin ^ 2 - 27 / 16 * Xn * Zn * r * Tin ^ 2 -
      9 / 16 * Xn ^ 2 * r * Tin - 9 / 8 * Xn * Yn * Tin
  let C6 : K :=
    27 / 16 * Yn * r ^ 3 * Tin ^ 2 -
      27 / 16 * Xn * r ^ 2 * Tin ^ 2 * u +
      27 / 16 * Zn * r ^ 2 * Tin ^ 2 + 9 / 16 * Xn * r ^ 2 * Tin +
      9 / 16 * Yn * r * Tin + 9 / 16 * Zn * Tin
  let C7 : K :=
    -27 / 16 * Xn ^ 2 * r ^ 3 * Tin ^ 2 -
      27 / 16 * Xn * Yn * r ^ 2 * Tin ^ 2 -
      27 / 16 * Xn ^ 2 * r * Tin ^ 2 * u +
      27 / 16 * Yn ^ 2 * r * Tin ^ 2 + 27 / 16 * Xn * Zn * r * Tin ^ 2
  let C8 : K := 3 / 2 * r ^ 2 * Tin - 1
  have hone : (1 : K) = 0 := by
    linear_combination C1 * h1 + C2 * h2 + C3 * h3 + C5 * hK +
      C6 * hphi + C7 * hv + C8 * hchart
  exact one_ne_zero hone

/-- At every projective first-`rho1` landing, the common cubic and its normal
have no common field-valued root. -/
theorem GCD369CubeRhoOneNoCommonRoot {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K) (hprojective : u ≠ 0 ∨ v ≠ 0)
    (h1 : 729 * u * Xn ^ 2 - 1458 * Xn * Zn - 729 * Yn ^ 2 + 1944 = 0)
    (h2 : -2187 * v * Xn ^ 2 - 4374 * u * Xn * Yn + 4374 * Yn * Zn = 0)
    (h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (h4 :
      19683 * u * v * Xn ^ 2 + 13122 * u ^ 2 * Xn * Yn -
          26244 * v * Xn * Zn - 13122 * v * Yn ^ 2 -
          13122 * u * Yn * Zn = 0) :
    ∀ r : K, r ^ 3 + u * r + v = 0 →
      Xn * r ^ 2 + Yn * r + Zn = 0 → False := by
  have hv : v = 0 := GCD369CubeRhoOneSupport Xn Yn Zn u v h1 h2 h3 h4
  have hu : u ≠ 0 := hprojective.resolve_right (fun h => h hv)
  intro r hK hphi
  exact GCD369CubeRhoOneNoCommonRootOnVZeroChart
    Xn Yn Zn r u⁻¹ u v h1 h2 h3 h4 hK hphi hv (by simp [hu])

/-- With all high constants zero, a first `rho2` load forces `u = 0`. -/
theorem GCD369CubeRhoTwoSupport {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K)
    (h1 : 729 * u * Xn ^ 2 - 1458 * Xn * Zn - 729 * Yn ^ 2 = 0)
    (h2 :
      -2187 * v * Xn ^ 2 - 4374 * u * Xn * Yn + 4374 * Yn * Zn - 5832 = 0)
    (_h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (h4 :
      19683 * u * v * Xn ^ 2 + 13122 * u ^ 2 * Xn * Yn -
          26244 * v * Xn * Zn - 13122 * v * Yn ^ 2 -
          13122 * u * Yn * Zn = 0) :
    u = 0 := by
  linear_combination (1 / 972 * v) * h1 + (-1 / 5832 * u) * h2 +
    (-1 / 17496) * h4

/-- On a projective first-`rho2` landing, the quadratic terminal coefficient
is nonzero.  The support equation forces `u=0`, after which the second row
identifies it with `-5832*v`. -/
theorem GCD369CubeRhoTwoTerminalNonzero {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K) (hprojective : u ≠ 0 ∨ v ≠ 0)
    (h1 : 729 * u * Xn ^ 2 - 1458 * Xn * Zn - 729 * Yn ^ 2 = 0)
    (h2 :
      -2187 * v * Xn ^ 2 - 4374 * u * Xn * Yn + 4374 * Yn * Zn - 5832 = 0)
    (h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (h4 :
      19683 * u * v * Xn ^ 2 + 13122 * u ^ 2 * Xn * Yn -
          26244 * v * Xn * Zn - 13122 * v * Yn ^ 2 -
          13122 * u * Yn * Zn = 0) :
    -729 * u ^ 3 * Xn ^ 2 + 2187 * v ^ 2 * Xn ^ 2 +
        4374 * u * v * Xn * Yn + 1458 * u ^ 2 * Xn * Zn +
        729 * u ^ 2 * Yn ^ 2 - 4374 * v * Yn * Zn ≠ 0 := by
  intro hterminal
  have hu : u = 0 := GCD369CubeRhoTwoSupport Xn Yn Zn u v h1 h2 h3 h4
  have hv : v ≠ 0 := hprojective.resolve_left (fun h => h hu)
  subst u
  have hv0 : v = 0 := by
    linear_combination (-1 / 5832 * v) * h2 + (-1 / 5832) * hterminal
  exact hv hv0

/-- The `u=0`, `v!=0` chart certificate for a first-`rho2` landing. -/
theorem GCD369CubeRhoTwoNoCommonRootOnUZeroChart
    {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn r Tin u v : K)
    (h1 : 729 * u * Xn ^ 2 - 1458 * Xn * Zn - 729 * Yn ^ 2 = 0)
    (h2 :
      -2187 * v * Xn ^ 2 - 4374 * u * Xn * Yn + 4374 * Yn * Zn - 5832 = 0)
    (h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (_h4 :
      19683 * u * v * Xn ^ 2 + 13122 * u ^ 2 * Xn * Yn -
          26244 * v * Xn * Zn - 13122 * v * Yn ^ 2 -
          13122 * u * Yn * Zn = 0)
    (hK : r ^ 3 + u * r + v = 0)
    (hphi : Xn * r ^ 2 + Yn * r + Zn = 0)
    (hu : u = 0) (hchart : Tin * v - 1 = 0) :
    False := by
  let C1 : K := 1 / 1944 * r * Tin * v
  let C2 : K := 1 / 2916 * r ^ 3 * Tin + 1 / 5832 * Tin * v
  let C3 : K := 1 / 8 * r ^ 2 * Tin
  let C5 : K :=
    3 / 8 * Xn * Zn * r * Tin + 3 / 8 * Xn ^ 2 * Tin * v -
      9 / 8 * Yn * Zn * Tin + 2 * Tin
  let C6 : K :=
    -3 / 8 * Zn * r ^ 2 * Tin + 3 / 8 * Xn * r * Tin * v +
      3 / 8 * Yn * Tin * v
  let C7 : K :=
    3 / 2 * Xn * Yn * r ^ 3 * Tin - 1 / 4 * Xn ^ 2 * r ^ 2 * Tin * u +
      1 / 4 * Yn ^ 2 * r ^ 2 * Tin + 1 / 8 * Xn * Zn * r ^ 2 * Tin -
      3 / 4 * Xn ^ 2 * r * Tin * v + 9 / 8 * Yn * Zn * r * Tin +
      3 / 4 * Xn * Yn * Tin * v - 2 * r * Tin
  let C8 : K := -1
  have hone : (1 : K) = 0 := by
    linear_combination C1 * h1 + C2 * h2 + C3 * h3 + C5 * hK +
      C6 * hphi + C7 * hu + C8 * hchart
  exact one_ne_zero hone

/-- At every projective first-`rho2` landing, the common cubic and its normal
have no common field-valued root. -/
theorem GCD369CubeRhoTwoNoCommonRoot {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K) (hprojective : u ≠ 0 ∨ v ≠ 0)
    (h1 : 729 * u * Xn ^ 2 - 1458 * Xn * Zn - 729 * Yn ^ 2 = 0)
    (h2 :
      -2187 * v * Xn ^ 2 - 4374 * u * Xn * Yn + 4374 * Yn * Zn - 5832 = 0)
    (h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (h4 :
      19683 * u * v * Xn ^ 2 + 13122 * u ^ 2 * Xn * Yn -
          26244 * v * Xn * Zn - 13122 * v * Yn ^ 2 -
          13122 * u * Yn * Zn = 0) :
    ∀ r : K, r ^ 3 + u * r + v = 0 →
      Xn * r ^ 2 + Yn * r + Zn = 0 → False := by
  have hu : u = 0 := GCD369CubeRhoTwoSupport Xn Yn Zn u v h1 h2 h3 h4
  have hv : v ≠ 0 := hprojective.resolve_left (fun h => h hu)
  intro r hK hphi
  exact GCD369CubeRhoTwoNoCommonRootOnUZeroChart
    Xn Yn Zn r v⁻¹ u v h1 h2 h3 h4 hK hphi hu (by simp [hv])

/-- A first `rho4` load has no common quadratic landing.  The displayed
contradiction is the exact unit-ideal certificate from the Kuranishi replay. -/
theorem GCD369CubeRhoFourFirstLoadImpossible {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K)
    (h1 : 729 * u * Xn ^ 2 - 1458 * Xn * Zn - 729 * Yn ^ 2 = 0)
    (h2 : -2187 * v * Xn ^ 2 - 4374 * u * Xn * Yn + 4374 * Yn * Zn = 0)
    (_h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (h4 :
      19683 * u * v * Xn ^ 2 + 13122 * u ^ 2 * Xn * Yn -
          26244 * v * Xn * Zn - 13122 * v * Yn ^ 2 -
          13122 * u * Yn * Zn - 52488 = 0) :
    False := by
  have hone : (1 : K) = 0 := by
    linear_combination (1 / 2916 * v) * h1 + (-1 / 17496 * u) * h2 +
      (-1 / 52488) * h4
  exact one_ne_zero hone

/-- No quadratic normal direction can supply only the terminal row. -/
theorem GCD369CubeTerminalOnlyQuadraticImpossible
    {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v : K)
    (h1 : 729 * u * Xn ^ 2 - 1458 * Xn * Zn - 729 * Yn ^ 2 = 0)
    (h2 : -2187 * v * Xn ^ 2 - 4374 * u * Xn * Yn + 4374 * Yn * Zn = 0)
    (_h3 :
      2 * u ^ 2 * Xn ^ 2 - 6 * v * Xn * Yn - 4 * u * Xn * Zn -
          2 * u * Yn ^ 2 + 3 * Zn ^ 2 = 0)
    (_h4 :
      19683 * u * v * Xn ^ 2 + 13122 * u ^ 2 * Xn * Yn -
          26244 * v * Xn * Zn - 13122 * v * Yn ^ 2 -
          13122 * u * Yn * Zn = 0)
    (h5 :
      -729 * u ^ 3 * Xn ^ 2 + 2187 * v ^ 2 * Xn ^ 2 +
          4374 * u * v * Xn * Yn + 1458 * u ^ 2 * Xn * Zn +
          729 * u ^ 2 * Yn ^ 2 - 4374 * v * Yn * Zn - 17496 = 0) :
    False := by
  have hone : (1 : K) = 0 := by
    linear_combination (-1 / 17496 * u ^ 2) * h1 + (-1 / 17496 * v) * h2 +
      (-1 / 17496) * h5
  exact one_ne_zero hone

private theorem gcd369_outside_nat (q : ℚ) (hq : q < 0 ∨ (0 < q ∧ q < 1))
    (n : ℕ) : q ≠ n := by
  intro h
  rcases hq with hqneg | ⟨hq0, hq1⟩
  · have hn : (0 : ℚ) ≤ n := by positivity
    linarith
  · have hnlt : n < 1 := by
      exact_mod_cast (show (n : ℚ) < 1 by simpa [← h] using hq1)
    have hn : n = 0 := by omega
    subst n
    exact (ne_of_gt hq0) h

/-- Exact finite arithmetic behind every constant-core pole exclusion before
the final `(rho3,rho4)` fibre.  Each displayed rational is a required degree
of a nonzero coefficient (or, in the last row, a required correction degree),
and cannot be a natural-number polynomial degree. -/
theorem GCD369CubeConstantPoleDegreeAudit :
    (∀ n : ℕ, (2 : ℚ) / 14 ≠ n) ∧
    (∀ n : ℕ, (2 : ℚ) / 13 ≠ n) ∧
    (∀ n : ℕ, (2 : ℚ) / 12 ≠ n) ∧
    (∀ n : ℕ, (3 : ℚ) / 12 ≠ n) ∧
    (∀ n : ℕ, (2 : ℚ) / 10 ≠ n) ∧
    (∀ n : ℕ, (3 : ℚ) / 9 ≠ n) ∧
    (∀ n : ℕ, (2 : ℚ) / 7 ≠ n) ∧
    (∀ n : ℕ, (2 : ℚ) / 6 ≠ n) ∧
    (∀ n : ℕ, (3 : ℚ) / 6 ≠ n) ∧
    (∀ n : ℕ, (2 : ℚ) / 4 ≠ n) ∧
    (∀ n : ℕ, (-1 : ℚ) / 2 ≠ n) ∧
    (∀ n : ℕ, (-1 : ℚ) / 6 ≠ n) ∧
    (∀ n : ℕ, (1 : ℚ) / 6 ≠ n) := by
  repeat' apply And.intro
  all_goals
    intro n
    apply gcd369_outside_nat
    norm_num

/-- The original-boundary inequalities are strict for every early forced
load, and become equalities for the first time at weight twelve. -/
theorem GCD369CubeBoundaryWeightAudit :
    (∀ k ∈ ([1, 2, 4, 5, 7, 8, 10, 11] : List ℕ),
      (1 : ℚ) < 12 / k ∧ (3 : ℚ) / 2 < 18 / k) ∧
    (12 : ℚ) / 12 = 1 ∧ (18 : ℚ) / 12 = 3 / 2 := by
  constructor
  · intro k hk
    simp at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · norm_num

/-- The universal first-order boundary cancellation behind every early
common-cubic landing.  If the cubic value and normal value do not vanish
together and the transverse parameter is nonzero, then the reconstructed
first-order source values
`K^2 + h*phi` and `K^3 + (3/2)*h*K*phi` cannot both vanish. -/
theorem GCD369CubeBoundaryFirstOrderSeparation
    {K : Type*} [Field K] [CharZero K]
    (Kval phival h : K) (hh : h ≠ 0)
    (hnocommon : Kval = 0 → phival = 0 → False)
    (hf : Kval ^ 2 + h * phival = 0)
    (hg : Kval ^ 3 + (3 / 2) * h * Kval * phival = 0) :
    False := by
  by_cases hKval : Kval = 0
  · have hphi : phival = 0 := by
      have hhphi : h * phival = 0 := by simpa [hKval] using hf
      exact (mul_eq_zero.mp hhphi).resolve_left hh
    exact hnocommon hKval hphi
  · have hproduct : h * Kval * phival = 0 := by
      linear_combination 2 * hg - 2 * Kval * hf
    have hphi : phival = 0 := by
      rcases mul_eq_zero.mp hproduct with hhk | hphi
      · exact False.elim ((mul_eq_zero.mp hhk).elim hh hKval)
      · exact hphi
    rw [hphi] at hf
    exact (pow_ne_zero 2 hKval) (by simpa using hf)

/-- Source-shaped form of `GCD369CubeBoundaryFirstOrderSeparation` for the
common cubic `z^3+u*z+v` and transverse normal `X*z^2+Y*z+Z`. -/
theorem GCD369CubeCommonCubicBoundaryFirstOrderSeparation
    {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v h : K) (hh : h ≠ 0)
    (hnocommon : ∀ r : K, r ^ 3 + u * r + v = 0 →
      Xn * r ^ 2 + Yn * r + Zn = 0 → False) :
    ∀ r : K,
      (r ^ 3 + u * r + v) ^ 2 + h * (Xn * r ^ 2 + Yn * r + Zn) = 0 →
      (r ^ 3 + u * r + v) ^ 3 +
          (3 / 2) * h * (r ^ 3 + u * r + v) *
            (Xn * r ^ 2 + Yn * r + Zn) = 0 →
      False := by
  intro r hf hg
  apply GCD369CubeBoundaryFirstOrderSeparation
    (r ^ 3 + u * r + v) (Xn * r ^ 2 + Yn * r + Zn) h hh
  · exact hnocommon r
  · exact hf
  · exact hg

/-- In the only possible first-order cancellation regime, where the cubic
has `h`-order `1/2` and `K^2+h*phi` cancels, the leading term of
`K^3+(3/2)h*K*phi` has exact `h`-order `3/2`.  Rational-exponent Hahn series
encode the Puiseux order used in the source boundary argument. -/
theorem GCD369CubeBoundaryCancellationOrder
    {K : Type*} [Field K] [CharZero K]
    (a b h : K) (ha : a ≠ 0)
    (hcancel : a ^ 2 + h * b = 0) :
    let A : HahnSeries ℚ K := HahnSeries.single (1 / 2) a
    let B : HahnSeries ℚ K := HahnSeries.single 0 b
    let H : HahnSeries ℚ K := HahnSeries.single 1 h
    let C32 : HahnSeries ℚ K := HahnSeries.single 0 (3 / 2)
    (A ^ 3 + C32 * H * A * B).order = 3 / 2 := by
  dsimp only
  have hcoefficient : a ^ 3 + (3 / 2) * h * a * b ≠ 0 := by
    have heq : a ^ 3 + (3 / 2) * h * a * b = (-1 / 2) * a ^ 3 := by
      linear_combination (3 / 2 * a) * hcancel
    rw [heq]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 3 ha)
  have hseries :
      (HahnSeries.single (1 / 2 : ℚ) a : HahnSeries ℚ K) ^ 3 +
          HahnSeries.single 0 (3 / 2 : K) * HahnSeries.single 1 h *
            HahnSeries.single (1 / 2) a * HahnSeries.single 0 b =
        HahnSeries.single (3 / 2) (a ^ 3 + (3 / 2) * h * a * b) := by
    rw [HahnSeries.single_pow]
    norm_num
  rw [hseries, HahnSeries.order_single hcoefficient]

/-- Terms of strictly larger Puiseux order cannot cancel the forced
`3/2`-order boundary term. -/
theorem GCD369CubeBoundaryCancellationOrderWithHigherTerms
    {K : Type*} [Field K] [CharZero K]
    (a b h : K) (ha : a ≠ 0)
    (hcancel : a ^ 2 + h * b = 0)
    (E : HahnSeries ℚ K)
    (hE : (↑(3 / 2 : ℚ) : WithTop ℚ) < E.orderTop) :
    let A : HahnSeries ℚ K := HahnSeries.single (1 / 2) a
    let B : HahnSeries ℚ K := HahnSeries.single 0 b
    let H : HahnSeries ℚ K := HahnSeries.single 1 h
    let C32 : HahnSeries ℚ K := HahnSeries.single 0 (3 / 2)
    (A ^ 3 + C32 * H * A * B + E).orderTop =
      (↑(3 / 2 : ℚ) : WithTop ℚ) := by
  dsimp only
  let G : HahnSeries ℚ K :=
    HahnSeries.single (1 / 2) a ^ 3 +
      HahnSeries.single 0 (3 / 2) * HahnSeries.single 1 h *
        HahnSeries.single (1 / 2) a * HahnSeries.single 0 b
  change (G + E).orderTop = (↑(3 / 2 : ℚ) : WithTop ℚ)
  have hGorder : G.order = (3 / 2 : ℚ) := by
    simpa [G] using GCD369CubeBoundaryCancellationOrder a b h ha hcancel
  have hGne : G ≠ 0 := by
    intro hzero
    have : (0 : ℚ) = 3 / 2 := by simpa [hzero] using hGorder
    norm_num at this
  have hGtop : G.orderTop = (↑(3 / 2 : ℚ) : WithTop ℚ) := by
    calc
      G.orderTop = (G.order : WithTop ℚ) :=
        (HahnSeries.order_eq_orderTop_of_ne_zero hGne).symm
      _ = (↑(3 / 2 : ℚ) : WithTop ℚ) :=
        congrArg (fun q : ℚ => (q : WithTop ℚ)) hGorder
  have hGE : G.orderTop < E.orderTop := by
    rw [hGtop]
    exact hE
  calc
    (G + E).orderTop = G.orderTop := HahnSeries.orderTop_add_eq_left hGE
    _ = (↑(3 / 2 : ℚ) : WithTop ℚ) := hGtop

/-- A source value required to vanish to order strictly greater than `3/2`
cannot contain the forced cancellation term plus only higher-order errors. -/
theorem GCD369CubeBoundaryRegularityContradiction
    {K : Type*} [Field K] [CharZero K]
    (a b h : K) (ha : a ≠ 0)
    (hcancel : a ^ 2 + h * b = 0)
    (E : HahnSeries ℚ K)
    (hE : (↑(3 / 2 : ℚ) : WithTop ℚ) < E.orderTop)
    (required : WithTop ℚ)
    (hrequired : (↑(3 / 2 : ℚ) : WithTop ℚ) < required)
    (hregular : required ≤
      let A : HahnSeries ℚ K := HahnSeries.single (1 / 2) a
      let B : HahnSeries ℚ K := HahnSeries.single 0 b
      let H : HahnSeries ℚ K := HahnSeries.single 1 h
      let C32 : HahnSeries ℚ K := HahnSeries.single 0 (3 / 2)
      (A ^ 3 + C32 * H * A * B + E).orderTop) :
    False := by
  have horder :=
    GCD369CubeBoundaryCancellationOrderWithHigherTerms a b h ha hcancel E hE
  rw [horder] at hregular
  exact (not_le_of_gt hrequired) hregular

/-- The cancellation branch contradicts the original `g`-boundary order for
every early forced load.  Weight twelve is deliberately absent: it is the
first equality case and is handled by the reconstructed terminal fibres. -/
theorem GCD369CubeEarlyBoundaryRegularityContradiction
    {K : Type*} [Field K] [CharZero K]
    (k : ℕ) (hk : k ∈ ([1, 2, 4, 5, 7, 8, 10, 11] : List ℕ))
    (a b h : K) (ha : a ≠ 0)
    (hcancel : a ^ 2 + h * b = 0)
    (E : HahnSeries ℚ K)
    (hE : (↑(3 / 2 : ℚ) : WithTop ℚ) < E.orderTop)
    (hregular : (↑((18 : ℚ) / k) : WithTop ℚ) ≤
      let A : HahnSeries ℚ K := HahnSeries.single (1 / 2) a
      let B : HahnSeries ℚ K := HahnSeries.single 0 b
      let H : HahnSeries ℚ K := HahnSeries.single 1 h
      let C32 : HahnSeries ℚ K := HahnSeries.single 0 (3 / 2)
      (A ^ 3 + C32 * H * A * B + E).orderTop) :
    False := by
  have hstrict : (3 / 2 : ℚ) < 18 / k :=
    (GCD369CubeBoundaryWeightAudit.1 k hk).2
  have hstrictTop :
      (↑(3 / 2 : ℚ) : WithTop ℚ) < (↑((18 : ℚ) / k) : WithTop ℚ) :=
    WithTop.coe_lt_coe.mpr hstrict
  exact GCD369CubeBoundaryRegularityContradiction
    a b h ha hcancel E hE (↑((18 : ℚ) / k) : WithTop ℚ) hstrictTop hregular

/-- Local order of the numerator of a reduced rational derivative at a pole
of the denominator.  If `N/B` is pointwise reduced and `B` has multiplicity
`m > 0`, then `N'B-NB'` has multiplicity exactly `m-1`. -/
theorem GCD369ReducedQuotientWronskianLocal {K : Type*} [Field K] [CharZero K]
    (N B : K[X]) (x : K) (_hN : N ≠ 0) (hB : B ≠ 0)
    (hreduced : ∀ y : K, eval y N = 0 → eval y B ≠ 0)
    (hxB : B.IsRoot x) :
    let W := derivative N * B - N * derivative B
    W ≠ 0 ∧ W.rootMultiplicity x = B.rootMultiplicity x - 1 := by
  dsimp only
  let L : K[X] := X - C x
  let m := B.rootMultiplicity x
  let B0 := B /ₘ L ^ m
  let R : K[X] :=
    L * derivative N * B0 - N * (C (m : K) * B0 + L * derivative B0)
  have hm : 0 < m := by
    simpa [m] using (rootMultiplicity_pos hB).mpr hxB
  have hBL : L ^ m * B0 = B := by
    simpa [L, m, B0] using B.pow_mul_divByMonic_rootMultiplicity_eq x
  have hB0eval : eval x B0 ≠ 0 := by
    simpa [L, m, B0] using B.eval_divByMonic_pow_rootMultiplicity_ne_zero x hB
  have hNeval : eval x N ≠ 0 := by
    intro hxN
    exact hreduced x hxN (by simpa [IsRoot] using hxB)
  have hpowDerivative (n : ℕ) :
      L * derivative (L ^ n) = C (n : K) * L ^ n := by
    cases n with
    | zero => simp
    | succ n =>
        simp only [derivative_pow, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
        rw [show derivative L = 1 by simp [L]]
        simp only [mul_one]
        rw [pow_succ]
        ring
  have hBDerivative :
      L * derivative B = L ^ m * (C (m : K) * B0 + L * derivative B0) := by
    rw [← hBL, derivative_mul]
    rw [mul_add, ← mul_assoc, hpowDerivative]
    ring
  have hfactor :
      L * (derivative N * B - N * derivative B) = L ^ m * R := by
    calc
      L * (derivative N * B - N * derivative B) =
          (L * derivative N) * B - N * (L * derivative B) := by ring
      _ = (L * derivative N) * (L ^ m * B0) -
          N * (L ^ m * (C (m : K) * B0 + L * derivative B0)) := by
            rw [hBL, hBDerivative]
      _ = L ^ m * R := by
        dsimp [R]
        ring
  have hmK : (m : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hReval : eval x R ≠ 0 := by
    dsimp [R, L]
    simp only [eval_sub, eval_add, eval_mul, eval_C, eval_X, sub_self,
      zero_mul, add_zero, zero_sub]
    exact neg_ne_zero.mpr (mul_ne_zero hNeval (mul_ne_zero hmK hB0eval))
  have hR : R ≠ 0 := by
    intro hzero
    rw [hzero, eval_zero] at hReval
    exact hReval rfl
  have hL : L ≠ 0 := by simpa [L] using X_sub_C_ne_zero x
  have hright : L ^ m * R ≠ 0 := mul_ne_zero (pow_ne_zero _ hL) hR
  have hleft : L * (derivative N * B - N * derivative B) ≠ 0 := hfactor ▸ hright
  have hW : derivative N * B - N * derivative B ≠ 0 := right_ne_zero_of_mul hleft
  have hrm := congrArg (rootMultiplicity x) hfactor
  rw [rootMultiplicity_mul hleft, rootMultiplicity_mul hright,
    rootMultiplicity_X_sub_C_self, rootMultiplicity_X_sub_C_pow] at hrm
  have hRroot : ¬ R.IsRoot x := by simpa [IsRoot] using hReval
  have hRmult : R.rootMultiplicity x = 0 := rootMultiplicity_eq_zero hRroot
  rw [hRmult, add_zero] at hrm
  exact ⟨hW, by omega⟩

/-- Finite-place classification for a reduced rational primitive of `j/s`.
The polynomial core and the rational denominator have exactly the same finite
support, and their multiplicities differ by one. -/
theorem GCD369CubeRationalPrimitiveFinitePlace {K : Type*} [Field K] [CharZero K]
    (s N B : K[X]) (j : K) (_hs : s ≠ 0) (hN : N ≠ 0) (hB : B ≠ 0)
    (hj : j ≠ 0) (hreduced : ∀ y : K, eval y N = 0 → eval y B ≠ 0)
    (hODE :
      s * (derivative N * B - N * derivative B) = C j * B ^ 2)
    (x : K) (hx : s.IsRoot x ∨ B.IsRoot x) :
    s.IsRoot x ∧ B.IsRoot x ∧
      s.rootMultiplicity x = B.rootMultiplicity x + 1 := by
  have hxB : B.IsRoot x := by
    rcases hx with hxS | hxB
    · have heval := congrArg (eval x) hODE
      simp only [eval_mul, eval_sub, eval_C, eval_pow, IsRoot] at heval hxS ⊢
      rw [hxS, zero_mul] at heval
      have hjB : j * eval x B ^ 2 = 0 := heval.symm
      have hBsq : eval x B ^ 2 = 0 := (mul_eq_zero.mp hjB).resolve_left hj
      exact (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp hBsq
    · exact hxB
  have hxS : s.IsRoot x := by
    by_contra hxS
    have hsmult : s.rootMultiplicity x = 0 := rootMultiplicity_eq_zero hxS
    have hlocal :=
      GCD369ReducedQuotientWronskianLocal N B x hN hB hreduced hxB
    let W := derivative N * B - N * derivative B
    have hB2 : B ^ 2 ≠ 0 := pow_ne_zero _ hB
    have hjC : C j ≠ (0 : K[X]) := C_ne_zero.mpr hj
    have hright : C j * B ^ 2 ≠ 0 := mul_ne_zero hjC hB2
    have hleft : s * W ≠ 0 := by
      change s * (derivative N * B - N * derivative B) ≠ 0
      rw [hODE]
      exact hright
    have hmult := congrArg (rootMultiplicity x) hODE
    rw [rootMultiplicity_mul hleft, rootMultiplicity_mul hright,
      rootMultiplicity_C, pow_two, rootMultiplicity_mul (mul_ne_zero hB hB),
      hsmult] at hmult
    dsimp [W] at hlocal
    rw [hlocal.2] at hmult
    have hm : 0 < B.rootMultiplicity x := (rootMultiplicity_pos hB).mpr hxB
    omega
  have hlocal := GCD369ReducedQuotientWronskianLocal N B x hN hB hreduced hxB
  let W := derivative N * B - N * derivative B
  have hB2 : B ^ 2 ≠ 0 := pow_ne_zero _ hB
  have hjC : C j ≠ (0 : K[X]) := C_ne_zero.mpr hj
  have hright : C j * B ^ 2 ≠ 0 := mul_ne_zero hjC hB2
  have hleft : s * W ≠ 0 := by
    change s * (derivative N * B - N * derivative B) ≠ 0
    rw [hODE]
    exact hright
  have hmult := congrArg (rootMultiplicity x) hODE
  rw [rootMultiplicity_mul hleft, rootMultiplicity_mul hright,
    rootMultiplicity_C, pow_two, rootMultiplicity_mul (mul_ne_zero hB hB)] at hmult
  dsimp [W] at hlocal
  rw [hlocal.2] at hmult
  have hm : 0 < B.rootMultiplicity x := (rootMultiplicity_pos hB).mpr hxB
  refine ⟨hxS, hxB, ?_⟩
  omega

/-- Global finite-support count for a rational primitive of `j/s`: over an
algebraically closed field, `s` and the reduced denominator have identical
root support, and `deg(s)` exceeds the denominator degree by exactly the
number of distinct roots of `s`. -/
theorem GCD369CubeRationalPrimitiveRootCount {K : Type*} [Field K] [CharZero K]
    [IsAlgClosed K] (s N B : K[X]) (j : K)
    (hs : s ≠ 0) (hN : N ≠ 0) (hB : B ≠ 0) (hj : j ≠ 0)
    (hsdegree : 0 < s.natDegree)
    (hreduced : ∀ y : K, eval y N = 0 → eval y B ≠ 0)
    (hODE : s * (derivative N * B - N * derivative B) = C j * B ^ 2) :
    (∀ x : K, s.IsRoot x ↔ B.IsRoot x) ∧
      ∃ r : ℕ, 0 < r ∧ s.natDegree = B.natDegree + r ∧
        (r = 1 → ∃ a : K, ∀ x : K, s.IsRoot x → x = a) := by
  classical
  let S := s.roots.toFinset
  have hsdegree' : s.degree ≠ 0 :=
    ne_of_gt (natDegree_pos_iff_degree_pos.mp hsdegree)
  obtain ⟨x0, hx0⟩ := IsAlgClosed.exists_root s hsdegree'
  have hx0S : x0 ∈ S := by
    simpa [S] using (mem_roots hs).mpr hx0
  have hSnonempty : S.Nonempty := ⟨x0, hx0S⟩
  have hsupport (x : K) : x ∈ S ↔ x ∈ B.roots.toFinset := by
    constructor
    · intro hxS
      have hxsRoot : s.IsRoot x :=
        (mem_roots hs).mp (by simpa [S] using hxS)
      have hfinite := GCD369CubeRationalPrimitiveFinitePlace
        s N B j hs hN hB hj hreduced hODE x (Or.inl hxsRoot)
      simpa using (mem_roots hB).mpr hfinite.2.1
    · intro hxB
      have hxbRoot : B.IsRoot x := (mem_roots hB).mp (by simpa using hxB)
      have hfinite := GCD369CubeRationalPrimitiveFinitePlace
        s N B j hs hN hB hj hreduced hODE x (Or.inr hxbRoot)
      simpa [S] using (mem_roots hs).mpr hfinite.1
  have hpoint (x : K) (hx : x ∈ S) :
      s.rootMultiplicity x = B.rootMultiplicity x + 1 := by
    have hxsRoot : s.IsRoot x := (mem_roots hs).mp (by simpa [S] using hx)
    exact (GCD369CubeRationalPrimitiveFinitePlace
      s N B j hs hN hB hj hreduced hODE x (Or.inl hxsRoot)).2.2
  have hsumS : ∑ x ∈ S, s.rootMultiplicity x = s.natDegree := by
    calc
      ∑ x ∈ S, s.rootMultiplicity x = ∑ x ∈ S, s.roots.count x := by
        apply Finset.sum_congr rfl
        intro x _
        exact (count_roots s).symm
      _ = s.roots.card := by
        apply Multiset.sum_count_eq_card
        intro x hx
        simpa [S] using hx
      _ = s.natDegree := (IsAlgClosed.splits s).natDegree_eq_card_roots.symm
  have hsumB : ∑ x ∈ S, B.rootMultiplicity x = B.natDegree := by
    calc
      ∑ x ∈ S, B.rootMultiplicity x = ∑ x ∈ S, B.roots.count x := by
        apply Finset.sum_congr rfl
        intro x _
        exact (count_roots B).symm
      _ = B.roots.card := by
        apply Multiset.sum_count_eq_card
        intro x hx
        exact (hsupport x).mpr (by simpa using hx)
      _ = B.natDegree := (IsAlgClosed.splits B).natDegree_eq_card_roots.symm
  have hsum := Finset.sum_congr rfl hpoint
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  rw [hsumS, hsumB] at hsum
  refine ⟨?_, ⟨S.card, hSnonempty.card_pos, hsum, ?_⟩⟩
  intro x
  constructor
  · intro hxs
    have hxS : x ∈ S := by simpa [S] using (mem_roots hs).mpr hxs
    exact (mem_roots hB).mp (by simpa using (hsupport x).mp hxS)
  · intro hxb
    have hxB : x ∈ B.roots.toFinset := by simpa using (mem_roots hB).mpr hxb
    exact (mem_roots hs).mp (by simpa [S] using (hsupport x).mpr hxB)
  · intro hcard
    obtain ⟨a, hS⟩ := Finset.card_eq_one.mp hcard
    refine ⟨a, ?_⟩
    intro x hxroot
    have hxS : x ∈ S := by simpa [S] using (mem_roots hs).mpr hxroot
    rw [hS] at hxS
    simpa using hxS

/-- Degree at infinity of the numerator of a reduced rational derivative once
the additive constant has been chosen so that the numerator degree is smaller
than the denominator degree. -/
theorem GCD369ReducedQuotientWronskianDegree {K : Type*} [Field K] [CharZero K]
    (N B : K[X]) (hN : N ≠ 0) (hB : B ≠ 0)
    (hdegree : N.natDegree < B.natDegree) :
    (derivative N * B - N * derivative B).natDegree =
      N.natDegree + B.natDegree - 1 := by
  have hBdegree : 0 < B.natDegree := lt_of_le_of_lt (Nat.zero_le _) hdegree
  by_cases hNdegree : N.natDegree = 0
  · have hNderivative : derivative N = 0 := derivative_eq_zero.mpr hNdegree
    have hBderivative : derivative B ≠ 0 := by
      intro hzero
      have := derivative_eq_zero.mp hzero
      omega
    rw [hNderivative, zero_mul, zero_sub, natDegree_neg,
      natDegree_mul hN hBderivative, natDegree_derivative]
    omega
  · have hNdegreePos : 0 < N.natDegree := Nat.pos_of_ne_zero hNdegree
    let n := N.natDegree + B.natDegree - 1
    let W := derivative N * B - N * derivative B
    have hNderivativeDegree : (derivative N).natDegree = N.natDegree - 1 :=
      natDegree_derivative N
    have hBderivativeDegree : (derivative B).natDegree = B.natDegree - 1 :=
      natDegree_derivative B
    have hfirstCoeff :
        (derivative N * B).coeff n =
          N.leadingCoeff * (N.natDegree : K) * B.leadingCoeff := by
      calc
        (derivative N * B).coeff n =
            (derivative N * B).coeff ((derivative N).natDegree + B.natDegree) := by
              congr 1
              dsimp [n]
              omega
        _ = (derivative N).leadingCoeff * B.leadingCoeff :=
          coeff_mul_degree_add_degree _ _
        _ = N.leadingCoeff * (N.natDegree : K) * B.leadingCoeff := by
          rw [leadingCoeff_derivative]
    have hsecondCoeff :
        (N * derivative B).coeff n =
          N.leadingCoeff * B.leadingCoeff * (B.natDegree : K) := by
      calc
        (N * derivative B).coeff n =
            (N * derivative B).coeff (N.natDegree + (derivative B).natDegree) := by
              congr 1
              dsimp [n]
              omega
        _ = N.leadingCoeff * (derivative B).leadingCoeff :=
          coeff_mul_degree_add_degree _ _
        _ = N.leadingCoeff * B.leadingCoeff * (B.natDegree : K) := by
          rw [leadingCoeff_derivative]
          ring
    have hcoefficient : W.coeff n ≠ 0 := by
      dsimp [W]
      rw [coeff_sub, hfirstCoeff, hsecondCoeff]
      have hNleading : N.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hN
      have hBleading : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hB
      have hdegrees : (N.natDegree : K) ≠ (B.natDegree : K) := by
        exact_mod_cast (ne_of_lt hdegree)
      have hproduct :
          N.leadingCoeff * B.leadingCoeff *
              ((N.natDegree : K) - (B.natDegree : K)) ≠ 0 :=
        mul_ne_zero (mul_ne_zero hNleading hBleading) (sub_ne_zero.mpr hdegrees)
      have hrearrange :
          N.leadingCoeff * (N.natDegree : K) * B.leadingCoeff -
              N.leadingCoeff * B.leadingCoeff * (B.natDegree : K) =
            N.leadingCoeff * B.leadingCoeff *
              ((N.natDegree : K) - (B.natDegree : K)) := by
        ring
      rw [hrearrange]
      exact hproduct
    have hdegreeUpper : W.natDegree ≤ n := by
      dsimp [W]
      refine (natDegree_sub_le _ _).trans ?_
      rw [max_le_iff]
      constructor
      · refine natDegree_mul_le.trans ?_
        rw [hNderivativeDegree]
        dsimp [n]
        omega
      · refine natDegree_mul_le.trans ?_
        rw [hBderivativeDegree]
        dsimp [n]
        omega
    exact natDegree_eq_of_le_of_coeff_ne_zero hdegreeUpper hcoefficient

/-- Exact finite-pole reduction for the cube-core terminal row.  After
subtracting the value at infinity, so the reduced numerator has smaller
degree than its denominator, rational exactness of `j/s` forces `s` to be a
single-root power of exponent at least two; the denominator has exponent one
less. -/
theorem GCD369CubeRationalPrimitiveOneRoot {K : Type*} [Field K] [CharZero K]
    [IsAlgClosed K] (s N B : K[X]) (j : K)
    (hs : s ≠ 0) (hN : N ≠ 0) (hB : B ≠ 0) (hj : j ≠ 0)
    (hsdegree : 0 < s.natDegree) (hdegree : N.natDegree < B.natDegree)
    (hreduced : ∀ y : K, eval y N = 0 → eval y B ≠ 0)
    (hODE : s * (derivative N * B - N * derivative B) = C j * B ^ 2) :
    ∃ a : K, ∃ m : ℕ, 2 ≤ m ∧
      s = C s.leadingCoeff * (X - C a) ^ m ∧
      B = C B.leadingCoeff * (X - C a) ^ (m - 1) := by
  classical
  obtain ⟨hsupport, r, hr, hsdegreeEq, hunique⟩ :=
    GCD369CubeRationalPrimitiveRootCount s N B j hs hN hB hj hsdegree
      hreduced hODE
  let W := derivative N * B - N * derivative B
  have hB2 : B ^ 2 ≠ 0 := pow_ne_zero _ hB
  have hjC : C j ≠ (0 : K[X]) := C_ne_zero.mpr hj
  have hright : C j * B ^ 2 ≠ 0 := mul_ne_zero hjC hB2
  have hleft : s * W ≠ 0 := by
    change s * (derivative N * B - N * derivative B) ≠ 0
    rw [hODE]
    exact hright
  have hW : W ≠ 0 := right_ne_zero_of_mul hleft
  have hWdegree : W.natDegree = N.natDegree + B.natDegree - 1 := by
    simpa [W] using GCD369ReducedQuotientWronskianDegree N B hN hB hdegree
  have hdegreeODE := congrArg natDegree hODE
  rw [natDegree_mul hs hW, natDegree_mul hjC hB2, natDegree_C,
    natDegree_pow, hWdegree] at hdegreeODE
  simp only [zero_add] at hdegreeODE
  have hrOne : r = 1 := by omega
  have hNconstant : N.natDegree = 0 := by omega
  obtain ⟨a, ha⟩ := hunique hrOne
  have hrootsS : s.roots = Multiset.replicate s.roots.card a := by
    apply Multiset.eq_replicate_of_mem
    intro x hx
    exact ha x ((mem_roots hs).mp hx)
  have hrootsB : B.roots = Multiset.replicate B.roots.card a := by
    apply Multiset.eq_replicate_of_mem
    intro x hx
    have hxB : B.IsRoot x := (mem_roots hB).mp hx
    exact ha x ((hsupport x).mpr hxB)
  have hsform : s = C s.leadingCoeff * (X - C a) ^ s.natDegree := by
    calc
      s = C s.leadingCoeff * (s.roots.map fun x => X - C x).prod :=
        (IsAlgClosed.splits s).eq_prod_roots
      _ = C s.leadingCoeff * (X - C a) ^ s.natDegree := by
        rw [hrootsS]
        simp only [Multiset.map_replicate, Multiset.prod_replicate]
        rw [(IsAlgClosed.splits s).natDegree_eq_card_roots]
  have hBform : B = C B.leadingCoeff * (X - C a) ^ B.natDegree := by
    calc
      B = C B.leadingCoeff * (B.roots.map fun x => X - C x).prod :=
        (IsAlgClosed.splits B).eq_prod_roots
      _ = C B.leadingCoeff * (X - C a) ^ B.natDegree := by
        rw [hrootsB]
        simp only [Multiset.map_replicate, Multiset.prod_replicate]
        rw [(IsAlgClosed.splits B).natDegree_eq_card_roots]
  have hm : 2 ≤ s.natDegree := by omega
  refine ⟨a, s.natDegree, hm, hsform, ?_⟩
  calc
    B = C B.leadingCoeff * (X - C a) ^ B.natDegree := hBform
    _ = C B.leadingCoeff * (X - C a) ^ (s.natDegree - 1) := by
      congr 2
      omega

/-- Constant-core half of the same terminal reduction: a reduced rational
primitive with nonzero constant derivative has constant denominator and
affine numerator. -/
theorem GCD369CubeRationalPrimitiveConstantCore {K : Type*} [Field K] [CharZero K]
    [IsAlgClosed K] (s N B : K[X]) (j : K)
    (hs : s ≠ 0) (hN : N ≠ 0) (hB : B ≠ 0) (hj : j ≠ 0)
    (hsdegree : s.natDegree = 0)
    (hreduced : ∀ y : K, eval y N = 0 → eval y B ≠ 0)
    (hODE : s * (derivative N * B - N * derivative B) = C j * B ^ 2) :
    B.natDegree = 0 ∧ N.natDegree = 1 := by
  have hBdegree : B.natDegree = 0 := by
    by_contra hBdegree
    have hBpos : 0 < B.natDegree := Nat.pos_of_ne_zero hBdegree
    have hBdegree' : B.degree ≠ 0 :=
      ne_of_gt (natDegree_pos_iff_degree_pos.mp hBpos)
    obtain ⟨x, hxB⟩ := IsAlgClosed.exists_root B hBdegree'
    have hxS := (GCD369CubeRationalPrimitiveFinitePlace
      s N B j hs hN hB hj hreduced hODE x (Or.inr hxB)).1
    have hspos : 0 < s.natDegree :=
      natDegree_pos_iff_degree_pos.mpr (degree_pos_of_root hs hxS)
    omega
  have hBderivative : derivative B = 0 := derivative_eq_zero.mpr hBdegree
  let W := derivative N * B - N * derivative B
  have hB2 : B ^ 2 ≠ 0 := pow_ne_zero _ hB
  have hjC : C j ≠ (0 : K[X]) := C_ne_zero.mpr hj
  have hright : C j * B ^ 2 ≠ 0 := mul_ne_zero hjC hB2
  have hleft : s * W ≠ 0 := by
    change s * (derivative N * B - N * derivative B) ≠ 0
    rw [hODE]
    exact hright
  have hW : W ≠ 0 := right_ne_zero_of_mul hleft
  have hWform : W = derivative N * B := by
    dsimp [W]
    rw [hBderivative]
    simp
  have hNderivative : derivative N ≠ 0 := by
    intro hzero
    apply hW
    rw [hWform, hzero, zero_mul]
  have hdegreeODE := congrArg natDegree hODE
  rw [natDegree_mul hs hW, natDegree_mul hjC hB2, natDegree_C,
    natDegree_pow, hsdegree, hBdegree, hWform,
    natDegree_mul hNderivative hB] at hdegreeODE
  simp only [zero_add, add_zero, mul_zero] at hdegreeODE
  have hNderivativeDegree : (derivative N).natDegree = 0 := by omega
  rw [natDegree_derivative] at hNderivativeDegree
  have hNdegreePos : 0 < N.natDegree := by
    by_contra hzero
    have : N.natDegree = 0 := Nat.eq_zero_of_not_pos hzero
    exact hNderivative (derivative_eq_zero.mpr this)
  refine ⟨hBdegree, ?_⟩
  omega

/-- A rational primitive of `j/s` with nonconstant polynomial `s` cannot
grow at infinity: in every reduced presentation its numerator degree is at
most its denominator degree. -/
theorem GCD369CubeRationalPrimitiveNumeratorDegreeLe {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K] (s N B : K[X]) (j : K)
    (hs : s ≠ 0) (hN : N ≠ 0) (hB : B ≠ 0) (hj : j ≠ 0)
    (hsdegree : 0 < s.natDegree)
    (hreduced : ∀ y : K, eval y N = 0 → eval y B ≠ 0)
    (hODE : s * (derivative N * B - N * derivative B) = C j * B ^ 2) :
    N.natDegree ≤ B.natDegree := by
  have hB2 : B ^ 2 ≠ 0 := pow_ne_zero _ hB
  have hjC : C j ≠ (0 : K[X]) := C_ne_zero.mpr hj
  have hright : C j * B ^ 2 ≠ 0 := mul_ne_zero hjC hB2
  let W := derivative N * B - N * derivative B
  have hleft : s * W ≠ 0 := by
    change s * (derivative N * B - N * derivative B) ≠ 0
    rw [hODE]
    exact hright
  have hW : W ≠ 0 := right_ne_zero_of_mul hleft
  obtain ⟨_, r, hr, hsdegreeEq, _⟩ :=
    GCD369CubeRationalPrimitiveRootCount s N B j hs hN hB hj hsdegree
      hreduced hODE
  by_contra hle
  have hBN : B.natDegree < N.natDegree := Nat.lt_of_not_ge hle
  have hswap := GCD369ReducedQuotientWronskianDegree B N hB hN hBN
  have hWdegree : W.natDegree = B.natDegree + N.natDegree - 1 := by
    calc
      W.natDegree = (-(derivative B * N - B * derivative N)).natDegree := by
        congr 1
        dsimp [W]
        ring
      _ = (derivative B * N - B * derivative N).natDegree := natDegree_neg _
      _ = B.natDegree + N.natDegree - 1 := hswap
  have hdegreeODE := congrArg natDegree hODE
  rw [natDegree_mul hs hW, natDegree_mul hjC hB2, natDegree_C,
    natDegree_pow, hWdegree] at hdegreeODE
  simp only [zero_add] at hdegreeODE
  omega

/-- Source-form finite-pole dichotomy for a nonconstant polynomial cube root.
For an arbitrary reduced rational presentation, the proof first rules out
growth at infinity, subtracts the unique leading constant when necessary,
and then invokes the normalized one-root theorem. -/
theorem GCD369CubeRationalPrimitiveNonconstantCore {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K] (s N B : K[X]) (j : K)
    (hs : s ≠ 0) (hN : N ≠ 0) (hB : B ≠ 0) (hj : j ≠ 0)
    (hsdegree : 0 < s.natDegree)
    (hreduced : ∀ y : K, eval y N = 0 → eval y B ≠ 0)
    (hODE : s * (derivative N * B - N * derivative B) = C j * B ^ 2) :
    ∃ a : K, ∃ m : ℕ, 2 ≤ m ∧
      s = C s.leadingCoeff * (X - C a) ^ m ∧
      B = C B.leadingCoeff * (X - C a) ^ (m - 1) := by
  have hB2 : B ^ 2 ≠ 0 := pow_ne_zero _ hB
  have hjC : C j ≠ (0 : K[X]) := C_ne_zero.mpr hj
  have hright : C j * B ^ 2 ≠ 0 := mul_ne_zero hjC hB2
  let W := derivative N * B - N * derivative B
  have hleft : s * W ≠ 0 := by
    change s * (derivative N * B - N * derivative B) ≠ 0
    rw [hODE]
    exact hright
  have hW : W ≠ 0 := right_ne_zero_of_mul hleft
  obtain ⟨_, r, hr, hsdegreeEq, _⟩ :=
    GCD369CubeRationalPrimitiveRootCount s N B j hs hN hB hj hsdegree
      hreduced hODE
  have hNle : N.natDegree ≤ B.natDegree := by
    by_contra hle
    have hBN : B.natDegree < N.natDegree := Nat.lt_of_not_ge hle
    have hswap := GCD369ReducedQuotientWronskianDegree B N hB hN hBN
    have hWdegree : W.natDegree = B.natDegree + N.natDegree - 1 := by
      calc
        W.natDegree =
            (-(derivative B * N - B * derivative N)).natDegree := by
              congr 1
              dsimp [W]
              ring
        _ = (derivative B * N - B * derivative N).natDegree := natDegree_neg _
        _ = B.natDegree + N.natDegree - 1 := hswap
    have hdegreeODE := congrArg natDegree hODE
    rw [natDegree_mul hs hW, natDegree_mul hjC hB2, natDegree_C,
      natDegree_pow, hWdegree] at hdegreeODE
    simp only [zero_add] at hdegreeODE
    omega
  have hBdegree : 0 < B.natDegree := by
    by_contra hpos
    have hBzero : B.natDegree = 0 := Nat.eq_zero_of_not_pos hpos
    have hNzero : N.natDegree = 0 := by omega
    have hNderivative : derivative N = 0 := derivative_eq_zero.mpr hNzero
    have hBderivative : derivative B = 0 := derivative_eq_zero.mpr hBzero
    apply hW
    dsimp [W]
    rw [hNderivative, hBderivative]
    simp
  by_cases hlt : N.natDegree < B.natDegree
  · obtain ⟨a, m, hm, hsform, hBform⟩ :=
      GCD369CubeRationalPrimitiveOneRoot s N B j hs hN hB hj hsdegree hlt
        hreduced hODE
    exact ⟨a, m, hm, hsform, hBform⟩
  · have heq : N.natDegree = B.natDegree := Nat.le_antisymm hNle (Nat.le_of_not_gt hlt)
    let c : K := N.leadingCoeff / B.leadingCoeff
    let A : K[X] := N - C c * B
    have hNleading : N.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hN
    have hBleading : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hB
    have hc : c ≠ 0 := div_ne_zero hNleading hBleading
    have hCB : C c * B ≠ (0 : K[X]) := mul_ne_zero (C_ne_zero.mpr hc) hB
    have hdegrees : N.degree = (C c * B).degree := by
      rw [degree_eq_natDegree hN, degree_C_mul hc, degree_eq_natDegree hB, heq]
    have hleading : N.leadingCoeff = (C c * B).leadingCoeff := by
      rw [leadingCoeff_mul, leadingCoeff_C]
      dsimp [c]
      field_simp
    have hA : A ≠ 0 := by
      intro hAzero
      have hNform : N = C c * B := sub_eq_zero.mp (by simpa [A] using hAzero)
      apply hW
      dsimp [W]
      rw [hNform]
      simp only [derivative_mul, derivative_C, zero_mul, zero_add]
      ring
    have hAdegree : A.natDegree < B.natDegree := by
      have hdegA : A.degree < N.degree := by
        simpa [A] using degree_sub_lt_left hdegrees hN hleading
      have hdegAB : A.degree < B.degree := hdegA.trans_eq (by
        rw [degree_eq_natDegree hN, degree_eq_natDegree hB, heq])
      exact natDegree_lt_natDegree hA hdegAB
    have hAreduced : ∀ y : K, eval y A = 0 → eval y B ≠ 0 := by
      intro y hAy hBy
      apply hreduced y
      dsimp [A] at hAy
      simp only [eval_sub, eval_mul, eval_C] at hAy
      rw [hBy, mul_zero, sub_zero] at hAy
      exact hAy
      exact hBy
    have hWsame :
        derivative A * B - A * derivative B =
          derivative N * B - N * derivative B := by
      dsimp [A]
      simp only [derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add]
      ring
    have hAODE : s * (derivative A * B - A * derivative B) = C j * B ^ 2 := by
      rw [hWsame]
      exact hODE
    obtain ⟨a, m, hm, hsform, hBform⟩ :=
      GCD369CubeRationalPrimitiveOneRoot s A B j hs hA hB hj hsdegree hAdegree
        hAreduced hAODE
    exact ⟨a, m, hm, hsform, hBform⟩

/-- Polynomial Fermat--Catalan `(2,3,6)` closes the homogeneous model of the
smooth mixed cube-core elliptic fibre.  Thus every reduced homogeneous
rational parametrization of `72 V² = 3 A³ + 512 μ` is constant when
`μ ≠ 0`. -/
theorem GCD369CubeMixedEllipticConstancy {K : Type*} [Field K] [CharZero K]
    (mu : K) (hmu : mu ≠ 0) (M N D : K[X])
    (hM : M ≠ 0) (hN : N ≠ 0) (hD : D ≠ 0) (hMN : IsCoprime M N)
    (hcurve :
      C (72 : K) * M ^ 2 + C (-3 : K) * N ^ 3 + C (-512 * mu) * D ^ 6 = 0) :
    M.natDegree = 0 ∧ N.natDegree = 0 ∧ D.natDegree = 0 := by
  have h72 : (72 : K) ≠ 0 := by norm_num
  have hneg3 : (-3 : K) ≠ 0 := by norm_num
  have hnegmu : (-512 * mu : K) ≠ 0 := mul_ne_zero (by norm_num) hmu
  have heq :
      C (72 : K) * M ^ 2 + C (-3 : K) * N ^ 3 + C (-512 * mu) * D ^ 6 = 0 := by
    exact hcurve
  exact Polynomial.flt_catalan
    (by norm_num : 2 ≠ 0) (by norm_num : 3 ≠ 0) (by norm_num : 6 ≠ 0)
    (by norm_num : 3 * 6 + 6 * 2 + 2 * 3 ≤ 2 * 3 * 6)
    (by norm_num : (2 : K) ≠ 0) (by norm_num : (3 : K) ≠ 0)
    (by norm_num : (6 : K) ≠ 0) hM hN hD hMN h72 hneg3 hnegmu heq

/-- The unmixed elliptic sheet has the same `(2,3,6)` obstruction in its
homogeneous model `Y² = 3X³ + 4096 μ`. -/
theorem GCD369CubeUnmixedEllipticConstancy {K : Type*} [Field K] [CharZero K]
    (mu : K) (hmu : mu ≠ 0) (M N D : K[X])
    (hM : M ≠ 0) (hN : N ≠ 0) (hD : D ≠ 0) (hMN : IsCoprime M N)
    (hcurve :
      C (1 : K) * M ^ 2 + C (-3 : K) * N ^ 3 + C (-4096 * mu) * D ^ 6 = 0) :
    M.natDegree = 0 ∧ N.natDegree = 0 ∧ D.natDegree = 0 := by
  have h1 : (1 : K) ≠ 0 := one_ne_zero
  have hneg3 : (-3 : K) ≠ 0 := by norm_num
  have hnegmu : (-4096 * mu : K) ≠ 0 := mul_ne_zero (by norm_num) hmu
  have heq :
      C (1 : K) * M ^ 2 + C (-3 : K) * N ^ 3 + C (-4096 * mu) * D ^ 6 = 0 := by
    exact hcurve
  exact Polynomial.flt_catalan
    (by norm_num : 2 ≠ 0) (by norm_num : 3 ≠ 0) (by norm_num : 6 ≠ 0)
    (by norm_num : 3 * 6 + 6 * 2 + 2 * 3 ≤ 2 * 3 * 6)
    (by norm_num : (2 : K) ≠ 0) (by norm_num : (3 : K) ≠ 0)
    (by norm_num : (6 : K) ≠ 0) hM hN hD hMN h1 hneg3 hnegmu heq

/-- The cusp normalization from the mixed `(rho3,rho4)` fibre gives exactly
the two-sided Laurent expression in the trajectory report. -/
theorem GCD369CubeMixedCuspIdentity {K : Type*} [Field K] [CharZero K]
    (lambda nu : K) (hlambda : lambda ≠ 0) :
    let A := 24 * lambda ^ 2
    let V := 24 * lambda ^ 3
    72 * V ^ 2 - 3 * A ^ 3 = 0 ∧
      A ^ 2 * V / 1024 - 256 * nu ^ 2 / (27 * A ^ 3) =
        27 * lambda ^ 7 / 2 - nu ^ 2 / (1458 * lambda ^ 6) := by
  dsimp
  constructor
  · ring
  · field_simp
    ring

/-- After clearing the cusp denominator, the numerator has a nonzero value
at zero and degree thirteen.  These certify the distinct zero and infinity
pole places when `nu != 0`. -/
theorem GCD369CubeMixedCuspPoleData {K : Type*} [Field K] [CharZero K]
    (nu : K) (hnu : nu ≠ 0) :
    let N : K[X] := C 19683 * X ^ 13 - C (nu ^ 2)
    N.eval 0 ≠ 0 ∧ N.natDegree = 13 := by
  dsimp
  constructor
  · simp [hnu]
  · rw [natDegree_sub_eq_left_of_natDegree_lt]
    · simp
    · simp

/-- The numerator and denominator obtained by substituting a reduced rational
`lambda = LN/LB` into the mixed cusp function remain pointwise reduced. -/
theorem GCD369CubeMixedCuspReducedPresentation {K : Type*}
    [Field K] [CharZero K] (nu : K) (hnu : nu ≠ 0)
    (LN LB : K[X]) (hLN : LN ≠ 0) (hLB : LB ≠ 0)
    (hlambdaReduced : ∀ x : K, eval x LN = 0 → eval x LB ≠ 0) :
    let P := C 19683 * LN ^ 13 - C (nu ^ 2) * LB ^ 13
    let Q := C 1458 * LN ^ 6 * LB ^ 7
    Q ≠ 0 ∧ (∀ x : K, eval x P = 0 → eval x Q ≠ 0) ∧
      Q.natDegree = 6 * LN.natDegree + 7 * LB.natDegree := by
  dsimp only
  have hQ : C 1458 * LN ^ 6 * LB ^ 7 ≠ (0 : K[X]) :=
    mul_ne_zero
      (mul_ne_zero (C_ne_zero.mpr (by norm_num)) (pow_ne_zero _ hLN))
      (pow_ne_zero _ hLB)
  refine ⟨hQ, ?_, ?_⟩
  · intro x hxP hxQ
    simp only [eval_mul, eval_C, eval_pow] at hxQ
    rcases mul_eq_zero.mp hxQ with hfirst | hxLBpow
    · have hxLNpow : eval x LN ^ 6 = 0 :=
        (mul_eq_zero.mp hfirst).resolve_left (by norm_num)
      have hxLN : eval x LN = 0 :=
        (pow_eq_zero_iff (by norm_num : 6 ≠ 0)).mp hxLNpow
      have hxLB : eval x LB ≠ 0 := hlambdaReduced x hxLN
      have hxP' : -(nu ^ 2 * eval x LB ^ 13) = 0 := by
        simp only [eval_sub, eval_mul, eval_C, eval_pow] at hxP
        rw [hxLN] at hxP
        norm_num at hxP ⊢
        exact hxP
      exact (neg_ne_zero.mpr
        (mul_ne_zero (pow_ne_zero _ hnu) (pow_ne_zero _ hxLB))) hxP'
    · have hxLB : eval x LB = 0 :=
        (pow_eq_zero_iff (by norm_num : 7 ≠ 0)).mp hxLBpow
      have hxLN : eval x LN ≠ 0 := by
        intro hxLNzero
        exact hlambdaReduced x hxLNzero hxLB
      have hxP' : (19683 : K) * eval x LN ^ 13 = 0 := by
        simp only [eval_sub, eval_mul, eval_C, eval_pow] at hxP
        rw [hxLB] at hxP
        norm_num at hxP ⊢
        exact hxP
      exact (mul_ne_zero (by norm_num : (19683 : K) ≠ 0)
        (pow_ne_zero _ hxLN)) hxP'
  · rw [natDegree_mul
      (mul_ne_zero (C_ne_zero.mpr (by norm_num)) (pow_ne_zero _ hLN))
        (pow_ne_zero _ hLB),
      natDegree_mul (C_ne_zero.mpr (by norm_num)) (pow_ne_zero _ hLN),
      natDegree_C, natDegree_pow, natDegree_pow, zero_add]

/-- The singular mixed fibre has no nonconstant polynomial-core terminal
trajectory.  For a reduced `lambda = LN/LB`, the exact two-pole cusp function
has numerator `19683 LN^13 - nu^2 LB^13` and denominator
`1458 LN^6 LB^7`.  Rational exactness would force that denominator to have
one finite root and its numerator not to grow at infinity; the two degree
conditions force `LN` and `LB` to be constant, contradicting the nonzero
terminal derivative. -/
theorem GCD369CubeMixedCuspTerminalExclusion {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K]
    (nu j : K) (hnu : nu ≠ 0) (hj : j ≠ 0)
    (s LN LB : K[X]) (hs : s ≠ 0) (hLN : LN ≠ 0) (hLB : LB ≠ 0)
    (hsdegree : 0 < s.natDegree)
    (hlambdaReduced : ∀ x : K, eval x LN = 0 → eval x LB ≠ 0)
    (hODE :
      let P := C 19683 * LN ^ 13 - C (nu ^ 2) * LB ^ 13
      let Q := C 1458 * LN ^ 6 * LB ^ 7
      s * (derivative P * Q - P * derivative Q) = C j * Q ^ 2) : False := by
  let P : K[X] := C 19683 * LN ^ 13 - C (nu ^ 2) * LB ^ 13
  let Q : K[X] := C 1458 * LN ^ 6 * LB ^ 7
  change s * (derivative P * Q - P * derivative Q) = C j * Q ^ 2 at hODE
  have hQ : Q ≠ 0 := by
    dsimp [Q]
    exact mul_ne_zero
      (mul_ne_zero (C_ne_zero.mpr (by norm_num)) (pow_ne_zero _ hLN))
      (pow_ne_zero _ hLB)
  have hjC : C j ≠ (0 : K[X]) := C_ne_zero.mpr hj
  have hQ2 : Q ^ 2 ≠ 0 := pow_ne_zero _ hQ
  have hright : C j * Q ^ 2 ≠ 0 := mul_ne_zero hjC hQ2
  have hP : P ≠ 0 := by
    intro hPzero
    rw [hPzero, derivative_zero, zero_mul, zero_mul, sub_zero, mul_zero] at hODE
    exact hright hODE.symm
  have hPred : ∀ x : K, eval x P = 0 → eval x Q ≠ 0 := by
    intro x hxP hxQ
    have hxQ' := hxQ
    dsimp [Q] at hxQ'
    simp only [eval_mul, eval_C, eval_pow] at hxQ'
    rcases mul_eq_zero.mp hxQ' with hfirst | hxLBpow
    · have hxLNpow : eval x LN ^ 6 = 0 :=
        (mul_eq_zero.mp hfirst).resolve_left (by norm_num)
      have hxLN : eval x LN = 0 :=
          (pow_eq_zero_iff (by norm_num : 6 ≠ 0)).mp hxLNpow
      have hxLB : eval x LB ≠ 0 := hlambdaReduced x hxLN
      have hxLBpowNe : eval x LB ^ 13 ≠ 0 := pow_ne_zero _ hxLB
      have hxP' : -(nu ^ 2 * eval x LB ^ 13) = 0 := by
        dsimp [P] at hxP
        simp only [eval_sub, eval_mul, eval_C, eval_pow] at hxP
        rw [hxLN] at hxP
        norm_num at hxP ⊢
        exact hxP
      exact (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hnu) hxLBpowNe)) hxP'
    · have hxLB : eval x LB = 0 :=
        (pow_eq_zero_iff (by norm_num : 7 ≠ 0)).mp hxLBpow
      have hxLN : eval x LN ≠ 0 := by
        intro hxLNzero
        exact hlambdaReduced x hxLNzero hxLB
      have hxLNpowNe : eval x LN ^ 13 ≠ 0 := pow_ne_zero _ hxLN
      have hxP' : (19683 : K) * eval x LN ^ 13 = 0 := by
        dsimp [P] at hxP
        simp only [eval_sub, eval_mul, eval_C, eval_pow] at hxP
        rw [hxLB] at hxP
        norm_num at hxP ⊢
        exact hxP
      exact (mul_ne_zero (by norm_num : (19683 : K) ≠ 0) hxLNpowNe) hxP'
  have hdegreeLe : P.natDegree ≤ Q.natDegree :=
    GCD369CubeRationalPrimitiveNumeratorDegreeLe s P Q j hs hP hQ hj hsdegree
      hPred hODE
  obtain ⟨a, m, hm, _, hQform⟩ :=
    GCD369CubeRationalPrimitiveNonconstantCore s P Q j hs hP hQ hj hsdegree
      hPred hODE
  have h19683 : (19683 : K) ≠ 0 := by norm_num
  have hnu2 : nu ^ 2 ≠ 0 := pow_ne_zero _ hnu
  have h1458 : (1458 : K) ≠ 0 := by norm_num
  have hleftTerm : C 19683 * LN ^ 13 ≠ (0 : K[X]) :=
    mul_ne_zero (C_ne_zero.mpr h19683) (pow_ne_zero _ hLN)
  have hrightTerm : C (nu ^ 2) * LB ^ 13 ≠ (0 : K[X]) :=
    mul_ne_zero (C_ne_zero.mpr hnu2) (pow_ne_zero _ hLB)
  have hQdegree : Q.natDegree = 6 * LN.natDegree + 7 * LB.natDegree := by
    dsimp [Q]
    rw [natDegree_mul
      (mul_ne_zero (C_ne_zero.mpr h1458) (pow_ne_zero _ hLN)) (pow_ne_zero _ hLB),
      natDegree_mul (C_ne_zero.mpr h1458) (pow_ne_zero _ hLN),
      natDegree_C, natDegree_pow, natDegree_pow, zero_add]
  have hLNle : LN.natDegree ≤ LB.natDegree := by
    by_contra hle
    have hlt : LB.natDegree < LN.natDegree := Nat.lt_of_not_ge hle
    have htermDegrees :
        (C (nu ^ 2) * LB ^ 13).natDegree < (C 19683 * LN ^ 13).natDegree := by
      rw [natDegree_C_mul hnu2, natDegree_C_mul h19683,
        natDegree_pow, natDegree_pow]
      omega
    have hPdegree : P.natDegree = 13 * LN.natDegree := by
      dsimp [P]
      rw [natDegree_sub_eq_left_of_natDegree_lt htermDegrees,
        natDegree_C_mul h19683, natDegree_pow]
    omega
  have hLBle : LB.natDegree ≤ LN.natDegree := by
    by_contra hle
    have hlt : LN.natDegree < LB.natDegree := Nat.lt_of_not_ge hle
    have htermDegrees :
        (C 19683 * LN ^ 13).natDegree < (C (nu ^ 2) * LB ^ 13).natDegree := by
      rw [natDegree_C_mul h19683, natDegree_C_mul hnu2,
        natDegree_pow, natDegree_pow]
      omega
    have hPdegree : P.natDegree = 13 * LB.natDegree := by
      dsimp [P]
      rw [natDegree_sub_eq_right_of_natDegree_lt htermDegrees,
        natDegree_C_mul hnu2, natDegree_pow]
    omega
  have hdegrees : LN.natDegree = LB.natDegree := Nat.le_antisymm hLNle hLBle
  have hQrootUnique (x : K) (hxQ : Q.IsRoot x) : x = a := by
    have hxQ' : eval x Q = 0 := hxQ
    rw [hQform] at hxQ'
    simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X] at hxQ'
    have hlc : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
    have hxpow : (x - a) ^ (m - 1) = 0 :=
      (mul_eq_zero.mp hxQ').resolve_left hlc
    have hexponent : m - 1 ≠ 0 := by omega
    exact sub_eq_zero.mp ((pow_eq_zero_iff hexponent).mp hxpow)
  have hLNdegree : LN.natDegree = 0 := by
    by_contra hpos
    have hLNpos : 0 < LN.natDegree := Nat.pos_of_ne_zero hpos
    have hLBpos : 0 < LB.natDegree := by omega
    obtain ⟨x, hxLN⟩ := IsAlgClosed.exists_root LN
      (ne_of_gt (natDegree_pos_iff_degree_pos.mp hLNpos))
    obtain ⟨y, hyLB⟩ := IsAlgClosed.exists_root LB
      (ne_of_gt (natDegree_pos_iff_degree_pos.mp hLBpos))
    have hxQ : Q.IsRoot x := by
      have hxLNeval : eval x LN = 0 := hxLN
      dsimp [Q, IsRoot]
      simp [hxLNeval]
    have hyQ : Q.IsRoot y := by
      have hyLBeval : eval y LB = 0 := hyLB
      dsimp [Q, IsRoot]
      simp [hyLBeval]
    have hxa : x = a := hQrootUnique x hxQ
    have hya : y = a := hQrootUnique y hyQ
    have hxLB : LB.IsRoot x := by simpa [hxa, hya] using hyLB
    exact hlambdaReduced x (by simpa [IsRoot] using hxLN)
      (by simpa [IsRoot] using hxLB)
  have hLBdegree : LB.natDegree = 0 := by omega
  have hLNderivative : derivative LN = 0 := derivative_eq_zero.mpr hLNdegree
  have hLBderivative : derivative LB = 0 := derivative_eq_zero.mpr hLBdegree
  have hPderivative : derivative P = 0 := by
    dsimp [P]
    simp [derivative_sub, derivative_mul, derivative_pow, hLNderivative, hLBderivative]
  have hQderivative : derivative Q = 0 := by
    dsimp [Q]
    simp [derivative_mul, derivative_pow, hLNderivative, hLBderivative]
  rw [hPderivative, hQderivative, zero_mul, mul_zero, sub_zero, mul_zero] at hODE
  exact hright hODE.symm

/-- Constant polynomial cores cannot support the mixed cusp either: constant
exactness forces an affine rational primitive, whereas the cusp denominator
can be constant only when `lambda` itself is constant. -/
theorem GCD369CubeMixedCuspConstantTerminalExclusion {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K]
    (nu j : K) (hnu : nu ≠ 0) (hj : j ≠ 0)
    (s LN LB : K[X]) (hs : s ≠ 0) (hLN : LN ≠ 0) (hLB : LB ≠ 0)
    (hsdegree : s.natDegree = 0)
    (hlambdaReduced : ∀ x : K, eval x LN = 0 → eval x LB ≠ 0)
    (hODE :
      let P := C 19683 * LN ^ 13 - C (nu ^ 2) * LB ^ 13
      let Q := C 1458 * LN ^ 6 * LB ^ 7
      s * (derivative P * Q - P * derivative Q) = C j * Q ^ 2) : False := by
  let P : K[X] := C 19683 * LN ^ 13 - C (nu ^ 2) * LB ^ 13
  let Q : K[X] := C 1458 * LN ^ 6 * LB ^ 7
  change s * (derivative P * Q - P * derivative Q) = C j * Q ^ 2 at hODE
  obtain ⟨hQ, hPred, hQdegree⟩ :=
    GCD369CubeMixedCuspReducedPresentation nu hnu LN LB hLN hLB hlambdaReduced
  change Q ≠ 0 at hQ
  change (∀ x : K, eval x P = 0 → eval x Q ≠ 0) at hPred
  change Q.natDegree = 6 * LN.natDegree + 7 * LB.natDegree at hQdegree
  have hjC : C j ≠ (0 : K[X]) := C_ne_zero.mpr hj
  have hQ2 : Q ^ 2 ≠ 0 := pow_ne_zero _ hQ
  have hright : C j * Q ^ 2 ≠ 0 := mul_ne_zero hjC hQ2
  have hP : P ≠ 0 := by
    intro hPzero
    rw [hPzero, derivative_zero, zero_mul, zero_mul, sub_zero, mul_zero] at hODE
    exact hright hODE.symm
  obtain ⟨hQconstant, hPaffine⟩ :=
    GCD369CubeRationalPrimitiveConstantCore s P Q j hs hP hQ hj hsdegree
      hPred hODE
  have hLNdegree : LN.natDegree = 0 := by omega
  have hLBdegree : LB.natDegree = 0 := by omega
  have hLNderivative : derivative LN = 0 := derivative_eq_zero.mpr hLNdegree
  have hLBderivative : derivative LB = 0 := derivative_eq_zero.mpr hLBdegree
  have hPderivative : derivative P = 0 := by
    dsimp [P]
    simp [derivative_sub, derivative_mul, derivative_pow, hLNderivative, hLBderivative]
  have hPconstant : P.natDegree = 0 := derivative_eq_zero.mp hPderivative
  omega

/-- A nonconstant affine rational primitive cannot be a seventh power.  This
is the constant-core DS terminal obstruction in reduced numerator/denominator
form. -/
theorem GCD369CubeDSConstantCoreTerminalExclusion {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K]
    (j : K) (hj : j ≠ 0) (s LN LB : K[X])
    (hs : s ≠ 0) (hLN : LN ≠ 0) (hLB : LB ≠ 0)
    (hsdegree : s.natDegree = 0)
    (hlambdaReduced : ∀ x : K, eval x LN = 0 → eval x LB ≠ 0)
    (hODE :
      s * (derivative (LN ^ 7) * LB ^ 7 - LN ^ 7 * derivative (LB ^ 7)) =
        C j * (LB ^ 7) ^ 2) : False := by
  have hP : LN ^ 7 ≠ 0 := pow_ne_zero _ hLN
  have hQ : LB ^ 7 ≠ 0 := pow_ne_zero _ hLB
  have hReduced : ∀ x : K, eval x (LN ^ 7) = 0 → eval x (LB ^ 7) ≠ 0 := by
    intro x hx
    simp only [eval_pow] at hx ⊢
    have hxLN : eval x LN = 0 :=
      (pow_eq_zero_iff (by norm_num : 7 ≠ 0)).mp hx
    exact pow_ne_zero _ (hlambdaReduced x hxLN)
  obtain ⟨hQdegree, hPdegree⟩ :=
    GCD369CubeRationalPrimitiveConstantCore s (LN ^ 7) (LB ^ 7) j
      hs hP hQ hj hsdegree hReduced hODE
  rw [natDegree_pow] at hQdegree hPdegree
  omega

/-- In the monomial-core DS branch, rational exactness forces the core
exponent to be `1 mod 7`, exactly the arithmetic precursor to the original
boundary-resultant exclusion. -/
theorem GCD369CubeDSMonomialExponent {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K]
    (j : K) (hj : j ≠ 0) (s LN LB : K[X])
    (hs : s ≠ 0) (hLN : LN ≠ 0) (hLB : LB ≠ 0)
    (hsdegree : 0 < s.natDegree)
    (hlambdaReduced : ∀ x : K, eval x LN = 0 → eval x LB ≠ 0)
    (hODE :
      s * (derivative (LN ^ 7) * LB ^ 7 - LN ^ 7 * derivative (LB ^ 7)) =
        C j * (LB ^ 7) ^ 2) :
    ∃ a : K, ∃ m : ℕ, 2 ≤ m ∧
      s = C s.leadingCoeff * (X - C a) ^ m ∧ 7 ∣ m - 1 := by
  have hP : LN ^ 7 ≠ 0 := pow_ne_zero _ hLN
  have hQ : LB ^ 7 ≠ 0 := pow_ne_zero _ hLB
  have hReduced : ∀ x : K, eval x (LN ^ 7) = 0 → eval x (LB ^ 7) ≠ 0 := by
    intro x hx
    simp only [eval_pow] at hx ⊢
    have hxLN : eval x LN = 0 :=
      (pow_eq_zero_iff (by norm_num : 7 ≠ 0)).mp hx
    exact pow_ne_zero _ (hlambdaReduced x hxLN)
  obtain ⟨a, m, hm, hsform, hQform⟩ :=
    GCD369CubeRationalPrimitiveNonconstantCore s (LN ^ 7) (LB ^ 7) j
      hs hP hQ hj hsdegree hReduced hODE
  have hQdegree := congrArg natDegree hQform
  rw [natDegree_pow, natDegree_C_mul (leadingCoeff_ne_zero.mpr hQ),
    natDegree_pow, natDegree_X_sub_C] at hQdegree
  simp only [mul_one] at hQdegree
  refine ⟨a, m, hm, hsform, ?_⟩
  exact ⟨LB.natDegree, hQdegree.symm⟩

#print axioms GCD369CubeLowerRowTriangularity
#print axioms GCD369CubeZeroSheetBracket
#print axioms GCD369CubeDSBracket
#print axioms GCD369CubeDSBoundaryBezout
#print axioms GCD369CubeDoubleRootNormalObstruction
#print axioms GCD369CubeExceptionalOrbitSquarefree
#print axioms GCD369CubeDExceptionalSupport
#print axioms GCD369CubeDExceptionalCoordinatesNonzero
#print axioms GCD369CubeDExceptionalTerminalNonzero
#print axioms GCD369CubeDExceptionalNoCommonRootOnUChart
#print axioms GCD369CubeDExceptionalNoCommonRoot
#print axioms GCD369CubeC7Support
#print axioms GCD369CubeC7TerminalNonzero
#print axioms GCD369CubeC7NoCommonRootOnUZeroChart
#print axioms GCD369CubeC7NoCommonRootOnUChart
#print axioms GCD369CubeC7NoCommonRoot
#print axioms GCD369CubeC5Support
#print axioms GCD369CubeC5TerminalNonzero
#print axioms GCD369CubeC5NoCommonRootOnUChart
#print axioms GCD369CubeC5NoCommonRoot
#print axioms GCD369CubeC4Support
#print axioms GCD369CubeC4TerminalNonzero
#print axioms GCD369CubeC4NoCommonRootOnUZeroChart
#print axioms GCD369CubeC4NoCommonRootOnUChart
#print axioms GCD369CubeC4NoCommonRoot
#print axioms GCD369CubeC2Support
#print axioms GCD369CubeC2TerminalNonzero
#print axioms GCD369CubeC2NoCommonRootOnUChart
#print axioms GCD369CubeC2NoCommonRoot
#print axioms GCD369CubeC1Support
#print axioms GCD369CubeC1TerminalNonzero
#print axioms GCD369CubeC1NoCommonRootOnUZeroChart
#print axioms GCD369CubeC1NoCommonRootOnVZeroChart
#print axioms GCD369CubeC1NoCommonRoot
#print axioms GCD369CubeRhoOneSupport
#print axioms GCD369CubeRhoOneTerminalNonzero
#print axioms GCD369CubeRhoOneNoCommonRootOnVZeroChart
#print axioms GCD369CubeRhoOneNoCommonRoot
#print axioms GCD369CubeRhoTwoSupport
#print axioms GCD369CubeRhoTwoTerminalNonzero
#print axioms GCD369CubeRhoTwoNoCommonRootOnUZeroChart
#print axioms GCD369CubeRhoTwoNoCommonRoot
#print axioms GCD369CubeRhoFourFirstLoadImpossible
#print axioms GCD369CubeTerminalOnlyQuadraticImpossible
#print axioms GCD369CubeConstantPoleDegreeAudit
#print axioms GCD369CubeBoundaryWeightAudit
#print axioms GCD369CubeBoundaryFirstOrderSeparation
#print axioms GCD369CubeCommonCubicBoundaryFirstOrderSeparation
#print axioms GCD369CubeBoundaryCancellationOrder
#print axioms GCD369CubeBoundaryCancellationOrderWithHigherTerms
#print axioms GCD369CubeBoundaryRegularityContradiction
#print axioms GCD369CubeEarlyBoundaryRegularityContradiction
#print axioms GCD369ReducedQuotientWronskianLocal
#print axioms GCD369CubeRationalPrimitiveFinitePlace
#print axioms GCD369CubeRationalPrimitiveRootCount
#print axioms GCD369ReducedQuotientWronskianDegree
#print axioms GCD369CubeRationalPrimitiveOneRoot
#print axioms GCD369CubeRationalPrimitiveConstantCore
#print axioms GCD369CubeRationalPrimitiveNumeratorDegreeLe
#print axioms GCD369CubeRationalPrimitiveNonconstantCore
#print axioms GCD369CubeMixedEllipticConstancy
#print axioms GCD369CubeUnmixedEllipticConstancy
#print axioms GCD369CubeMixedCuspIdentity
#print axioms GCD369CubeMixedCuspPoleData
#print axioms GCD369CubeMixedCuspReducedPresentation
#print axioms GCD369CubeMixedCuspTerminalExclusion
#print axioms GCD369CubeMixedCuspConstantTerminalExclusion
#print axioms GCD369CubeDSConstantCoreTerminalExclusion
#print axioms GCD369CubeDSMonomialExponent
