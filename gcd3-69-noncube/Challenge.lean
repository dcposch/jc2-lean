/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch (direction), OpenAI Codex agent (formalization)
-/
import Mathlib

/-!
# Challenge: the lower-Pfaffian noncube gate at partial degrees `(6,9)`

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- At least one of the two finite forbidden-value numerators is
nonconstant whenever a polynomial numerator/denominator pair is nonconstant
as a pair. -/
theorem GCD369ForbiddenNumerator {K : Type*} [Field K] [CharZero K]
    (N D : K[X]) (t : K) (ht : t ≠ 0)
    (hnonconstant : 0 < N.natDegree ∨ 0 < D.natDegree) :
    0 < (N - C t * D).natDegree ∨ 0 < (N + C t * D).natDegree := by
  sorry

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
  sorry

/-- On the special fibre `C=kappa²+mu=0`, the elliptic-sheet equation factors
without division into the zero-bracket intersection and the shifted
Davenport--Stothers sheet. -/
theorem GCD369SpecialFibreDichotomy {K : Type*} [Field K] [CharZero K]
    (a2 a4 kappa mu : K) (hC : kappa ^ 2 + mu = 0)
    (hEB : 384 * a2 ^ 3 - 432 * a2 ^ 2 * a4 ^ 2 + 144 * a2 * a4 ^ 4
      - 15 * a4 ^ 6 + 1024 * (kappa ^ 2 + mu) = 0) :
    let X := 8 * a2 - 2 * a4 ^ 2
    X = 0 ∨ X = 3 * a4 ^ 2 := by
  sorry

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
  sorry

/-- The terminal equation on the shifted Davenport--Stothers sheet descends
exactly through `s³=h`, `lambda=s²q` to the rational weighted ODE used by the
valuation closure. -/
theorem GCD369ShiftedDSTerminalDescent {K : Type*} [Field K] [CharZero K]
    (s h lambda q sdot qdot hdot lambdaDot : K) (hs : s ^ 3 = h)
    (hlambda : lambda = s ^ 2 * q) (hhdot : hdot = 3 * s ^ 2 * sdot)
    (hlambdaDot : lambdaDot = 2 * s * sdot * q + s ^ 2 * qdot) :
    567 * s * lambda ^ 6 * lambdaDot
      = 189 * h ^ 4 * q ^ 6 * (2 * hdot * q + 3 * h * qdot) := by
  sorry

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
  sorry

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
  sorry

/-- Degree at infinity of the weighted Wronskian.  The only possible leading
cancellation is the explicit resonance `2 deg(H) = 3 deg(B)`. -/
theorem GCD369WeightedWronskianDegree {K : Type*} [Field K] [CharZero K]
    (H B : K[X]) (hH : H ≠ 0) (hB : B ≠ 0)
    (hHdegree : 0 < H.natDegree) (hBdegree : 0 < B.natDegree)
    (hnonresonant :
      (2 : K) * (H.natDegree : K) ≠ 3 * (B.natDegree : K)) :
    (2 * derivative H * B - 3 * H * derivative B).natDegree
      = H.natDegree + B.natDegree - 1 := by
  sorry

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
  sorry

/-- In a reduced presentation `q = N / B` with `B ≠ 0`, the cleared shifted
Davenport--Stothers ODE forces the numerator `N` to be constant. -/
theorem GCD369ShiftedDSNumeratorConstant {K : Type*} [Field K] [CharZero K]
    [IsAlgClosed K] (H N B : K[X]) (j : K) (hB : B ≠ 0) (hj : j ≠ 0)
    (hreduced : ∀ x : K, eval x N = 0 → eval x B ≠ 0)
    (hODE :
      C 189 * H ^ 4 * N ^ 6
          * (2 * derivative H * N * B
            + 3 * H * (derivative N * B - N * derivative B))
        = C j * B ^ 8) :
    N.natDegree = 0 := by
  sorry

/-- Complete valuation closure for a reduced rational trajectory
`q = N / B`: the numerator is constant, the common support is a singleton,
the local exponents are explicit, and the core is a cube. -/
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
  sorry

/-- The shifted Davenport--Stothers sheet has no reduced rational trajectory
in the noncube Kummer branch.  The finite-place classification and one-point
support conclusion are derived from the ODE rather than assumed. -/
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
  sorry

/-- The infinity-degree arithmetic in the shifted Davenport--Stothers
valuation classification forces a single finite support point. -/
theorem GCD369DSInfinitySupport (r totalK Hdeg Bdeg : Nat)
    (hH : Hdeg = 3 * r + 7 * totalK) (hB : Bdeg = 2 * r + 5 * totalK)
    (hdegree : 5 * Hdeg = 7 * Bdeg + 1) : r = 1 := by
  sorry

/-- Once the one-point valuation classification has exponent `3+7k`, the
historical divisibility by three makes the polynomial Kummer core a cube.
The algebraic-closedness hypothesis is used only to extract a cube root of
the leading scalar. -/
theorem GCD369DSOneRootCube {K : Type*} [Field K] [IsAlgClosed K]
    (c a : K) (k : Nat) (hdiv : 3 ∣ 3 + 7 * k) :
    ∃ u : K[X], C c * (X - C a) ^ (3 + 7 * k) = u ^ 3 := by
  sorry
