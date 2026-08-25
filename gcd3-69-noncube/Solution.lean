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

/-- The degree-six member of the aligned eight-high-row normal form. -/
noncomputable def GCD369AlignedF {K : Type*} [Field K]
    (a0 a1 a2 a3 a4 : K) : K[X] :=
  X ^ 6 + C a4 * X ^ 4 + C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0

/-- The degree-nine member of the aligned eight-high-row normal form, with
the sole surviving high-row integration constant `kappa`. -/
noncomputable def GCD369AlignedG {K : Type*} [Field K]
    (a0 a1 a2 a3 a4 kappa : K) : K[X] :=
  X ^ 9
    + C (3 * a4 / 2) * X ^ 7
    + C (3 * a3 / 2) * X ^ 6
    + C (3 * (4 * a2 + a4 ^ 2) / 8) * X ^ 5
    + C (3 * (2 * a1 + a3 * a4) / 4) * X ^ 4
    + C ((24 * a0 + 12 * a2 * a4 + 6 * a3 ^ 2 - a4 ^ 3) / 16) * X ^ 3
    + C (3 * (4 * a1 * a4 + 4 * a2 * a3 - a3 * a4 ^ 2) / 16) * X ^ 2
    + C (3 * (32 * a0 * a4 + 32 * a1 * a3 + 16 * a2 ^ 2
        - 8 * a2 * a4 ^ 2 - 8 * a3 ^ 2 * a4 + a4 ^ 4) / 128) * X
    + C ((24 * a0 * a3 + 24 * a1 * a2 - 6 * a1 * a4 ^ 2
        - 12 * a2 * a3 * a4 - 2 * a3 ^ 3 + 3 * a3 * a4 ^ 3) / 32)
    + C kappa * (X ^ 3 + C (a4 / 2) * X + C (a3 / 2))

/-- Evaluation at a differential indeterminate commutes with formal
polynomial differentiation when the derivation kills the coefficient field
and sends the indeterminate to one. -/
theorem GCD369PolynomialEvalDerivative {k L : Type*} [Field k] [Field L]
    [Algebra k L] [Differential L] (x : L)
    (hconst : ∀ c : k, Differential.deriv (algebraMap k L c) = 0)
    (hx : Differential.deriv x = 1) (P : k[X]) :
    Differential.deriv (aeval x P) = aeval x P.derivative := by
  rw [Derivation.apply_aeval_eq (R := ℤ) (A := k) Differential.deriv x P]
  rw [hx]
  simp only [smul_eq_mul, mul_one]
  let dk : Derivation ℤ k L := Differential.deriv.compAlgebraMap k
  have hz : dk.mapCoeffs P = 0 := by
    ext n
    simp [dk, hconst]
  rw [hz]
  simp

set_option maxHeartbeats 2000000 in
/-- The complete five-row lower bracket after clearing the common denominator `128`.
The identity is universal over a commutative ring: `fx` and `Gx` are the
formal `z`-derivatives, while `fdot` and `Gdot` are coefficient velocities. -/
theorem GCD369LowerBracketIdentity {R : Type*} [CommRing R]
    (x a0 a1 a2 a3 a4 kappa v0 v1 v2 v3 v4 : R) :
    let fx :=
      6 * x ^ 5 + 4 * a4 * x ^ 3 + 3 * a3 * x ^ 2 + 2 * a2 * x + a1
    let Gx :=
      1152 * x ^ 8
        + 1344 * a4 * x ^ 6
        + 1152 * a3 * x ^ 5
        + 240 * (4 * a2 + a4 ^ 2) * x ^ 4
        + 384 * (2 * a1 + a3 * a4) * x ^ 3
        + 24 * (24 * a0 + 12 * a2 * a4 + 6 * a3 ^ 2 - a4 ^ 3) * x ^ 2
        + 48 * (4 * a1 * a4 + 4 * a2 * a3 - a3 * a4 ^ 2) * x
        + 3 * (32 * a0 * a4 + 32 * a1 * a3 + 16 * a2 ^ 2
            - 8 * a2 * a4 ^ 2 - 8 * a3 ^ 2 * a4 + a4 ^ 4)
        + 384 * kappa * x ^ 2 + 64 * kappa * a4
    let fdot := v4 * x ^ 4 + v3 * x ^ 3 + v2 * x ^ 2 + v1 * x + v0
    let Gdot :=
      192 * v4 * x ^ 7
        + 192 * v3 * x ^ 6
        + 48 * (4 * v2 + 2 * a4 * v4) * x ^ 5
        + 96 * (2 * v1 + v3 * a4 + a3 * v4) * x ^ 4
        + 8 * (24 * v0 + 12 * (v2 * a4 + a2 * v4) + 12 * a3 * v3
            - 3 * a4 ^ 2 * v4) * x ^ 3
        + 24 * (4 * (v1 * a4 + a1 * v4) + 4 * (v2 * a3 + a2 * v3)
            - (v3 * a4 ^ 2 + 2 * a3 * a4 * v4)) * x ^ 2
        + 3 * (32 * (v0 * a4 + a0 * v4) + 32 * (v1 * a3 + a1 * v3)
            + 32 * a2 * v2 - 8 * (v2 * a4 ^ 2 + 2 * a2 * a4 * v4)
            - 8 * (2 * a3 * v3 * a4 + a3 ^ 2 * v4) + 4 * a4 ^ 3 * v4) * x
        + 4 * (24 * (v0 * a3 + a0 * v3) + 24 * (v1 * a2 + a1 * v2)
            - 6 * (v1 * a4 ^ 2 + 2 * a1 * a4 * v4)
            - 12 * (v2 * a3 * a4 + a2 * v3 * a4 + a2 * a3 * v4)
            - 6 * a3 ^ 2 * v3 + 3 * (v3 * a4 ^ 3 + 3 * a3 * a4 ^ 2 * v4))
        + 64 * kappa * v4 * x + 64 * kappa * v3
    let row4 := 3 * (-96 * a0 * a4 * v4 + 192 * a0 * v2 - 96 * a1 * a3 * v4
        - 96 * a1 * a4 * v3 + 192 * a1 * v1 - 48 * a2 ^ 2 * v4
        - 96 * a2 * a3 * v3 + 72 * a2 * a4 ^ 2 * v4 - 96 * a2 * a4 * v2
        + 192 * a2 * v0 + 72 * a3 ^ 2 * a4 * v4 - 48 * a3 ^ 2 * v2
        + 72 * a3 * a4 ^ 2 * v3 - 96 * a3 * a4 * v1 - 15 * a4 ^ 4 * v4
        + 24 * a4 ^ 3 * v2 - 48 * a4 ^ 2 * v0 - 64 * a4 * kappa * v4
        + 128 * kappa * v2)
    let row3 := 3 * (-96 * a0 * a3 * v4 - 96 * a0 * a4 * v3 + 192 * a0 * v1
        - 96 * a1 * a2 * v4 - 96 * a1 * a3 * v3 + 72 * a1 * a4 ^ 2 * v4
        - 96 * a1 * a4 * v2 + 192 * a1 * v0 - 48 * a2 ^ 2 * v3
        + 144 * a2 * a3 * a4 * v4 - 96 * a2 * a3 * v2
        + 72 * a2 * a4 ^ 2 * v3 - 96 * a2 * a4 * v1 + 24 * a3 ^ 3 * v4
        + 72 * a3 ^ 2 * a4 * v3 - 48 * a3 ^ 2 * v1 - 60 * a3 * a4 ^ 3 * v4
        + 72 * a3 * a4 ^ 2 * v2 - 96 * a3 * a4 * v0 - 64 * a3 * kappa * v4
        - 15 * a4 ^ 4 * v3 + 24 * a4 ^ 3 * v1 - 64 * a4 * kappa * v3
        + 128 * kappa * v1)
    let row2 := -192 * a0 * a2 * v4 - 288 * a0 * a3 * v3 + 96 * a0 * a4 * v2
        + 576 * a0 * v0 - 96 * a1 ^ 2 * v4 - 288 * a1 * a2 * v3
        + 192 * a1 * a3 * a4 * v4 - 288 * a1 * a3 * v2 + 24 * a1 * a4 ^ 2 * v3
        + 96 * a1 * a4 * v1 + 96 * a2 ^ 2 * a4 * v4 - 144 * a2 ^ 2 * v2
        + 192 * a2 * a3 ^ 2 * v4 + 240 * a2 * a3 * a4 * v3
        - 288 * a2 * a3 * v1 - 24 * a2 * a4 ^ 3 * v4 + 24 * a2 * a4 ^ 2 * v2
        + 96 * a2 * a4 * v0 - 128 * a2 * kappa * v4 + 72 * a3 ^ 3 * v3
        - 108 * a3 ^ 2 * a4 ^ 2 * v4 + 120 * a3 ^ 2 * a4 * v2
        - 144 * a3 ^ 2 * v0 - 36 * a3 * a4 ^ 3 * v3 + 24 * a3 * a4 ^ 2 * v1
        - 192 * a3 * kappa * v3 + 3 * a4 ^ 4 * v2 - 24 * a4 ^ 3 * v0
        + 64 * a4 * kappa * v2 + 384 * kappa * v0
    let row1 := -96 * a0 * a1 * v4 - 192 * a0 * a2 * v3 + 96 * a0 * a4 * v1
        - 96 * a1 ^ 2 * v3 + 144 * a1 * a2 * a4 * v4 - 288 * a1 * a2 * v2
        + 24 * a1 * a3 ^ 2 * v4 + 48 * a1 * a3 * a4 * v3 - 12 * a1 * a4 ^ 3 * v4
        + 24 * a1 * a4 ^ 2 * v2 + 96 * a1 * a4 * v0 - 64 * a1 * kappa * v4
        + 96 * a2 ^ 2 * a3 * v4 + 96 * a2 ^ 2 * a4 * v3 - 144 * a2 ^ 2 * v1
        + 48 * a2 * a3 ^ 2 * v3 - 72 * a2 * a3 * a4 ^ 2 * v4
        + 96 * a2 * a3 * a4 * v2 - 24 * a2 * a4 ^ 3 * v3 + 24 * a2 * a4 ^ 2 * v1
        - 128 * a2 * kappa * v3 - 24 * a3 ^ 2 * a4 * v1 - 48 * a3 * a4 ^ 2 * v0
        + 3 * a4 ^ 4 * v1 + 64 * a4 * kappa * v1
    let row0 := -96 * a0 * a1 * v3 + 96 * a0 * a4 * v0 + 48 * a1 ^ 2 * a4 * v4
        - 96 * a1 ^ 2 * v2 + 48 * a1 * a2 * a3 * v4 + 48 * a1 * a2 * a4 * v3
        - 96 * a1 * a2 * v1 + 24 * a1 * a3 ^ 2 * v3 - 36 * a1 * a3 * a4 ^ 2 * v4
        + 48 * a1 * a3 * a4 * v2 - 12 * a1 * a4 ^ 3 * v3 + 24 * a1 * a4 ^ 2 * v1
        - 64 * a1 * kappa * v3 + 48 * a2 ^ 2 * v0 - 24 * a2 * a4 ^ 2 * v0
        - 24 * a3 ^ 2 * a4 * v0 + 3 * a4 ^ 4 * v0 + 64 * a4 * kappa * v0
    fdot * Gx - fx * Gdot =
      row4 * x ^ 4 + row3 * x ^ 3 + row2 * x ^ 2 + row1 * x + row0 := by
  dsimp only
  ring


set_option maxHeartbeats 2000000 in
/-- Vanishing of the four lower zero rows makes the four triangular
Pfaffian invariants differential constants.  The displayed normalizations are
the integral multiples used by `GCD369InvariantFibreDichotomy`. -/
theorem GCD369LowerFirstIntegrals {K : Type*} [Field K] [CharZero K] [Differential K]
    (a0 a1 a2 a3 a4 kappa : K) (hkappa : Differential.deriv kappa = 0) :
    let v0 := Differential.deriv a0
    let v1 := Differential.deriv a1
    let v2 := Differential.deriv a2
    let v3 := Differential.deriv a3
    let v4 := Differential.deriv a4
    let row4 := 3 * (-96 * a0 * a4 * v4 + 192 * a0 * v2 - 96 * a1 * a3 * v4
        - 96 * a1 * a4 * v3 + 192 * a1 * v1 - 48 * a2 ^ 2 * v4
        - 96 * a2 * a3 * v3 + 72 * a2 * a4 ^ 2 * v4 - 96 * a2 * a4 * v2
        + 192 * a2 * v0 + 72 * a3 ^ 2 * a4 * v4 - 48 * a3 ^ 2 * v2
        + 72 * a3 * a4 ^ 2 * v3 - 96 * a3 * a4 * v1 - 15 * a4 ^ 4 * v4
        + 24 * a4 ^ 3 * v2 - 48 * a4 ^ 2 * v0 - 64 * a4 * kappa * v4
        + 128 * kappa * v2)
    let row3 := 3 * (-96 * a0 * a3 * v4 - 96 * a0 * a4 * v3 + 192 * a0 * v1
        - 96 * a1 * a2 * v4 - 96 * a1 * a3 * v3 + 72 * a1 * a4 ^ 2 * v4
        - 96 * a1 * a4 * v2 + 192 * a1 * v0 - 48 * a2 ^ 2 * v3
        + 144 * a2 * a3 * a4 * v4 - 96 * a2 * a3 * v2
        + 72 * a2 * a4 ^ 2 * v3 - 96 * a2 * a4 * v1 + 24 * a3 ^ 3 * v4
        + 72 * a3 ^ 2 * a4 * v3 - 48 * a3 ^ 2 * v1 - 60 * a3 * a4 ^ 3 * v4
        + 72 * a3 * a4 ^ 2 * v2 - 96 * a3 * a4 * v0 - 64 * a3 * kappa * v4
        - 15 * a4 ^ 4 * v3 + 24 * a4 ^ 3 * v1 - 64 * a4 * kappa * v3
        + 128 * kappa * v1)
    let row2 := -192 * a0 * a2 * v4 - 288 * a0 * a3 * v3 + 96 * a0 * a4 * v2
        + 576 * a0 * v0 - 96 * a1 ^ 2 * v4 - 288 * a1 * a2 * v3
        + 192 * a1 * a3 * a4 * v4 - 288 * a1 * a3 * v2 + 24 * a1 * a4 ^ 2 * v3
        + 96 * a1 * a4 * v1 + 96 * a2 ^ 2 * a4 * v4 - 144 * a2 ^ 2 * v2
        + 192 * a2 * a3 ^ 2 * v4 + 240 * a2 * a3 * a4 * v3
        - 288 * a2 * a3 * v1 - 24 * a2 * a4 ^ 3 * v4 + 24 * a2 * a4 ^ 2 * v2
        + 96 * a2 * a4 * v0 - 128 * a2 * kappa * v4 + 72 * a3 ^ 3 * v3
        - 108 * a3 ^ 2 * a4 ^ 2 * v4 + 120 * a3 ^ 2 * a4 * v2
        - 144 * a3 ^ 2 * v0 - 36 * a3 * a4 ^ 3 * v3 + 24 * a3 * a4 ^ 2 * v1
        - 192 * a3 * kappa * v3 + 3 * a4 ^ 4 * v2 - 24 * a4 ^ 3 * v0
        + 64 * a4 * kappa * v2 + 384 * kappa * v0
    let row1 := -96 * a0 * a1 * v4 - 192 * a0 * a2 * v3 + 96 * a0 * a4 * v1
        - 96 * a1 ^ 2 * v3 + 144 * a1 * a2 * a4 * v4 - 288 * a1 * a2 * v2
        + 24 * a1 * a3 ^ 2 * v4 + 48 * a1 * a3 * a4 * v3 - 12 * a1 * a4 ^ 3 * v4
        + 24 * a1 * a4 ^ 2 * v2 + 96 * a1 * a4 * v0 - 64 * a1 * kappa * v4
        + 96 * a2 ^ 2 * a3 * v4 + 96 * a2 ^ 2 * a4 * v3 - 144 * a2 ^ 2 * v1
        + 48 * a2 * a3 ^ 2 * v3 - 72 * a2 * a3 * a4 ^ 2 * v4
        + 96 * a2 * a3 * a4 * v2 - 24 * a2 * a4 ^ 3 * v3 + 24 * a2 * a4 ^ 2 * v1
        - 128 * a2 * kappa * v3 - 24 * a3 ^ 2 * a4 * v1 - 48 * a3 * a4 ^ 2 * v0
        + 3 * a4 ^ 4 * v1 + 64 * a4 * kappa * v1
    let I4 := 3 * (64 * a0 * a2 - 16 * a0 * a4 ^ 2 + 32 * a1 ^ 2
        - 32 * a1 * a3 * a4 - 16 * a2 ^ 2 * a4 - 16 * a2 * a3 ^ 2
        + 8 * a2 * a4 ^ 3 + 12 * a3 ^ 2 * a4 ^ 2 - a4 ^ 5)
        + 32 * kappa * (4 * a2 - a4 ^ 2)
    let I3 := 3 * (64 * a0 * a1 - 32 * a0 * a3 * a4 - 32 * a1 * a2 * a4
        - 16 * a1 * a3 ^ 2 + 8 * a1 * a4 ^ 3 - 16 * a2 ^ 2 * a3
        + 24 * a2 * a3 * a4 ^ 2 + 8 * a3 ^ 3 * a4 - 5 * a3 * a4 ^ 4)
        + 64 * kappa * (2 * a1 - a3 * a4)
    let I2 :=
      1152 * a0 ^ 2 - 768 * a0 * a2 * a4 - 576 * a0 * a3 ^ 2
        + 192 * a0 * a4 ^ 3 + 1536 * a0 * kappa - 384 * a1 ^ 2 * a4
        - 1152 * a1 * a2 * a3 + 672 * a1 * a3 * a4 ^ 2 - 192 * a2 ^ 3
        + 336 * a2 ^ 2 * a4 ^ 2 + 768 * a2 * a3 ^ 2 * a4 - 132 * a2 * a4 ^ 4
        - 512 * a2 * a4 * kappa + 72 * a3 ^ 4 - 288 * a3 ^ 2 * a4 ^ 3
        - 384 * a3 ^ 2 * kappa + 15 * a4 ^ 6 + 128 * a4 ^ 3 * kappa
    let I1 :=
      96 * a0 * a1 * a4 + 192 * a0 * a2 * a3 - 96 * a0 * a3 * a4 ^ 2
        + 96 * a1 ^ 2 * a3 + 144 * a1 * a2 ^ 2 - 120 * a1 * a2 * a4 ^ 2
        - 120 * a1 * a3 ^ 2 * a4 + 21 * a1 * a4 ^ 4 + 64 * a1 * a4 * kappa
        - 144 * a2 ^ 2 * a3 * a4 - 48 * a2 * a3 ^ 3 + 96 * a2 * a3 * a4 ^ 3
        + 128 * a2 * a3 * kappa + 48 * a3 ^ 3 * a4 ^ 2 - 15 * a3 * a4 ^ 5
        - 64 * a3 * a4 ^ 2 * kappa
    row4 = 0 → row3 = 0 → row2 = 0 → row1 = 0 →
      Differential.deriv I4 = 0 ∧ Differential.deriv I3 = 0
        ∧ Differential.deriv I2 = 0 ∧ Differential.deriv I1 = 0 := by
  dsimp only
  intro hrow4 hrow3 hrow2 hrow1
  have hnat (n : ℕ) : Differential.deriv (n : K) = 0 :=
    Differential.deriv.map_natCast n
  have hOfNat (n : ℕ) [n.AtLeastTwo] :
      Differential.deriv (ofNat(n) : K) = 0 := by
    exact hnat n
  have hconstOfNat (n : ℕ) [n.AtLeastTwo] (x : K) :
      Differential.deriv ((ofNat(n) : K) * x) =
        (ofNat(n) : K) * Differential.deriv x := by
    rw [Derivation.leibniz, hOfNat]
    simp
  have hI4 : Differential.deriv
      (3 * (64 * a0 * a2 - 16 * a0 * a4 ^ 2 + 32 * a1 ^ 2
        - 32 * a1 * a3 * a4 - 16 * a2 ^ 2 * a4 - 16 * a2 * a3 ^ 2
        + 8 * a2 * a4 ^ 3 + 12 * a3 ^ 2 * a4 ^ 2 - a4 ^ 5)
        + 32 * kappa * (4 * a2 - a4 ^ 2)) =
      (3 * (-96 * a0 * a4 * Differential.deriv a4
        + 192 * a0 * Differential.deriv a2 - 96 * a1 * a3 * Differential.deriv a4
        - 96 * a1 * a4 * Differential.deriv a3 + 192 * a1 * Differential.deriv a1
        - 48 * a2 ^ 2 * Differential.deriv a4 - 96 * a2 * a3 * Differential.deriv a3
        + 72 * a2 * a4 ^ 2 * Differential.deriv a4
        - 96 * a2 * a4 * Differential.deriv a2 + 192 * a2 * Differential.deriv a0
        + 72 * a3 ^ 2 * a4 * Differential.deriv a4
        - 48 * a3 ^ 2 * Differential.deriv a2
        + 72 * a3 * a4 ^ 2 * Differential.deriv a3
        - 96 * a3 * a4 * Differential.deriv a1 - 15 * a4 ^ 4 * Differential.deriv a4
        + 24 * a4 ^ 3 * Differential.deriv a2
        - 48 * a4 ^ 2 * Differential.deriv a0
        - 64 * a4 * kappa * Differential.deriv a4
        + 128 * kappa * Differential.deriv a2)) / 3 := by
    simp only [map_add, map_sub, hconstOfNat, Derivation.leibniz,
      Derivation.leibniz_pow, hkappa]
    ring
  have hI3 : Differential.deriv
      (3 * (64 * a0 * a1 - 32 * a0 * a3 * a4 - 32 * a1 * a2 * a4
        - 16 * a1 * a3 ^ 2 + 8 * a1 * a4 ^ 3 - 16 * a2 ^ 2 * a3
        + 24 * a2 * a3 * a4 ^ 2 + 8 * a3 ^ 3 * a4 - 5 * a3 * a4 ^ 4)
        + 64 * kappa * (2 * a1 - a3 * a4)) =
      (3 * (-96 * a0 * a3 * Differential.deriv a4
        - 96 * a0 * a4 * Differential.deriv a3 + 192 * a0 * Differential.deriv a1
        - 96 * a1 * a2 * Differential.deriv a4 - 96 * a1 * a3 * Differential.deriv a3
        + 72 * a1 * a4 ^ 2 * Differential.deriv a4
        - 96 * a1 * a4 * Differential.deriv a2 + 192 * a1 * Differential.deriv a0
        - 48 * a2 ^ 2 * Differential.deriv a3
        + 144 * a2 * a3 * a4 * Differential.deriv a4
        - 96 * a2 * a3 * Differential.deriv a2
        + 72 * a2 * a4 ^ 2 * Differential.deriv a3
        - 96 * a2 * a4 * Differential.deriv a1 + 24 * a3 ^ 3 * Differential.deriv a4
        + 72 * a3 ^ 2 * a4 * Differential.deriv a3
        - 48 * a3 ^ 2 * Differential.deriv a1
        - 60 * a3 * a4 ^ 3 * Differential.deriv a4
        + 72 * a3 * a4 ^ 2 * Differential.deriv a2
        - 96 * a3 * a4 * Differential.deriv a0
        - 64 * a3 * kappa * Differential.deriv a4
        - 15 * a4 ^ 4 * Differential.deriv a3
        + 24 * a4 ^ 3 * Differential.deriv a1
        - 64 * a4 * kappa * Differential.deriv a3
        + 128 * kappa * Differential.deriv a1)) / 3 := by
    simp only [map_add, map_sub, hconstOfNat, Derivation.leibniz,
      Derivation.leibniz_pow, hkappa]
    ring
  have hI2 : Differential.deriv
      (1152 * a0 ^ 2 - 768 * a0 * a2 * a4 - 576 * a0 * a3 ^ 2
        + 192 * a0 * a4 ^ 3 + 1536 * a0 * kappa - 384 * a1 ^ 2 * a4
        - 1152 * a1 * a2 * a3 + 672 * a1 * a3 * a4 ^ 2 - 192 * a2 ^ 3
        + 336 * a2 ^ 2 * a4 ^ 2 + 768 * a2 * a3 ^ 2 * a4 - 132 * a2 * a4 ^ 4
        - 512 * a2 * a4 * kappa + 72 * a3 ^ 4 - 288 * a3 ^ 2 * a4 ^ 3
        - 384 * a3 ^ 2 * kappa + 15 * a4 ^ 6 + 128 * a4 ^ 3 * kappa) =
      4 * (-192 * a0 * a2 * Differential.deriv a4
        - 288 * a0 * a3 * Differential.deriv a3 + 96 * a0 * a4 * Differential.deriv a2
        + 576 * a0 * Differential.deriv a0 - 96 * a1 ^ 2 * Differential.deriv a4
        - 288 * a1 * a2 * Differential.deriv a3
        + 192 * a1 * a3 * a4 * Differential.deriv a4
        - 288 * a1 * a3 * Differential.deriv a2
        + 24 * a1 * a4 ^ 2 * Differential.deriv a3
        + 96 * a1 * a4 * Differential.deriv a1
        + 96 * a2 ^ 2 * a4 * Differential.deriv a4
        - 144 * a2 ^ 2 * Differential.deriv a2
        + 192 * a2 * a3 ^ 2 * Differential.deriv a4
        + 240 * a2 * a3 * a4 * Differential.deriv a3
        - 288 * a2 * a3 * Differential.deriv a1
        - 24 * a2 * a4 ^ 3 * Differential.deriv a4
        + 24 * a2 * a4 ^ 2 * Differential.deriv a2
        + 96 * a2 * a4 * Differential.deriv a0
        - 128 * a2 * kappa * Differential.deriv a4
        + 72 * a3 ^ 3 * Differential.deriv a3
        - 108 * a3 ^ 2 * a4 ^ 2 * Differential.deriv a4
        + 120 * a3 ^ 2 * a4 * Differential.deriv a2
        - 144 * a3 ^ 2 * Differential.deriv a0
        - 36 * a3 * a4 ^ 3 * Differential.deriv a3
        + 24 * a3 * a4 ^ 2 * Differential.deriv a1
        - 192 * a3 * kappa * Differential.deriv a3
        + 3 * a4 ^ 4 * Differential.deriv a2
        - 24 * a4 ^ 3 * Differential.deriv a0
        + 64 * a4 * kappa * Differential.deriv a2
        + 384 * kappa * Differential.deriv a0)
      - 2 * a4 * (3 * (-96 * a0 * a4 * Differential.deriv a4
        + 192 * a0 * Differential.deriv a2 - 96 * a1 * a3 * Differential.deriv a4
        - 96 * a1 * a4 * Differential.deriv a3 + 192 * a1 * Differential.deriv a1
        - 48 * a2 ^ 2 * Differential.deriv a4 - 96 * a2 * a3 * Differential.deriv a3
        + 72 * a2 * a4 ^ 2 * Differential.deriv a4
        - 96 * a2 * a4 * Differential.deriv a2 + 192 * a2 * Differential.deriv a0
        + 72 * a3 ^ 2 * a4 * Differential.deriv a4
        - 48 * a3 ^ 2 * Differential.deriv a2
        + 72 * a3 * a4 ^ 2 * Differential.deriv a3
        - 96 * a3 * a4 * Differential.deriv a1
        - 15 * a4 ^ 4 * Differential.deriv a4
        + 24 * a4 ^ 3 * Differential.deriv a2
        - 48 * a4 ^ 2 * Differential.deriv a0
        - 64 * a4 * kappa * Differential.deriv a4
        + 128 * kappa * Differential.deriv a2)) := by
    simp only [map_add, map_sub, hconstOfNat, Derivation.leibniz,
      Derivation.leibniz_pow, hkappa]
    ring
  have hI1 : Differential.deriv
      (96 * a0 * a1 * a4 + 192 * a0 * a2 * a3 - 96 * a0 * a3 * a4 ^ 2
        + 96 * a1 ^ 2 * a3 + 144 * a1 * a2 ^ 2 - 120 * a1 * a2 * a4 ^ 2
        - 120 * a1 * a3 ^ 2 * a4 + 21 * a1 * a4 ^ 4 + 64 * a1 * a4 * kappa
        - 144 * a2 ^ 2 * a3 * a4 - 48 * a2 * a3 ^ 3 + 96 * a2 * a3 * a4 ^ 3
        + 128 * a2 * a3 * kappa + 48 * a3 ^ 3 * a4 ^ 2 - 15 * a3 * a4 ^ 5
        - 64 * a3 * a4 ^ 2 * kappa) =
      -(-96 * a0 * a1 * Differential.deriv a4
        - 192 * a0 * a2 * Differential.deriv a3 + 96 * a0 * a4 * Differential.deriv a1
        - 96 * a1 ^ 2 * Differential.deriv a3
        + 144 * a1 * a2 * a4 * Differential.deriv a4
        - 288 * a1 * a2 * Differential.deriv a2
        + 24 * a1 * a3 ^ 2 * Differential.deriv a4
        + 48 * a1 * a3 * a4 * Differential.deriv a3
        - 12 * a1 * a4 ^ 3 * Differential.deriv a4
        + 24 * a1 * a4 ^ 2 * Differential.deriv a2
        + 96 * a1 * a4 * Differential.deriv a0
        - 64 * a1 * kappa * Differential.deriv a4
        + 96 * a2 ^ 2 * a3 * Differential.deriv a4
        + 96 * a2 ^ 2 * a4 * Differential.deriv a3
        - 144 * a2 ^ 2 * Differential.deriv a1
        + 48 * a2 * a3 ^ 2 * Differential.deriv a3
        - 72 * a2 * a3 * a4 ^ 2 * Differential.deriv a4
        + 96 * a2 * a3 * a4 * Differential.deriv a2
        - 24 * a2 * a4 ^ 3 * Differential.deriv a3
        + 24 * a2 * a4 ^ 2 * Differential.deriv a1
        - 128 * a2 * kappa * Differential.deriv a3
        - 24 * a3 ^ 2 * a4 * Differential.deriv a1
        - 48 * a3 * a4 ^ 2 * Differential.deriv a0
        + 3 * a4 ^ 4 * Differential.deriv a1
        + 64 * a4 * kappa * Differential.deriv a1)
      + (a3 * (3 * (-96 * a0 * a4 * Differential.deriv a4
        + 192 * a0 * Differential.deriv a2 - 96 * a1 * a3 * Differential.deriv a4
        - 96 * a1 * a4 * Differential.deriv a3 + 192 * a1 * Differential.deriv a1
        - 48 * a2 ^ 2 * Differential.deriv a4 - 96 * a2 * a3 * Differential.deriv a3
        + 72 * a2 * a4 ^ 2 * Differential.deriv a4
        - 96 * a2 * a4 * Differential.deriv a2 + 192 * a2 * Differential.deriv a0
        + 72 * a3 ^ 2 * a4 * Differential.deriv a4
        - 48 * a3 ^ 2 * Differential.deriv a2
        + 72 * a3 * a4 ^ 2 * Differential.deriv a3
        - 96 * a3 * a4 * Differential.deriv a1
        - 15 * a4 ^ 4 * Differential.deriv a4
        + 24 * a4 ^ 3 * Differential.deriv a2
        - 48 * a4 ^ 2 * Differential.deriv a0
        - 64 * a4 * kappa * Differential.deriv a4
        + 128 * kappa * Differential.deriv a2))
        + a4 * (3 * (-96 * a0 * a3 * Differential.deriv a4
          - 96 * a0 * a4 * Differential.deriv a3 + 192 * a0 * Differential.deriv a1
          - 96 * a1 * a2 * Differential.deriv a4
          - 96 * a1 * a3 * Differential.deriv a3
          + 72 * a1 * a4 ^ 2 * Differential.deriv a4
          - 96 * a1 * a4 * Differential.deriv a2 + 192 * a1 * Differential.deriv a0
          - 48 * a2 ^ 2 * Differential.deriv a3
          + 144 * a2 * a3 * a4 * Differential.deriv a4
          - 96 * a2 * a3 * Differential.deriv a2
          + 72 * a2 * a4 ^ 2 * Differential.deriv a3
          - 96 * a2 * a4 * Differential.deriv a1
          + 24 * a3 ^ 3 * Differential.deriv a4
          + 72 * a3 ^ 2 * a4 * Differential.deriv a3
          - 48 * a3 ^ 2 * Differential.deriv a1
          - 60 * a3 * a4 ^ 3 * Differential.deriv a4
          + 72 * a3 * a4 ^ 2 * Differential.deriv a2
          - 96 * a3 * a4 * Differential.deriv a0
          - 64 * a3 * kappa * Differential.deriv a4
          - 15 * a4 ^ 4 * Differential.deriv a3
          + 24 * a4 ^ 3 * Differential.deriv a1
          - 64 * a4 * kappa * Differential.deriv a3
          + 128 * kappa * Differential.deriv a1))) / 3 := by
    simp only [map_add, map_sub, hconstOfNat, Derivation.leibniz,
      Derivation.leibniz_pow, hkappa]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hI4, hrow4]
    simp
  · rw [hI3, hrow3]
    simp
  · rw [hI2, hrow2, hrow4]
    ring
  · rw [hI1, hrow1, hrow4, hrow3]
    ring


set_option maxHeartbeats 2000000 in
/-- The coefficient weights `(0,2,1,0,2,0)` induce invariant weights
`(1,2,0,1)` modulo three. -/
theorem GCD369KummerInvariantWeights {K : Type*} [Field K] [CharZero K]
    (sigma : K ≃+* K) (omega a0 a1 a2 a3 a4 kappa : K)
    (homega3 : omega ^ 3 = 1)
    (ha0 : sigma a0 = a0) (ha1 : sigma a1 = omega ^ 2 * a1)
    (ha2 : sigma a2 = omega * a2) (ha3 : sigma a3 = a3)
    (ha4 : sigma a4 = omega ^ 2 * a4) (hkappa : sigma kappa = kappa) :
    let p4 := 3 * (64 * a0 * a2 - 16 * a0 * a4 ^ 2 + 32 * a1 ^ 2
        - 32 * a1 * a3 * a4 - 16 * a2 ^ 2 * a4 - 16 * a2 * a3 ^ 2
        + 8 * a2 * a4 ^ 3 + 12 * a3 ^ 2 * a4 ^ 2 - a4 ^ 5)
        + 32 * kappa * (4 * a2 - a4 ^ 2)
    let p3 := 3 * (64 * a0 * a1 - 32 * a0 * a3 * a4 - 32 * a1 * a2 * a4
        - 16 * a1 * a3 ^ 2 + 8 * a1 * a4 ^ 3 - 16 * a2 ^ 2 * a3
        + 24 * a2 * a3 * a4 ^ 2 + 8 * a3 ^ 3 * a4 - 5 * a3 * a4 ^ 4)
        + 64 * kappa * (2 * a1 - a3 * a4)
    let n2 :=
      1152 * a0 ^ 2 - 768 * a0 * a2 * a4 - 576 * a0 * a3 ^ 2
        + 192 * a0 * a4 ^ 3 + 1536 * a0 * kappa - 384 * a1 ^ 2 * a4
        - 1152 * a1 * a2 * a3 + 672 * a1 * a3 * a4 ^ 2 - 192 * a2 ^ 3
        + 336 * a2 ^ 2 * a4 ^ 2 + 768 * a2 * a3 ^ 2 * a4 - 132 * a2 * a4 ^ 4
        - 512 * a2 * a4 * kappa + 72 * a3 ^ 4 - 288 * a3 ^ 2 * a4 ^ 3
        - 384 * a3 ^ 2 * kappa + 15 * a4 ^ 6 + 128 * a4 ^ 3 * kappa
    let p1 :=
      96 * a0 * a1 * a4 + 192 * a0 * a2 * a3 - 96 * a0 * a3 * a4 ^ 2
        + 96 * a1 ^ 2 * a3 + 144 * a1 * a2 ^ 2 - 120 * a1 * a2 * a4 ^ 2
        - 120 * a1 * a3 ^ 2 * a4 + 21 * a1 * a4 ^ 4 + 64 * a1 * a4 * kappa
        - 144 * a2 ^ 2 * a3 * a4 - 48 * a2 * a3 ^ 3 + 96 * a2 * a3 * a4 ^ 3
        + 128 * a2 * a3 * kappa + 48 * a3 ^ 3 * a4 ^ 2 - 15 * a3 * a4 ^ 5
        - 64 * a3 * a4 ^ 2 * kappa
    sigma p4 = omega * p4 ∧ sigma p3 = omega ^ 2 * p3
      ∧ sigma n2 = n2 ∧ sigma p1 = omega * p1 := by
  have hperiod (n : Nat) : omega ^ (n + 3) = omega ^ n := by
    rw [pow_add, homega3, mul_one]
  have h4 : omega ^ 4 = omega := by simpa using hperiod 1
  have h5 : omega ^ 5 = omega ^ 2 := by simpa using hperiod 2
  have h6 : omega ^ 6 = 1 := by
    calc
      omega ^ 6 = omega ^ 3 := by simpa using hperiod 3
      _ = 1 := homega3
  have h7 : omega ^ 7 = omega := by simpa using hperiod 4 |>.trans h4
  have h8 : omega ^ 8 = omega ^ 2 := by simpa using hperiod 5 |>.trans h5
  have h9 : omega ^ 9 = 1 := by simpa using hperiod 6 |>.trans h6
  have h10 : omega ^ 10 = omega := by simpa using hperiod 7 |>.trans h7
  have h11 : omega ^ 11 = omega ^ 2 := by simpa using hperiod 8 |>.trans h8
  have h12 : omega ^ 12 = 1 := by simpa using hperiod 9 |>.trans h9
  dsimp only
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, ha0, ha1, ha2, ha3,
    ha4, hkappa]
  constructor
  · ring_nf
    simp only [h4, h7, h10]
    ring
  constructor
  · ring_nf
    simp only [h5, h8]
    ring
  constructor
  · ring_nf
    simp only [homega3, h6, h9, h12]
    ring
  · ring_nf
    simp only [h4, h7, h10]
    ring

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

/-- Cyclic Kummer weights force the three nonzero-weight first integrals to
vanish.  The weight-zero integral descends to a fixed differential constant;
the fixed-constant hypothesis isolates the constant-field input. -/
theorem GCD369KummerInvariantLanding {K : Type*} [Field K] [CharZero K]
    [Differential K] (sigma : K ≃+* K) (omega p4 p3 n2 p1 : K)
    (homega : omega ≠ 1) (homega2 : omega ^ 2 ≠ 1)
    (hfix : ∀ c : K, Differential.deriv c = 0 → sigma c = c)
    (hd4 : Differential.deriv p4 = 0) (hd3 : Differential.deriv p3 = 0)
    (hd2 : Differential.deriv n2 = 0) (hd1 : Differential.deriv p1 = 0)
    (hw4 : sigma p4 = omega * p4) (hw3 : sigma p3 = omega ^ 2 * p3)
    (hw2 : sigma n2 = n2) (hw1 : sigma p1 = omega * p1) :
    p4 = 0 ∧ p3 = 0 ∧ p1 = 0 ∧
      ∃ mu : K, Differential.deriv mu = 0 ∧ sigma mu = mu ∧ n2 - 512 * mu = 0 := by
  have hp4fix := hfix p4 hd4
  have hp3fix := hfix p3 hd3
  have hp1fix := hfix p1 hd1
  have h4prod : (omega - 1) * p4 = 0 := by
    rw [sub_mul, one_mul, ← hw4]
    exact sub_eq_zero.mpr hp4fix
  have h3prod : (omega ^ 2 - 1) * p3 = 0 := by
    rw [sub_mul, one_mul, ← hw3]
    exact sub_eq_zero.mpr hp3fix
  have h1prod : (omega - 1) * p1 = 0 := by
    rw [sub_mul, one_mul, ← hw1]
    exact sub_eq_zero.mpr hp1fix
  have hp4 : p4 = 0 :=
    (mul_eq_zero.mp h4prod).resolve_left (sub_ne_zero.mpr homega)
  have hp3 : p3 = 0 :=
    (mul_eq_zero.mp h3prod).resolve_left (sub_ne_zero.mpr homega2)
  have hp1 : p1 = 0 :=
    (mul_eq_zero.mp h1prod).resolve_left (sub_ne_zero.mpr homega)
  refine ⟨hp4, hp3, hp1, n2 / 512, ?_, ?_, ?_⟩
  · have h512 : Differential.deriv (512 : K) = 0 :=
      Differential.deriv.map_natCast 512
    rw [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv, hd2, h512]
    simp
  · simp only [map_div₀, hw2, map_ofNat]
  · field_simp
    ring

/-- Composition of constant first integrals, coefficient weights, and the
complete reduced invariant-fibre decomposition. -/
theorem GCD369KummerFibreDichotomy {K : Type*} [Field K] [CharZero K]
    [Differential K] (sigma : K ≃+* K) (omega a0 a1 a2 a3 a4 kappa : K)
    (homega3 : omega ^ 3 = 1) (homega : omega ≠ 1) (homega2 : omega ^ 2 ≠ 1)
    (hfix : ∀ c : K, Differential.deriv c = 0 → sigma c = c)
    (ha0 : sigma a0 = a0) (ha1 : sigma a1 = omega ^ 2 * a1)
    (ha2 : sigma a2 = omega * a2) (ha3 : sigma a3 = a3)
    (ha4 : sigma a4 = omega ^ 2 * a4) (hkappa : sigma kappa = kappa) :
    let A := 4 * a2 - a4 ^ 2
    let B := 2 * a1 - a3 * a4
    let w := 4 * a0 - a3 ^ 2
    let e4 :=
      64 * a0 * a2 - 16 * a0 * a4 ^ 2 + 32 * a1 ^ 2 - 32 * a1 * a3 * a4
        - 16 * a2 ^ 2 * a4 - 16 * a2 * a3 ^ 2 + 8 * a2 * a4 ^ 3
        + 12 * a3 ^ 2 * a4 ^ 2 - a4 ^ 5
    let e3 :=
      64 * a0 * a1 - 32 * a0 * a3 * a4 - 32 * a1 * a2 * a4
        - 16 * a1 * a3 ^ 2 + 8 * a1 * a4 ^ 3 - 16 * a2 ^ 2 * a3
        + 24 * a2 * a3 * a4 ^ 2 + 8 * a3 ^ 3 * a4 - 5 * a3 * a4 ^ 4
    let p4 := 3 * e4 + 32 * kappa * A
    let p3 := 3 * e3 + 64 * kappa * B
    let n2 :=
      1152 * a0 ^ 2 - 768 * a0 * a2 * a4 - 576 * a0 * a3 ^ 2
        + 192 * a0 * a4 ^ 3 + 1536 * a0 * kappa - 384 * a1 ^ 2 * a4
        - 1152 * a1 * a2 * a3 + 672 * a1 * a3 * a4 ^ 2 - 192 * a2 ^ 3
        + 336 * a2 ^ 2 * a4 ^ 2 + 768 * a2 * a3 ^ 2 * a4 - 132 * a2 * a4 ^ 4
        - 512 * a2 * a4 * kappa + 72 * a3 ^ 4 - 288 * a3 ^ 2 * a4 ^ 3
        - 384 * a3 ^ 2 * kappa + 15 * a4 ^ 6 + 128 * a4 ^ 3 * kappa
    let p1 :=
      96 * a0 * a1 * a4 + 192 * a0 * a2 * a3 - 96 * a0 * a3 * a4 ^ 2
        + 96 * a1 ^ 2 * a3 + 144 * a1 * a2 ^ 2 - 120 * a1 * a2 * a4 ^ 2
        - 120 * a1 * a3 ^ 2 * a4 + 21 * a1 * a4 ^ 4 + 64 * a1 * a4 * kappa
        - 144 * a2 ^ 2 * a3 * a4 - 48 * a2 * a3 ^ 3 + 96 * a2 * a3 * a4 ^ 3
        + 128 * a2 * a3 * kappa + 48 * a3 ^ 3 * a4 ^ 2 - 15 * a3 * a4 ^ 5
        - 64 * a3 * a4 ^ 2 * kappa
    Differential.deriv p4 = 0 → Differential.deriv p3 = 0 →
      Differential.deriv n2 = 0 → Differential.deriv p1 = 0 →
      ∃ mu : K, Differential.deriv mu = 0 ∧ sigma mu = mu ∧
        ((A = 0 ∧ B = 0 ∧ 9 * w ^ 2 + 48 * kappa * w - 64 * mu = 0)
          ∨ (a3 = 0 ∧ a1 = 0
            ∧ 384 * a2 ^ 3 - 432 * a2 ^ 2 * a4 ^ 2 + 144 * a2 * a4 ^ 4
                - 15 * a4 ^ 6 + 1024 * (kappa ^ 2 + mu) = 0
            ∧ 48 * a0 - 12 * a2 * a4 + 3 * a4 ^ 3 + 32 * kappa = 0)) := by
  dsimp only
  intro hd4 hd3 hd2 hd1
  have hweights := GCD369KummerInvariantWeights sigma omega a0 a1 a2 a3 a4 kappa
    homega3 ha0 ha1 ha2 ha3 ha4 hkappa
  dsimp only at hweights
  rcases hweights with ⟨hw4, hw3, hw2, hw1⟩
  obtain ⟨hp4, hp3, hp1, mu, hdmu, hsmu, hp2⟩ :=
    GCD369KummerInvariantLanding sigma omega
      (3 * (64 * a0 * a2 - 16 * a0 * a4 ^ 2 + 32 * a1 ^ 2
        - 32 * a1 * a3 * a4 - 16 * a2 ^ 2 * a4 - 16 * a2 * a3 ^ 2
        + 8 * a2 * a4 ^ 3 + 12 * a3 ^ 2 * a4 ^ 2 - a4 ^ 5)
        + 32 * kappa * (4 * a2 - a4 ^ 2))
      (3 * (64 * a0 * a1 - 32 * a0 * a3 * a4 - 32 * a1 * a2 * a4
        - 16 * a1 * a3 ^ 2 + 8 * a1 * a4 ^ 3 - 16 * a2 ^ 2 * a3
        + 24 * a2 * a3 * a4 ^ 2 + 8 * a3 ^ 3 * a4 - 5 * a3 * a4 ^ 4)
        + 64 * kappa * (2 * a1 - a3 * a4))
      (1152 * a0 ^ 2 - 768 * a0 * a2 * a4 - 576 * a0 * a3 ^ 2
        + 192 * a0 * a4 ^ 3 + 1536 * a0 * kappa - 384 * a1 ^ 2 * a4
        - 1152 * a1 * a2 * a3 + 672 * a1 * a3 * a4 ^ 2 - 192 * a2 ^ 3
        + 336 * a2 ^ 2 * a4 ^ 2 + 768 * a2 * a3 ^ 2 * a4 - 132 * a2 * a4 ^ 4
        - 512 * a2 * a4 * kappa + 72 * a3 ^ 4 - 288 * a3 ^ 2 * a4 ^ 3
        - 384 * a3 ^ 2 * kappa + 15 * a4 ^ 6 + 128 * a4 ^ 3 * kappa)
      (96 * a0 * a1 * a4 + 192 * a0 * a2 * a3 - 96 * a0 * a3 * a4 ^ 2
        + 96 * a1 ^ 2 * a3 + 144 * a1 * a2 ^ 2 - 120 * a1 * a2 * a4 ^ 2
        - 120 * a1 * a3 ^ 2 * a4 + 21 * a1 * a4 ^ 4 + 64 * a1 * a4 * kappa
        - 144 * a2 ^ 2 * a3 * a4 - 48 * a2 * a3 ^ 3 + 96 * a2 * a3 * a4 ^ 3
        + 128 * a2 * a3 * kappa + 48 * a3 ^ 3 * a4 ^ 2 - 15 * a3 * a4 ^ 5
        - 64 * a3 * a4 ^ 2 * kappa)
      homega homega2 hfix hd4 hd3 hd2 hd1 hw4 hw3 hw2 hw1
  refine ⟨mu, hdmu, hsmu, ?_⟩
  exact GCD369InvariantFibreDichotomy a0 a1 a2 a3 a4 kappa mu
    hp4 hp3 hp2 hp1

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

/-- The complete eight-high-row normal form restricted to the first reduced
sheet is exactly the common-cubic family used by
`GCD369ZeroBracketSheet`.  Here `a₄=2u`, `a₃=2v`, `a₂=u²`,
`a₁=2uv`, and `a₀=v²+d` have already been substituted. -/
theorem GCD369HighRowZeroSheet {K : Type*} [Field K] [CharZero K]
    (u v d kappa : K) :
    let f : K[X] :=
      X ^ 6 + C (2 * u) * X ^ 4 + C (2 * v) * X ^ 3 + C (u ^ 2) * X ^ 2
        + C (2 * u * v) * X + C (v ^ 2 + d)
    let g : K[X] :=
      X ^ 9
        + C (3 * (2 * u) / 2) * X ^ 7
        + C (3 * (2 * v) / 2) * X ^ 6
        + C (3 * (4 * u ^ 2 + (2 * u) ^ 2) / 8) * X ^ 5
        + C (3 * (2 * (2 * u * v) + (2 * v) * (2 * u)) / 4) * X ^ 4
        + C ((24 * (v ^ 2 + d) + 12 * u ^ 2 * (2 * u)
            + 6 * (2 * v) ^ 2 - (2 * u) ^ 3) / 16) * X ^ 3
        + C (3 * (4 * (2 * u * v) * (2 * u) + 4 * u ^ 2 * (2 * v)
            - (2 * v) * (2 * u) ^ 2) / 16) * X ^ 2
        + C (3 * (32 * (v ^ 2 + d) * (2 * u) + 32 * (2 * u * v) * (2 * v)
            + 16 * (u ^ 2) ^ 2 - 8 * u ^ 2 * (2 * u) ^ 2
            - 8 * (2 * v) ^ 2 * (2 * u) + (2 * u) ^ 4) / 128) * X
        + C ((24 * (v ^ 2 + d) * (2 * v) + 24 * (2 * u * v) * u ^ 2
            - 6 * (2 * u * v) * (2 * u) ^ 2 - 12 * u ^ 2 * (2 * v) * (2 * u)
            - 2 * (2 * v) ^ 3 + 3 * (2 * v) * (2 * u) ^ 3) / 32)
        + C kappa * (X ^ 3 + C u * X + C v)
    let K0 : K[X] := X ^ 3 + C u * X + C v
    f = K0 ^ 2 + C d ∧ g = K0 ^ 3 + C (kappa + 3 * d / 2) * K0 := by
  have hb7 : 3 * (2 * u) / 2 = 3 * u := by ring
  have hb6 : 3 * (2 * v) / 2 = 3 * v := by ring
  have hb5 : 3 * (4 * u ^ 2 + (2 * u) ^ 2) / 8 = 3 * u ^ 2 := by ring
  have hb4 : 3 * (2 * (2 * u * v) + (2 * v) * (2 * u)) / 4 = 6 * u * v := by ring
  have hb3 :
      (24 * (v ^ 2 + d) + 12 * u ^ 2 * (2 * u) + 6 * (2 * v) ^ 2
          - (2 * u) ^ 3) / 16 = u ^ 3 + 3 * v ^ 2 + 3 * d / 2 := by ring
  have hb2 :
      3 * (4 * (2 * u * v) * (2 * u) + 4 * u ^ 2 * (2 * v)
          - (2 * v) * (2 * u) ^ 2) / 16 = 3 * u ^ 2 * v := by ring
  have hb1 :
      3 * (32 * (v ^ 2 + d) * (2 * u) + 32 * (2 * u * v) * (2 * v)
          + 16 * (u ^ 2) ^ 2 - 8 * u ^ 2 * (2 * u) ^ 2
          - 8 * (2 * v) ^ 2 * (2 * u) + (2 * u) ^ 4) / 128
        = 3 * u * v ^ 2 + 3 * u * d / 2 := by ring
  have hb0 :
      (24 * (v ^ 2 + d) * (2 * v) + 24 * (2 * u * v) * u ^ 2
          - 6 * (2 * u * v) * (2 * u) ^ 2 - 12 * u ^ 2 * (2 * v) * (2 * u)
          - 2 * (2 * v) ^ 3 + 3 * (2 * v) * (2 * u) ^ 3) / 32
        = v ^ 3 + 3 * d * v / 2 := by ring
  have hdu : 3 * u * d / 2 = u * (3 * d / 2) := by ring
  have hdv : 3 * d * v / 2 = v * (3 * d / 2) := by ring
  dsimp only
  rw [hb7, hb6, hb5, hb4, hb3, hb2, hb1, hb0]
  constructor
  · simp only [C_mul, C_add, C_sub, C_pow, C_ofNat, C_eq_natCast]
    ring
  · simp only [C_mul, C_add, C_sub, C_pow, C_ofNat, C_eq_natCast]
    rw [hdu, hdv]
    simp only [C_mul]
    ring

set_option maxHeartbeats 2000000 in
/-- The first invariant sheet cannot carry a nonzero terminal Keller row.
This theorem derives the constancy of the lower deformation parameter from
the invariant equation instead of assuming it, identifies the complete
high-row pair with the common-cubic family, and then applies its zero-bracket
identity. -/
theorem GCD369ZeroSheetTerminalExclusion {K : Type*} [Field K] [CharZero K]
    [Differential K] (a0 a1 a2 a3 a4 kappa mu terminal : K)
    (hkappa : Differential.deriv kappa = 0)
    (hmu : Differential.deriv mu = 0)
    (hA : 4 * a2 - a4 ^ 2 = 0) (hB : 2 * a1 - a3 * a4 = 0)
    (hquad : 9 * (4 * a0 - a3 ^ 2) ^ 2
      + 48 * kappa * (4 * a0 - a3 ^ 2) - 64 * mu = 0)
    (hterminal :
      Differential.mapCoeffs (GCD369AlignedF a0 a1 a2 a3 a4)
          * derivative (GCD369AlignedG a0 a1 a2 a3 a4 kappa)
        - derivative (GCD369AlignedF a0 a1 a2 a3 a4)
          * Differential.mapCoeffs (GCD369AlignedG a0 a1 a2 a3 a4 kappa)
        = C terminal)
    (hterminal0 : terminal ≠ 0) : False := by
  let u := a4 / 2
  let v := a3 / 2
  let d := a0 - v ^ 2
  have ha4 : a4 = 2 * u := by dsimp [u]; ring
  have ha3 : a3 = 2 * v := by dsimp [v]; ring
  have ha2 : a2 = u ^ 2 := by
    dsimp [u]
    linear_combination (1 / 4) * hA
  have ha1 : a1 = 2 * u * v := by
    dsimp [u, v]
    linear_combination (1 / 2) * hB
  have ha0 : a0 = v ^ 2 + d := by dsimp [d]; ring
  have hpoly : 9 * d ^ 2 + 12 * kappa * d - 4 * mu = 0 := by
    dsimp [d, v]
    linear_combination (1 / 16) * hquad
  have hnat (n : ℕ) : Differential.deriv (n : K) = 0 :=
    Differential.deriv.map_natCast n
  have hOfNat (n : ℕ) [n.AtLeastTwo] :
      Differential.deriv (ofNat(n) : K) = 0 := hnat n
  have hdpoly := congrArg Differential.deriv hpoly
  have hdprod : (18 * d + 12 * kappa) * Differential.deriv d = 0 := by
    simp only [map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow,
      hOfNat, hkappa, hmu, map_zero] at hdpoly
    linear_combination hdpoly
  have hd : Differential.deriv d = 0 := by
    by_cases hcoef : 18 * d + 12 * kappa = 0
    · have hdcoef := congrArg Differential.deriv hcoef
      simp only [map_add, Derivation.leibniz, hOfNat, hkappa, map_zero] at hdcoef
      linear_combination (1 / 18) * hdcoef
    · exact (mul_eq_zero.mp hdprod).resolve_left hcoef
  rw [ha4, ha3, ha2, ha1, ha0] at hterminal
  rw [GCD369AlignedF, GCD369AlignedG] at hterminal
  have hhigh := GCD369HighRowZeroSheet u v d kappa
  dsimp only at hhigh
  have hu : 2 * u / 2 = u := by ring
  have hv : 2 * v / 2 = v := by ring
  rw [hu, hv] at hterminal
  rw [hhigh.1, hhigh.2] at hterminal
  have hzero := GCD369ZeroBracketSheet (2 * u) (2 * v) d kappa hd hkappa
  dsimp only at hzero
  rw [hu, hv] at hzero
  rw [hzero] at hterminal
  exact hterminal0 (C_injective (by simpa using hterminal.symm))

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

/-- The forbidden-value exclusion on a nonzero elliptic fibre needs no
chosen square root: algebraic closedness supplies one automatically. -/
theorem GCD369EllipticNonzeroExclusionAutoRoot {K : Type*} [Field K]
    [CharZero K] [IsAlgClosed K] (C0 j : K) (hC : C0 ≠ 0) (hj : j ≠ 0)
    (N D H : K[X])
    (hnonconstant : 0 < N.natDegree ∨ 0 < D.natDegree)
    (hcoprime : ∀ x : K, eval x N = 0 → eval x D ≠ 0)
    (hterminal : ∀ x : K, eval x D ≠ 0 →
      let Y := eval x N / eval x D
      let Ydot :=
        eval x (derivative N * D - N * derivative D) / (eval x D) ^ 2
      3 * eval x H * (7 * Y ^ 2 - 12288 * C0) ^ 3 * Ydot ^ 3
        = (147456 * j) ^ 3 * (Y ^ 2 - 4096 * C0)) : False := by
  obtain ⟨t, ht⟩ :=
    IsAlgClosed.exists_pow_nat_eq (12288 * C0 / 7) (by norm_num : 0 < 2)
  apply GCD369EllipticNonzeroExclusion C0 j t hC hj ?_ N D H
    hnonconstant hcoprime hterminal
  linear_combination 7 * ht

/-- Cleared polynomial form of the nonzero-elliptic exclusion.  It is the
result of substituting `Y=N/D` into the cubed terminal equation and
multiplying by `D^12`; hence it is independent of a chosen rational-function
implementation. -/
theorem GCD369EllipticClearedNonzeroExclusion {K : Type*} [Field K]
    [CharZero K] [IsAlgClosed K] (C0 j : K) (hC : C0 ≠ 0) (hj : j ≠ 0)
    (N D H : K[X])
    (hnonconstant : 0 < N.natDegree ∨ 0 < D.natDegree)
    (hcoprime : ∀ x : K, eval x N = 0 → eval x D ≠ 0)
    (hpoly :
      C 3 * H * (C 7 * N ^ 2 - C (12288 * C0) * D ^ 2) ^ 3
          * (derivative N * D - N * derivative D) ^ 3
        = C ((147456 * j) ^ 3) * (N ^ 2 - C (4096 * C0) * D ^ 2) * D ^ 10) :
    False := by
  apply GCD369EllipticNonzeroExclusionAutoRoot C0 j hC hj N D H
    hnonconstant hcoprime
  intro x hxD
  dsimp only
  have heval := congrArg (eval x) hpoly
  simp only [eval_mul, eval_sub, eval_pow, eval_C] at heval ⊢
  field_simp [hxD]
  convert heval using 1 <;> ring

/-- A constant `Y` path on the elliptic sheet is already incompatible with
the uncleared terminal Keller row.  When `X=0`, the polynomial formula for
`beta` vanishes directly; when `X≠0`, the terminal one-form identity forces
the same conclusion. -/
theorem GCD369EllipticConstantExclusion {K : Type*} [Field K] [CharZero K]
    (a2 a4 a2dot a4dot C0 s j : K) (hj : j ≠ 0) :
    let X := 8 * a2 - 2 * a4 ^ 2
    let Y := 3 * a4 * X
    let Xdot := 8 * a2dot - 4 * a4 * a4dot
    let Ydot := 3 * a4dot * X + 3 * a4 * Xdot
    let beta :=
      3 * (4 * a2 - 3 * a4 ^ 2) * (4 * a2 - a4 ^ 2) * (4 * a2 + a4 ^ 2)
          / 2048 * a4dot
        + 3 * a4 * (4 * a2 - a4 ^ 2) * (4 * a2 + a4 ^ 2) / 512 * a2dot
    Y ^ 2 = 3 * X ^ 3 + 4096 * C0 → 2 * Y * Ydot = 9 * X ^ 2 * Xdot →
      Ydot = 0 → s * beta = j → False := by
  dsimp only
  intro hcurve htangent hYdot hKeller
  by_cases hX : 8 * a2 - 2 * a4 ^ 2 = 0
  · have hfactor : 4 * a2 - a4 ^ 2 = 0 := by
      linear_combination (1 / 2) * hX
    have hbeta :
        3 * (4 * a2 - 3 * a4 ^ 2) * (4 * a2 - a4 ^ 2) * (4 * a2 + a4 ^ 2)
              / 2048 * a4dot
            + 3 * a4 * (4 * a2 - a4 ^ 2) * (4 * a2 + a4 ^ 2) / 512 * a2dot = 0 := by
      rw [hfactor]
      ring
    rw [hbeta, mul_zero] at hKeller
    exact hj hKeller.symm
  · have hterminal :=
      GCD369EllipticTerminalForm a2 a4 a2dot a4dot C0 hcurve htangent
    rw [hYdot, mul_zero] at hterminal
    have hleft : (147456 : K) * (8 * a2 - 2 * a4 ^ 2) ≠ 0 :=
      mul_ne_zero (by norm_num) hX
    have hbeta :
        3 * (4 * a2 - 3 * a4 ^ 2) * (4 * a2 - a4 ^ 2) * (4 * a2 + a4 ^ 2)
              / 2048 * a4dot
            + 3 * a4 * (4 * a2 - a4 ^ 2) * (4 * a2 + a4 ^ 2) / 512 * a2dot = 0 :=
      (mul_eq_zero.mp hterminal).resolve_left hleft
    rw [hbeta, mul_zero] at hKeller
    exact hj hKeller.symm

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

/-- The zero-`X` part of the special elliptic fibre is precisely its
intersection with the zero-bracket sheet.  This implication is proved before
any division by `X`. -/
theorem GCD369EllipticZeroXToZeroSheet {K : Type*} [Field K] [CharZero K]
    (a0 a1 a2 a3 a4 kappa mu : K)
    (ha3 : a3 = 0) (ha1 : a1 = 0) (hC : kappa ^ 2 + mu = 0)
    (hlinear : 48 * a0 - 12 * a2 * a4 + 3 * a4 ^ 3 + 32 * kappa = 0)
    (hX : 8 * a2 - 2 * a4 ^ 2 = 0) :
    (4 * a2 - a4 ^ 2 = 0) ∧ (2 * a1 - a3 * a4 = 0)
      ∧ 9 * (4 * a0 - a3 ^ 2) ^ 2 + 48 * kappa * (4 * a0 - a3 ^ 2)
        - 64 * mu = 0 := by
  have hA : 4 * a2 - a4 ^ 2 = 0 := by
    linear_combination (1 / 2) * hX
  have hsmall : 48 * a0 + 32 * kappa = 0 := by
    linear_combination hlinear + (3 * a4 / 2) * hX
  have hsq : (48 * a0 + 32 * kappa) ^ 2 = 0 := by
    rw [hsmall, zero_pow (by norm_num : (2 : Nat) ≠ 0)]
  refine ⟨hA, ?_, ?_⟩
  · rw [ha3, ha1]
    ring
  · rw [ha3]
    linear_combination (1 / 16) * hsq - 64 * hC

/-- On the nonzero-`X` part of the special elliptic fibre, the coefficient
coordinates are exactly the shifted Davenport--Stothers parameters. -/
theorem GCD369EllipticShiftedDSParameters {K : Type*} [Field K] [CharZero K]
    (a0 a2 a4 kappa mu : K) (hC : kappa ^ 2 + mu = 0)
    (hEB : 384 * a2 ^ 3 - 432 * a2 ^ 2 * a4 ^ 2 + 144 * a2 * a4 ^ 4
      - 15 * a4 ^ 6 + 1024 * (kappa ^ 2 + mu) = 0)
    (hX : 8 * a2 - 2 * a4 ^ 2 ≠ 0)
    (hlinear : 48 * a0 - 12 * a2 * a4 + 3 * a4 ^ 3 + 32 * kappa = 0) :
    ∃ lambda : K, a4 = 4 * lambda ∧ a2 = 10 * lambda ^ 2
      ∧ a0 = 6 * lambda ^ 3 - 2 * kappa / 3 := by
  have hsplit := GCD369SpecialFibreDichotomy a2 a4 kappa mu hC hEB
  dsimp only at hsplit
  rcases hsplit with hzero | hshifted
  · exact False.elim (hX hzero)
  · let lambda := a4 / 4
    refine ⟨lambda, by dsimp [lambda]; ring, ?_, ?_⟩
    · dsimp [lambda]
      linear_combination (1 / 8) * hshifted
    · dsimp [lambda]
      linear_combination (1 / 48) * hlinear + (a4 / 32) * hshifted

/-- Substituting the nonzero-`X` special-fibre parameters into the complete
eight-high-row normal form gives exactly the shifted Davenport--Stothers
pair. -/
theorem GCD369HighRowShiftedDS {K : Type*} [Field K] [CharZero K]
    (a0 a1 a2 a3 a4 kappa lambda : K)
    (ha4 : a4 = 4 * lambda) (ha3 : a3 = 0) (ha2 : a2 = 10 * lambda ^ 2)
    (ha1 : a1 = 0) (ha0 : a0 = 6 * lambda ^ 3 - 2 * kappa / 3) :
    let f : K[X] :=
      X ^ 6 + C a4 * X ^ 4 + C a3 * X ^ 3 + C a2 * X ^ 2 + C a1 * X + C a0
    let g : K[X] :=
      X ^ 9
        + C (3 * a4 / 2) * X ^ 7
        + C (3 * a3 / 2) * X ^ 6
        + C (3 * (4 * a2 + a4 ^ 2) / 8) * X ^ 5
        + C (3 * (2 * a1 + a3 * a4) / 4) * X ^ 4
        + C ((24 * a0 + 12 * a2 * a4 + 6 * a3 ^ 2 - a4 ^ 3) / 16) * X ^ 3
        + C (3 * (4 * a1 * a4 + 4 * a2 * a3 - a3 * a4 ^ 2) / 16) * X ^ 2
        + C (3 * (32 * a0 * a4 + 32 * a1 * a3 + 16 * a2 ^ 2
            - 8 * a2 * a4 ^ 2 - 8 * a3 ^ 2 * a4 + a4 ^ 4) / 128) * X
        + C ((24 * a0 * a3 + 24 * a1 * a2 - 6 * a1 * a4 ^ 2
            - 12 * a2 * a3 * a4 - 2 * a3 ^ 3 + 3 * a3 * a4 ^ 3) / 32)
        + C kappa * (X ^ 3 + C (a4 / 2) * X + C (a3 / 2))
    f = X ^ 6 + C (4 * lambda) * X ^ 4 + C (10 * lambda ^ 2) * X ^ 2
          + C (6 * lambda ^ 3 - 2 * kappa / 3)
      ∧ g =
        X ^ 9 + C (6 * lambda) * X ^ 7 + C (21 * lambda ^ 2) * X ^ 5
          + C (35 * lambda ^ 3) * X ^ 3 + C (63 * lambda ^ 4 / 2) * X := by
  rw [ha4, ha3, ha2, ha1, ha0]
  have hb7 : 3 * (4 * lambda) / 2 = 6 * lambda := by ring
  have hhalf4 : 4 * lambda / 2 = 2 * lambda := by ring
  have hb5 : 3 * (4 * (10 * lambda ^ 2) + (4 * lambda) ^ 2) / 8
      = 21 * lambda ^ 2 := by ring
  have hb3 :
      (24 * (6 * lambda ^ 3 - 2 * kappa / 3)
          + 12 * (10 * lambda ^ 2) * (4 * lambda) + 6 * 0 ^ 2 - (4 * lambda) ^ 3) / 16
        = 35 * lambda ^ 3 - kappa := by ring
  have hb1 :
      3 * (32 * (6 * lambda ^ 3 - 2 * kappa / 3) * (4 * lambda)
          + 32 * 0 * 0 + 16 * (10 * lambda ^ 2) ^ 2
          - 8 * (10 * lambda ^ 2) * (4 * lambda) ^ 2
          - 8 * 0 ^ 2 * (4 * lambda) + (4 * lambda) ^ 4) / 128
        = 63 * lambda ^ 4 / 2 - 2 * kappa * lambda := by ring
  dsimp only
  rw [hb7, hhalf4, hb5, hb3, hb1]
  constructor <;>
    simp only [map_zero, C_0, C_mul, C_add, C_sub, C_pow, C_ofNat, C_eq_natCast,
      zero_mul, mul_zero, add_zero, zero_add, sub_zero] <;> simp <;> ring

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
