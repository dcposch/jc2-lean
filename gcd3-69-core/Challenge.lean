/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
-/
import Mathlib

/-!
# Challenge: the cubic-Kummer first gate at partial degrees `(6,9)`

This file states the reusable algebraic core of the new `(6,9)` analysis.
`Solution.lean` proves the same declarations without `sorry` or custom axioms.
-/

open Polynomial
open scoped IntermediateField

/-- The exact cancellation in the `y^13` Jacobian row after writing the
leading coefficients as `a₆=s⁶`, `b₉=s⁹`, `a₅=s⁵A`, `b₈=s⁸B`. -/
theorem GCD369TopRowIdentity {k L : Type*} [CommRing k] [CommRing L] [Algebra k L]
    (D : Derivation k L L) (s A B : L) :
    8 * D (s ^ 6) * (s ^ 8 * B) + 9 * D (s ^ 5 * A) * s ^ 9
        - 6 * s ^ 6 * D (s ^ 8 * B) - 5 * (s ^ 5 * A) * D (s ^ 9)
      = s ^ 14 * (9 * D A - 6 * D B) := by
  sorry

/-- The nontrivial cubic-Kummer branch aligns.  The hypothesis `hconstants`
encodes that the constants of the differential field are fixed by the Kummer
automorphism; `hA` and `hB` are the common weight-one descent laws. -/
theorem GCD369KummerAlignment {k L : Type*} [CommRing k] [CommRing L]
    [IsDomain L] [CharZero L] [Algebra k L] (D : Derivation k L L) (σ : L →ₐ[k] L)
    (s A B ω : L) (hs : s ≠ 0) (hω : ω ≠ 1)
    (hconstants : ∀ c : L, D c = 0 → σ c = c)
    (hA : σ A = ω * A) (hB : σ B = ω * B)
    (htop :
      8 * D (s ^ 6) * (s ^ 8 * B) + 9 * D (s ^ 5 * A) * s ^ 9
          - 6 * s ^ 6 * D (s ^ 8 * B) - 5 * (s ^ 5 * A) * D (s ^ 9) = 0) :
    3 * A - 2 * B = 0 := by
  sorry

/-- Once `3A-2B=0`, the translation `r=A/6` simultaneously removes the
degree-five and degree-eight terms of the normalized degree-six and
degree-nine polynomials. -/
theorem GCD369SimultaneousDepression {K : Type*} [Field K] [CharZero K]
    (A B : K) (halign : 3 * A - 2 * B = 0) :
    let r := A / 6
    let p : K[X] := (X - C r) ^ 6 + C A * (X - C r) ^ 5
    let q : K[X] := (X - C r) ^ 9 + C B * (X - C r) ^ 8
    p.coeff 5 = 0 ∧ q.coeff 8 = 0 := by
  sorry

/-- Multiplying a Kummer radicand by a cube changes the generator but not
the generated coefficient field. -/
theorem GCD369CubeFactorNeutral {F L : Type*} [Field F] [Field L] [Algebra F L]
    (g : F) (hg : g ≠ 0) (t : L) :
    IntermediateField.adjoin F {(algebraMap F L g) * t} = F⟮t⟯ := by
  sorry

/-- The order-three Davenport--Stothers family is the nonlinear
constant-Wronskian bypass encountered by the normalized binary gate.  This
denominator-free parametrization uses `lam = 2 * mu` and records its two key
polynomial identities. -/
theorem GCD369DavenportStothersCertificate {K : Type*} [Field K] [CharZero K]
    (mu : K) :
    let f : K[X] :=
      X ^ 6 + C (8 * mu) * X ^ 4 + C (40 * mu ^ 2) * X ^ 2 + C (48 * mu ^ 3)
    let g : K[X] :=
      X ^ 9 + C (12 * mu) * X ^ 7 + C (84 * mu ^ 2) * X ^ 5
        + C (280 * mu ^ 3) * X ^ 3 + C (504 * mu ^ 4) * X
    2 * f * derivative g - 3 * derivative f * g = C (48384 * mu ^ 7)
      ∧ f ^ 3 - g ^ 2
        = C (864 * mu ^ 7)
            * (C 4 * X ^ 4 + C (26 * mu) * X ^ 2 + C (128 * mu ^ 2)) := by
  sorry

/-- The general differential identity linking a constant weighted Wronskian
to a Davenport--Stothers difference `H=f³-g²`. -/
theorem GCD369DavenportStothersDerivativeIdentity {K : Type*} [CommRing K]
    (f g : K[X]) :
    let H := f ^ 3 - g ^ 2
    f * derivative H - 3 * derivative f * H
      = -(2 * f * derivative g - 3 * derivative f * g) * g := by
  sorry
