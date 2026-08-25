/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch (direction), OpenAI Codex agent (formalization)
-/
import Mathlib

/-!
# Solution: the cubic-Kummer first gate at partial degrees `(6,9)`

The first three theorems formalize the load-bearing normalization used in the
maximum-partial-`y`-degree-eleven argument: exact cancellation of the top
Jacobian row, Kummer descent of its mismatch, and simultaneous depression.
The remaining theorems certify that polynomial cube factors do not create an
extra Kummer branch and record the explicit Davenport--Stothers bypass found
by the normalized binary calculation.
-/

open Polynomial
open scoped IntermediateField

theorem GCD369TopRowIdentity {k L : Type*} [CommRing k] [CommRing L] [Algebra k L]
    (D : Derivation k L L) (s A B : L) :
    8 * D (s ^ 6) * (s ^ 8 * B) + 9 * D (s ^ 5 * A) * s ^ 9
        - 6 * s ^ 6 * D (s ^ 8 * B) - 5 * (s ^ 5 * A) * D (s ^ 9)
      = s ^ 14 * (9 * D A - 6 * D B) := by
  simp only [D.leibniz, D.leibniz_pow, nsmul_eq_mul, smul_eq_mul]
  ring

theorem GCD369KummerAlignment {k L : Type*} [CommRing k] [CommRing L]
    [IsDomain L] [CharZero L] [Algebra k L] (D : Derivation k L L) (σ : L →ₐ[k] L)
    (s A B ω : L) (hs : s ≠ 0) (hω : ω ≠ 1)
    (hconstants : ∀ c : L, D c = 0 → σ c = c)
    (hA : σ A = ω * A) (hB : σ B = ω * B)
    (htop :
      8 * D (s ^ 6) * (s ^ 8 * B) + 9 * D (s ^ 5 * A) * s ^ 9
          - 6 * s ^ 6 * D (s ^ 8 * B) - 5 * (s ^ 5 * A) * D (s ^ 9) = 0) :
    3 * A - 2 * B = 0 := by
  have hrow : s ^ 14 * (9 * D A - 6 * D B) = 0 := by
    rw [← GCD369TopRowIdentity D s A B]
    exact htop
  have hdiff : D (3 * A - 2 * B) = 0 := by
    have hs14 : s ^ 14 ≠ 0 := pow_ne_zero _ hs
    have h : 9 * D A - 6 * D B = 0 :=
      (mul_eq_zero.mp hrow).resolve_left hs14
    have h3 : (3 : L) ≠ 0 := Nat.cast_ne_zero.mpr (by norm_num)
    have hbase : 3 * D A - 2 * D B = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left h3
      linear_combination h
    rw [map_sub, D.leibniz, D.leibniz]
    rw [show (3 : L) = (3 : Nat) from rfl, show (2 : L) = (2 : Nat) from rfl]
    rw [D.map_natCast, D.map_natCast]
    simpa [smul_eq_mul] using hbase
  have hfixed : σ (3 * A - 2 * B) = 3 * A - 2 * B := hconstants _ hdiff
  have hweight : σ (3 * A - 2 * B) = ω * (3 * A - 2 * B) := by
    simp only [map_sub, map_ofNat, map_mul, hA, hB]
    ring
  have hkill : (ω - 1) * (3 * A - 2 * B) = 0 := by
    rw [hfixed] at hweight
    calc
      (ω - 1) * (3 * A - 2 * B) = ω * (3 * A - 2 * B) - (3 * A - 2 * B) := by
        ring
      _ = 0 := sub_eq_zero.mpr hweight.symm
  exact (mul_eq_zero.mp hkill).resolve_left (sub_ne_zero.mpr hω)

theorem GCD369SimultaneousDepression {K : Type*} [Field K] [CharZero K]
    (A B : K) (halign : 3 * A - 2 * B = 0) :
    let r := A / 6
    let p : K[X] := (X - C r) ^ 6 + C A * (X - C r) ^ 5
    let q : K[X] := (X - C r) ^ 9 + C B * (X - C r) ^ 8
    p.coeff 5 = 0 ∧ q.coeff 8 = 0 := by
  dsimp
  constructor
  · rw [coeff_add, coeff_C_mul]
    simp only [sub_eq_add_neg, ← C_neg, coeff_X_add_C_pow]
    norm_num
  · rw [coeff_add, coeff_C_mul]
    simp only [sub_eq_add_neg, ← C_neg, coeff_X_add_C_pow]
    norm_num
    linear_combination (-1 / 2) * halign

theorem GCD369CubeFactorNeutral {F L : Type*} [Field F] [Field L] [Algebra F L]
    (g : F) (hg : g ≠ 0) (t : L) :
    IntermediateField.adjoin F {(algebraMap F L g) * t} = F⟮t⟯ := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact (F⟮t⟯).mul_mem ((F⟮t⟯).algebraMap_mem g)
      (IntermediateField.mem_adjoin_simple_self F t)
  · rw [IntermediateField.adjoin_le_iff]
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    have hgL : algebraMap F L g ≠ 0 := (map_ne_zero (algebraMap F L)).mpr hg
    have hinv : (algebraMap F L g)⁻¹ ∈
        IntermediateField.adjoin F {(algebraMap F L g) * t} :=
      (IntermediateField.adjoin F {(algebraMap F L g) * t}).inv_mem
        ((IntermediateField.adjoin F {(algebraMap F L g) * t}).algebraMap_mem g)
    have hprod : (algebraMap F L g) * t ∈
        IntermediateField.adjoin F {(algebraMap F L g) * t} :=
      IntermediateField.mem_adjoin_simple_self F _
    have heq : (algebraMap F L g)⁻¹ * ((algebraMap F L g) * t) = t := by
      field_simp
    have hmem :=
      (IntermediateField.adjoin F {(algebraMap F L g) * t}).mul_mem hinv hprod
    rw [heq] at hmem
    exact hmem

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
  dsimp
  constructor
  ·
    simp only [derivative_add, derivative_pow, derivative_X, derivative_C,
      derivative_mul, zero_mul, add_zero]
    simp only [C_mul, C_pow, C_ofNat, C_eq_natCast]
    ring
  ·
    simp only [C_mul, C_pow, C_ofNat]
    ring

theorem GCD369DavenportStothersDerivativeIdentity {K : Type*} [CommRing K]
    (f g : K[X]) :
    let H := f ^ 3 - g ^ 2
    f * derivative H - 3 * derivative f * H
      = -(2 * f * derivative g - 3 * derivative f * g) * g := by
  dsimp
  simp only [derivative_sub, derivative_pow, C_eq_natCast]
  ring

#print axioms GCD369TopRowIdentity
#print axioms GCD369KummerAlignment
#print axioms GCD369SimultaneousDepression
#print axioms GCD369CubeFactorNeutral
#print axioms GCD369DavenportStothersCertificate
#print axioms GCD369DavenportStothersDerivativeIdentity
