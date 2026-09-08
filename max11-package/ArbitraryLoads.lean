import CubeCore

open Polynomial

noncomputable section

universe u

/-! # Arbitrary early Faber loads

The source analysis produces a nonzero first load `T`; the normalized
certificates in `Solution` use `T = 1`.  This file makes that normalization
explicit.  Over an algebraically closed field we choose a weighted root
`lambda` with `lambda^k * T = 1`, rescale

`(u,v,X,Y,Z) -> (lambda^2 u, lambda^3 v, lambda^4 X,
  lambda^5 Y, lambda^6 Z)`,

and transport the normalized no-common-root certificate back to the original
common cubic and normal.
-/

/-- A nonzero load of positive weight has a nonzero weighted normalizer. -/
theorem GCD369CubeExistsWeightedNormalizer {K : Type*}
    [Field K] [IsAlgClosed K] (k : ℕ) (hk : 0 < k) (T : K) (hT : T ≠ 0) :
    ∃ lambda : K, lambda ≠ 0 ∧ lambda ^ k * T = 1 := by
  obtain ⟨lambda, hlambda⟩ :=
    IsAlgClosed.exists_pow_nat_eq (T⁻¹) hk
  have hinv : T⁻¹ ≠ 0 := inv_ne_zero hT
  have hlambda0 : lambda ≠ 0 := by
    intro hzero
    apply hinv
    rw [← hlambda, hzero, zero_pow (Nat.ne_of_gt hk)]
  refine ⟨lambda, hlambda0, ?_⟩
  rw [hlambda]
  exact inv_mul_cancel₀ hT

/-- Weighted scaling preserves failure of a common root. -/
theorem GCD369CubeNoCommonRootOfWeightedScale {K : Type*}
    [Field K] (lambda Xn Yn Zn u v : K)
    (hscaled : ∀ s : K,
      s ^ 3 + (lambda ^ 2 * u) * s + lambda ^ 3 * v = 0 →
      (lambda ^ 4 * Xn) * s ^ 2 + (lambda ^ 5 * Yn) * s +
        lambda ^ 6 * Zn = 0 → False) :
    ∀ r : K, r ^ 3 + u * r + v = 0 →
      Xn * r ^ 2 + Yn * r + Zn = 0 → False := by
  intro r hK hphi
  apply hscaled (lambda * r)
  · linear_combination lambda ^ 3 * hK
  · linear_combination lambda ^ 6 * hphi

/-- A nonzero weighted scaling preserves the projective common-cubic point. -/
theorem GCD369CubeProjectiveOfWeightedScale {K : Type*} [Field K]
    (lambda u v : K) (hlambda : lambda ≠ 0) (hprojective : u ≠ 0 ∨ v ≠ 0) :
    lambda ^ 2 * u ≠ 0 ∨ lambda ^ 3 * v ≠ 0 := by
  rcases hprojective with hu | hv
  · exact Or.inl (mul_ne_zero (pow_ne_zero 2 hlambda) hu)
  · exact Or.inr (mul_ne_zero (pow_ne_zero 3 hlambda) hv)

/-- Exact source-facing `d = T h^2` Faber equations before normalizing `T`. -/
def GCD369CubeDLeadingFaberRowsAt {K : Type*} [Field K]
    (Xn Yn Zn u v T : K) : Prop :=
  let H : K[X] := X
  let A0 : K[X] := C (v ^ 2) + C Zn * H
  let A1 : K[X] := C (2 * u * v) + C Yn * H
  let A2 : K[X] := C (u ^ 2) + C Xn * H
  let A3 : K[X] := C (2 * v)
  let A4 : K[X] := C (2 * u)
  (GCD369CubeFaberD1 A0 A1 A2 A3 A4 (C T * H ^ 2)).coeff 2 = 0 ∧
  (GCD369CubeFaberD2 A0 A1 A2 A3 A4 (C T * H ^ 2)).coeff 2 = 0 ∧
  (GCD369CubeFaberD3 A0 A1 A2 A3 A4 (C T * H ^ 2)).coeff 2 = 0 ∧
  (GCD369CubeFaberD4 A0 A1 A2 A3 A4 (C T * H ^ 2)).coeff 2 = 0

/-- The unnormalized exceptional `d` rows derived from the exact Faber
coefficients. -/
def GCD369CubeDExceptionalRowsAt {K : Type*} [Field K]
    (Xn Yn Zn u v T : K) : Prop :=
  (u ≠ 0 ∨ v ≠ 0) ∧
  GCD369CubeNormalRow1 Xn Yn Zn u +
      320 * T * u ^ 3 * v - 960 * T * v ^ 3 = 0 ∧
  GCD369CubeNormalRow2 Xn Yn Zn u v +
      64 * T * u ^ 5 - 1440 * T * u ^ 2 * v ^ 2 = 0 ∧
  GCD369CubeNormalRow3 Xn Yn Zn u v = 0 ∧
  GCD369CubeNormalRow4 Xn Yn Zn u v +
      160 * T * u ^ 6 - 5760 * T * u ^ 3 * v ^ 2 +
      6480 * T * v ^ 4 = 0

/-- Exact arbitrary-`T` Faber coefficients force the arbitrary-`T` `d`
Kuranishi rows. -/
theorem GCD369CubeDExceptionalRowsAt_of_faber
    {K : Type*} [Field K] [CharZero K]
    {Xn Yn Zn u v T : K} (hprojective : u ≠ 0 ∨ v ≠ 0)
    (hfaber : GCD369CubeDLeadingFaberRowsAt Xn Yn Zn u v T) :
    GCD369CubeDExceptionalRowsAt Xn Yn Zn u v T := by
  dsimp [GCD369CubeDLeadingFaberRowsAt] at hfaber
  have hcoeff := GCD369CubeFaberDNormalCoefficients Xn Yn Zn u v T
  dsimp at hcoeff
  rcases hfaber with ⟨hf1, hf2, hf3, hf4⟩
  rcases hcoeff with ⟨hc1, hc2, hc3, hc4⟩
  rw [hc1] at hf1
  rw [hc2] at hf2
  rw [hc3] at hf3
  rw [hc4] at hf4
  refine ⟨hprojective, ?_, ?_, ?_, ?_⟩
  · exact (mul_eq_zero.mp hf1).resolve_left (by norm_num)
  · exact (mul_eq_zero.mp hf2).resolve_left (by norm_num)
  · exact (mul_eq_zero.mp hf3).resolve_left (by norm_num)
  · exact (mul_eq_zero.mp hf4).resolve_left (by norm_num)

/-- Normalize arbitrary nonzero `d` rows by the weight-one scaling. -/
theorem GCD369CubeDExceptionalRowsAt_normalize
    {K : Type*} [Field K] [IsAlgClosed K]
    {Xn Yn Zn u v T : K} (hT : T ≠ 0)
    (hrows : GCD369CubeDExceptionalRowsAt Xn Yn Zn u v T) :
    ∃ lambda : K, lambda ≠ 0 ∧ lambda * T = 1 ∧
      GCD369CubeDExceptionalRows
        (lambda ^ 4 * Xn) (lambda ^ 5 * Yn) (lambda ^ 6 * Zn)
        (lambda ^ 2 * u) (lambda ^ 3 * v) := by
  obtain ⟨lambda, hlambda, hscale⟩ :=
    GCD369CubeExistsWeightedNormalizer 1 (by norm_num) T hT
  simp only [pow_one] at hscale
  rcases hrows with ⟨hprojective, h1, h2, h3, h4⟩
  refine ⟨lambda, hlambda, hscale, ?_⟩
  dsimp [GCD369CubeDExceptionalRows]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases hprojective with hu | hv
    · exact Or.inl (mul_ne_zero (pow_ne_zero 2 hlambda) hu)
    · exact Or.inr (mul_ne_zero (pow_ne_zero 3 hlambda) hv)
  · calc
      729 * (lambda ^ 2 * u) * (lambda ^ 4 * Xn) ^ 2 -
          1458 * (lambda ^ 4 * Xn) * (lambda ^ 6 * Zn) -
          729 * (lambda ^ 5 * Yn) ^ 2 +
          320 * (lambda ^ 2 * u) ^ 3 * (lambda ^ 3 * v) -
          960 * (lambda ^ 3 * v) ^ 3 =
          lambda ^ 10 * (GCD369CubeNormalRow1 Xn Yn Zn u +
            320 * T * u ^ 3 * v - 960 * T * v ^ 3) := by
              rw [GCD369CubeNormalRow1]
              linear_combination
                (-(lambda ^ 9 * (320 * u ^ 3 * v - 960 * v ^ 3))) * hscale
      _ = 0 := by rw [h1, mul_zero]
  · calc
      -2187 * (lambda ^ 3 * v) * (lambda ^ 4 * Xn) ^ 2 -
          4374 * (lambda ^ 2 * u) * (lambda ^ 4 * Xn) *
            (lambda ^ 5 * Yn) +
          4374 * (lambda ^ 5 * Yn) * (lambda ^ 6 * Zn) +
          64 * (lambda ^ 2 * u) ^ 5 -
          1440 * (lambda ^ 2 * u) ^ 2 * (lambda ^ 3 * v) ^ 2 =
          lambda ^ 11 * (GCD369CubeNormalRow2 Xn Yn Zn u v +
            64 * T * u ^ 5 - 1440 * T * u ^ 2 * v ^ 2) := by
              rw [GCD369CubeNormalRow2]
              linear_combination
                (-(lambda ^ 10 * (64 * u ^ 5 - 1440 * u ^ 2 * v ^ 2))) *
                  hscale
      _ = 0 := by rw [h2, mul_zero]
  · calc
      2 * (lambda ^ 2 * u) ^ 2 * (lambda ^ 4 * Xn) ^ 2 -
          6 * (lambda ^ 3 * v) * (lambda ^ 4 * Xn) *
            (lambda ^ 5 * Yn) -
          4 * (lambda ^ 2 * u) * (lambda ^ 4 * Xn) *
            (lambda ^ 6 * Zn) -
          2 * (lambda ^ 2 * u) * (lambda ^ 5 * Yn) ^ 2 +
          3 * (lambda ^ 6 * Zn) ^ 2 =
          lambda ^ 12 * GCD369CubeNormalRow3 Xn Yn Zn u v := by
              rw [GCD369CubeNormalRow3]
              ring
      _ = 0 := by rw [h3, mul_zero]
  · calc
      19683 * (lambda ^ 2 * u) * (lambda ^ 3 * v) *
            (lambda ^ 4 * Xn) ^ 2 +
          13122 * (lambda ^ 2 * u) ^ 2 * (lambda ^ 4 * Xn) *
            (lambda ^ 5 * Yn) -
          26244 * (lambda ^ 3 * v) * (lambda ^ 4 * Xn) *
            (lambda ^ 6 * Zn) -
          13122 * (lambda ^ 3 * v) * (lambda ^ 5 * Yn) ^ 2 -
          13122 * (lambda ^ 2 * u) * (lambda ^ 5 * Yn) *
            (lambda ^ 6 * Zn) +
          160 * (lambda ^ 2 * u) ^ 6 -
          5760 * (lambda ^ 2 * u) ^ 3 * (lambda ^ 3 * v) ^ 2 +
          6480 * (lambda ^ 3 * v) ^ 4 =
          lambda ^ 13 * (GCD369CubeNormalRow4 Xn Yn Zn u v +
            160 * T * u ^ 6 - 5760 * T * u ^ 3 * v ^ 2 +
            6480 * T * v ^ 4) := by
              rw [GCD369CubeNormalRow4]
              linear_combination
                (-(lambda ^ 12 * (160 * u ^ 6 - 5760 * u ^ 3 * v ^ 2 +
                  6480 * v ^ 4))) * hscale
      _ = 0 := by rw [h4, mul_zero]

/-- Arbitrary nonzero first `d` load already forbids a common root; the
normalization scalar is not exposed downstream. -/
theorem GCD369CubeDLeadingFaberRowsAt_noCommonRoot
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (Xn Yn Zn u v T : K) (hT : T ≠ 0)
    (hprojective : u ≠ 0 ∨ v ≠ 0)
    (hfaber : GCD369CubeDLeadingFaberRowsAt Xn Yn Zn u v T) :
    ∀ r : K, r ^ 3 + u * r + v = 0 →
      Xn * r ^ 2 + Yn * r + Zn = 0 → False := by
  have hrows := GCD369CubeDExceptionalRowsAt_of_faber hprojective hfaber
  obtain ⟨lambda, hlambda, _hscale, hnormalized⟩ :=
    GCD369CubeDExceptionalRowsAt_normalize hT hrows
  apply GCD369CubeNoCommonRootOfWeightedScale lambda Xn Yn Zn u v
  exact (GCD369CubeEarlyLoadRows.d hnormalized).noCommonRoot

/-! ## The remaining arbitrary source-facing loads -/

/-- Exact source-facing `c7 = T h^2` Faber equations. -/
def GCD369CubeC7LeadingFaberRowsAt {K : Type*} [Field K]
    (Xn Yn Zn u v T : K) : Prop :=
  let H : K[X] := X
  let A0 : K[X] := C (v ^ 2) + C Zn * H
  let A1 : K[X] := C (2 * u * v) + C Yn * H
  let A2 : K[X] := C (u ^ 2) + C Xn * H
  let A3 : K[X] := C (2 * v)
  let A4 : K[X] := C (2 * u)
  (GCD369CubeFaberC7N1 A0 A1 A2 A3 A4 (C T * H ^ 2)).coeff 2 = 0 ∧
  (GCD369CubeFaberC7N2 A0 A1 A2 A3 A4 (C T * H ^ 2)).coeff 2 = 0 ∧
  (GCD369CubeFaberC7N3 A0 A1 A2 A3 A4 (C T * H ^ 2)).coeff 2 = 0 ∧
  (GCD369CubeFaberC7N4 A0 A1 A2 A3 A4 (C T * H ^ 2)).coeff 2 = 0

/-- Exact source-facing `c5 = T h^2` Faber equations. -/
def GCD369CubeC5LeadingFaberRowsAt {K : Type*} [Field K]
    (Xn Yn Zn u v T : K) : Prop :=
  let H : K[X] := X
  let A0 : K[X] := C (v ^ 2) + C Zn * H
  let A1 : K[X] := C (2 * u * v) + C Yn * H
  let A2 : K[X] := C (u ^ 2) + C Xn * H
  let A3 : K[X] := C (2 * v)
  let A4 : K[X] := C (2 * u)
  (GCD369CubeFaberC5N1 A0 A1 A2 A3 A4 (C T * H ^ 2)).coeff 2 = 0 ∧
  (GCD369CubeFaberC5N2 A0 A1 A2 A3 A4 (C T * H ^ 2)).coeff 2 = 0 ∧
  (GCD369CubeFaberC5N3 A0 A1 A2 A3 A4 (C T * H ^ 2)).coeff 2 = 0 ∧
  (GCD369CubeFaberC5N4 A0 A1 A2 A3 A4 (C T * H ^ 2)).coeff 2 = 0

/-- Exact source-facing `c4 = T h^2` Faber equations. -/
def GCD369CubeC4LeadingFaberRowsAt {K : Type*} [Field K]
    (Xn Yn Zn u v T : K) : Prop :=
  let H : K[X] := X
  let A0 : K[X] := C (v ^ 2) + C Zn * H
  let A1 : K[X] := C (2 * u * v) + C Yn * H
  let A2 : K[X] := C (u ^ 2) + C Xn * H
  let A3 : K[X] := C (2 * v)
  let A4 : K[X] := C (2 * u)
  (GCD369CubeFaberC4N1 A0 A1 A2 A3 A4 (C T * H ^ 2)).coeff 2 = 0 ∧
  (GCD369CubeFaberC4N2 A0 A1 A2 A3 A4 (C T * H ^ 2)).coeff 2 = 0 ∧
  (GCD369CubeFaberC4N3 A0 A1 A2 A3 A4 (C T * H ^ 2)).coeff 2 = 0 ∧
  (GCD369CubeFaberC4N4 A0 A1 A2 A3 A4 (C T * H ^ 2)).coeff 2 = 0

/-- Exact source-facing `c2 = T h^2` Faber equations. -/
def GCD369CubeC2LeadingFaberRowsAt {K : Type*} [Field K]
    (Xn Yn Zn u v T : K) : Prop :=
  let H : K[X] := X
  let A0 : K[X] := C (v ^ 2) + C Zn * H
  let A1 : K[X] := C (2 * u * v) + C Yn * H
  let A2 : K[X] := C (u ^ 2) + C Xn * H
  let A3 : K[X] := C (2 * v)
  let A4 : K[X] := C (2 * u)
  (GCD369CubeFaberC2N1 A0 A1 A2 A3 A4 (C T * H ^ 2)).coeff 2 = 0 ∧
  (GCD369CubeFaberC2N2 A0 A1 A2 A3 A4 (C T * H ^ 2)).coeff 2 = 0 ∧
  (GCD369CubeFaberC2N3 A0 A1 A2 A3 A4 (C T * H ^ 2)).coeff 2 = 0 ∧
  (GCD369CubeFaberC2N4 A0 A1 A2 A3 A4 (C T * H ^ 2)).coeff 2 = 0

/-- Exact source-facing `c1 = T h^2` Faber equations. -/
def GCD369CubeC1LeadingFaberRowsAt {K : Type*} [Field K]
    (Xn Yn Zn u v T : K) : Prop :=
  let H : K[X] := X
  let A0 : K[X] := C (v ^ 2) + C Zn * H
  let A1 : K[X] := C (2 * u * v) + C Yn * H
  let A2 : K[X] := C (u ^ 2) + C Xn * H
  let A3 : K[X] := C (2 * v)
  let A4 : K[X] := C (2 * u)
  (GCD369CubeFaberC1N1 A0 A1 A2 A3 A4 (C T * H ^ 2)).coeff 2 = 0 ∧
  (GCD369CubeFaberC1N2 A0 A1 A2 A3 A4 (C T * H ^ 2)).coeff 2 = 0 ∧
  (GCD369CubeFaberC1N3 A0 A1 A2 A3 A4 (C T * H ^ 2)).coeff 2 = 0 ∧
  (GCD369CubeFaberC1N4 A0 A1 A2 A3 A4 (C T * H ^ 2)).coeff 2 = 0

/-- Exact source-facing first `rho1 = T` target load. -/
def GCD369CubeRhoOneLeadingFaberRowsAt {K : Type*} [Field K]
    (Xn Yn Zn u v T : K) : Prop :=
  let H : K[X] := X
  let A0 : K[X] := C (v ^ 2) + C Zn * H
  let A1 : K[X] := C (2 * u * v) + C Yn * H
  let A2 : K[X] := C (u ^ 2) + C Xn * H
  let A3 : K[X] := C (2 * v)
  let A4 : K[X] := C (2 * u)
  (729 * GCD369CubeFaberN1 A0 A1 A2 A3 A4).coeff 2 = 62208 * T ∧
  (2187 * GCD369CubeFaberN2 A0 A1 A2 A3 A4).coeff 2 = 0 ∧
  (GCD369CubeFaberN3 A0 A1 A2 A3 A4).coeff 2 = 0 ∧
  (6561 * GCD369CubeFaberN4 A0 A1 A2 A3 A4).coeff 2 = 0

/-- Exact source-facing first `rho2 = T` target load. -/
def GCD369CubeRhoTwoLeadingFaberRowsAt {K : Type*} [Field K]
    (Xn Yn Zn u v T : K) : Prop :=
  let H : K[X] := X
  let A0 : K[X] := C (v ^ 2) + C Zn * H
  let A1 : K[X] := C (2 * u * v) + C Yn * H
  let A2 : K[X] := C (u ^ 2) + C Xn * H
  let A3 : K[X] := C (2 * v)
  let A4 : K[X] := C (2 * u)
  (729 * GCD369CubeFaberN1 A0 A1 A2 A3 A4).coeff 2 = 0 ∧
  (2187 * GCD369CubeFaberN2 A0 A1 A2 A3 A4).coeff 2 = 186624 * T ∧
  (GCD369CubeFaberN3 A0 A1 A2 A3 A4).coeff 2 = 0 ∧
  (6561 * GCD369CubeFaberN4 A0 A1 A2 A3 A4).coeff 2 = 0

/-- An arbitrary nonzero first `c7` load forbids a common root. -/
theorem GCD369CubeC7LeadingFaberRowsAt_noCommonRoot
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (Xn Yn Zn u v T : K) (hT : T ≠ 0)
    (hprojective : u ≠ 0 ∨ v ≠ 0)
    (hfaber : GCD369CubeC7LeadingFaberRowsAt Xn Yn Zn u v T) :
    ∀ r : K, r ^ 3 + u * r + v = 0 →
      Xn * r ^ 2 + Yn * r + Zn = 0 → False := by
  dsimp [GCD369CubeC7LeadingFaberRowsAt] at hfaber
  have hcoeff := GCD369CubeFaberC7NormalCoefficients Xn Yn Zn u v T
  dsimp at hcoeff
  rcases hfaber with ⟨hf1, hf2, hf3, hf4⟩
  rcases hcoeff with ⟨hc1, hc2, hc3, hc4⟩
  rw [hc1] at hf1
  rw [hc2] at hf2
  rw [hc3] at hf3
  rw [hc4] at hf4
  have h1 :
      56 * T * u ^ 4 - 1008 * T * u * v ^ 2 +
        GCD369CubeNormalRow1 Xn Yn Zn u = 0 :=
    (mul_eq_zero.mp hf1).resolve_left (by norm_num)
  have h2 :
      224 * T * u ^ 3 * v - 336 * T * v ^ 3 + 729 * v * Xn ^ 2 +
        1458 * u * Xn * Yn - 1458 * Yn * Zn = 0 :=
    (mul_eq_zero.mp hf2).resolve_left (by norm_num)
  have h3 : GCD369CubeNormalRow3 Xn Yn Zn u v = 0 :=
    (mul_eq_zero.mp hf3).resolve_left (by norm_num)
  have h4 :
      224 * T * u ^ 4 * v - 1008 * T * u * v ^ 3 -
        2187 * u * v * Xn ^ 2 - 1458 * u ^ 2 * Xn * Yn +
        2916 * v * Xn * Zn + 1458 * v * Yn ^ 2 +
        1458 * u * Yn * Zn = 0 :=
    (mul_eq_zero.mp hf4).resolve_left (by norm_num)
  obtain ⟨lambda, hlambda, hscale⟩ :=
    GCD369CubeExistsWeightedNormalizer 2 (by norm_num) T hT
  apply GCD369CubeNoCommonRootOfWeightedScale lambda Xn Yn Zn u v
  apply GCD369CubeC7NoCommonRoot
    (lambda ^ 4 * Xn) (lambda ^ 5 * Yn) (lambda ^ 6 * Zn)
    (lambda ^ 2 * u) (lambda ^ 3 * v)
    (GCD369CubeProjectiveOfWeightedScale lambda u v hlambda hprojective)
  · calc
      56 * (lambda ^ 2 * u) ^ 4 -
          1008 * (lambda ^ 2 * u) * (lambda ^ 3 * v) ^ 2 +
          729 * (lambda ^ 2 * u) * (lambda ^ 4 * Xn) ^ 2 -
          1458 * (lambda ^ 4 * Xn) * (lambda ^ 6 * Zn) -
          729 * (lambda ^ 5 * Yn) ^ 2 =
          lambda ^ 10 * (56 * T * u ^ 4 - 1008 * T * u * v ^ 2 +
            GCD369CubeNormalRow1 Xn Yn Zn u) := by
              rw [GCD369CubeNormalRow1]
              linear_combination
                (-(lambda ^ 8 * (56 * u ^ 4 - 1008 * u * v ^ 2))) * hscale
      _ = 0 := by rw [h1, mul_zero]
  · calc
      224 * (lambda ^ 2 * u) ^ 3 * (lambda ^ 3 * v) -
          336 * (lambda ^ 3 * v) ^ 3 +
          729 * (lambda ^ 3 * v) * (lambda ^ 4 * Xn) ^ 2 +
          1458 * (lambda ^ 2 * u) * (lambda ^ 4 * Xn) *
            (lambda ^ 5 * Yn) -
          1458 * (lambda ^ 5 * Yn) * (lambda ^ 6 * Zn) =
          lambda ^ 11 * (224 * T * u ^ 3 * v - 336 * T * v ^ 3 +
            729 * v * Xn ^ 2 + 1458 * u * Xn * Yn - 1458 * Yn * Zn) := by
              linear_combination
                (-(lambda ^ 9 * (224 * u ^ 3 * v - 336 * v ^ 3))) * hscale
      _ = 0 := by rw [h2, mul_zero]
  · calc
      2 * (lambda ^ 2 * u) ^ 2 * (lambda ^ 4 * Xn) ^ 2 -
          6 * (lambda ^ 3 * v) * (lambda ^ 4 * Xn) *
            (lambda ^ 5 * Yn) -
          4 * (lambda ^ 2 * u) * (lambda ^ 4 * Xn) *
            (lambda ^ 6 * Zn) -
          2 * (lambda ^ 2 * u) * (lambda ^ 5 * Yn) ^ 2 +
          3 * (lambda ^ 6 * Zn) ^ 2 =
          lambda ^ 12 * GCD369CubeNormalRow3 Xn Yn Zn u v := by
              rw [GCD369CubeNormalRow3]
              ring
      _ = 0 := by rw [h3, mul_zero]
  · calc
      224 * (lambda ^ 2 * u) ^ 4 * (lambda ^ 3 * v) -
          1008 * (lambda ^ 2 * u) * (lambda ^ 3 * v) ^ 3 -
          2187 * (lambda ^ 2 * u) * (lambda ^ 3 * v) *
            (lambda ^ 4 * Xn) ^ 2 -
          1458 * (lambda ^ 2 * u) ^ 2 * (lambda ^ 4 * Xn) *
            (lambda ^ 5 * Yn) +
          2916 * (lambda ^ 3 * v) * (lambda ^ 4 * Xn) *
            (lambda ^ 6 * Zn) +
          1458 * (lambda ^ 3 * v) * (lambda ^ 5 * Yn) ^ 2 +
          1458 * (lambda ^ 2 * u) * (lambda ^ 5 * Yn) *
            (lambda ^ 6 * Zn) =
          lambda ^ 13 * (224 * T * u ^ 4 * v - 1008 * T * u * v ^ 3 -
            2187 * u * v * Xn ^ 2 - 1458 * u ^ 2 * Xn * Yn +
            2916 * v * Xn * Zn + 1458 * v * Yn ^ 2 +
            1458 * u * Yn * Zn) := by
              linear_combination
                (-(lambda ^ 11 * (224 * u ^ 4 * v - 1008 * u * v ^ 3))) *
                  hscale
      _ = 0 := by rw [h4, mul_zero]

/-- An arbitrary nonzero first `c5` load forbids a common root. -/
theorem GCD369CubeC5LeadingFaberRowsAt_noCommonRoot
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (Xn Yn Zn u v T : K) (hT : T ≠ 0)
    (hprojective : u ≠ 0 ∨ v ≠ 0)
    (hfaber : GCD369CubeC5LeadingFaberRowsAt Xn Yn Zn u v T) :
    ∀ r : K, r ^ 3 + u * r + v = 0 →
      Xn * r ^ 2 + Yn * r + Zn = 0 → False := by
  dsimp [GCD369CubeC5LeadingFaberRowsAt] at hfaber
  have hcoeff := GCD369CubeFaberC5NormalCoefficients Xn Yn Zn u v T
  dsimp at hcoeff
  rcases hfaber with ⟨hf1, hf2, hf3, hf4⟩
  rcases hcoeff with ⟨hc1, hc2, hc3, hc4⟩
  rw [hc1] at hf1
  rw [hc2] at hf2
  rw [hc3] at hf3
  rw [hc4] at hf4
  have h1 :
      40 * T * u ^ 3 - 360 * T * v ^ 2 + 243 * u * Xn ^ 2 -
        486 * Xn * Zn - 243 * Yn ^ 2 = 0 :=
    (mul_eq_zero.mp hf1).resolve_left (by norm_num)
  have h2 :
      40 * T * u ^ 2 * v + 81 * v * Xn ^ 2 + 162 * u * Xn * Yn -
        162 * Yn * Zn = 0 :=
    (mul_eq_zero.mp hf2).resolve_left (by norm_num)
  have h3 : GCD369CubeNormalRow3 Xn Yn Zn u v = 0 :=
    (mul_eq_zero.mp hf3).resolve_left (by norm_num)
  have h4 :
      40 * T * u ^ 3 * v - 80 * T * v ^ 3 - 243 * u * v * Xn ^ 2 -
        162 * u ^ 2 * Xn * Yn + 324 * v * Xn * Zn +
        162 * v * Yn ^ 2 + 162 * u * Yn * Zn = 0 :=
    (mul_eq_zero.mp hf4).resolve_left (by norm_num)
  obtain ⟨lambda, hlambda, hscale⟩ :=
    GCD369CubeExistsWeightedNormalizer 4 (by norm_num) T hT
  apply GCD369CubeNoCommonRootOfWeightedScale lambda Xn Yn Zn u v
  apply GCD369CubeC5NoCommonRoot
    (lambda ^ 4 * Xn) (lambda ^ 5 * Yn) (lambda ^ 6 * Zn)
    (lambda ^ 2 * u) (lambda ^ 3 * v)
    (GCD369CubeProjectiveOfWeightedScale lambda u v hlambda hprojective)
  · calc
      40 * (lambda ^ 2 * u) ^ 3 - 360 * (lambda ^ 3 * v) ^ 2 +
          243 * (lambda ^ 2 * u) * (lambda ^ 4 * Xn) ^ 2 -
          486 * (lambda ^ 4 * Xn) * (lambda ^ 6 * Zn) -
          243 * (lambda ^ 5 * Yn) ^ 2 =
          lambda ^ 10 * (40 * T * u ^ 3 - 360 * T * v ^ 2 +
            243 * u * Xn ^ 2 - 486 * Xn * Zn - 243 * Yn ^ 2) := by
              linear_combination
                (-(lambda ^ 6 * (40 * u ^ 3 - 360 * v ^ 2))) * hscale
      _ = 0 := by rw [h1, mul_zero]
  · calc
      40 * (lambda ^ 2 * u) ^ 2 * (lambda ^ 3 * v) +
          81 * (lambda ^ 3 * v) * (lambda ^ 4 * Xn) ^ 2 +
          162 * (lambda ^ 2 * u) * (lambda ^ 4 * Xn) *
            (lambda ^ 5 * Yn) -
          162 * (lambda ^ 5 * Yn) * (lambda ^ 6 * Zn) =
          lambda ^ 11 * (40 * T * u ^ 2 * v + 81 * v * Xn ^ 2 +
            162 * u * Xn * Yn - 162 * Yn * Zn) := by
              linear_combination (-(lambda ^ 7 * (40 * u ^ 2 * v))) * hscale
      _ = 0 := by rw [h2, mul_zero]
  · calc
      2 * (lambda ^ 2 * u) ^ 2 * (lambda ^ 4 * Xn) ^ 2 -
          6 * (lambda ^ 3 * v) * (lambda ^ 4 * Xn) *
            (lambda ^ 5 * Yn) -
          4 * (lambda ^ 2 * u) * (lambda ^ 4 * Xn) *
            (lambda ^ 6 * Zn) -
          2 * (lambda ^ 2 * u) * (lambda ^ 5 * Yn) ^ 2 +
          3 * (lambda ^ 6 * Zn) ^ 2 =
          lambda ^ 12 * GCD369CubeNormalRow3 Xn Yn Zn u v := by
              rw [GCD369CubeNormalRow3]
              ring
      _ = 0 := by rw [h3, mul_zero]
  · calc
      40 * (lambda ^ 2 * u) ^ 3 * (lambda ^ 3 * v) -
          80 * (lambda ^ 3 * v) ^ 3 -
          243 * (lambda ^ 2 * u) * (lambda ^ 3 * v) *
            (lambda ^ 4 * Xn) ^ 2 -
          162 * (lambda ^ 2 * u) ^ 2 * (lambda ^ 4 * Xn) *
            (lambda ^ 5 * Yn) +
          324 * (lambda ^ 3 * v) * (lambda ^ 4 * Xn) *
            (lambda ^ 6 * Zn) +
          162 * (lambda ^ 3 * v) * (lambda ^ 5 * Yn) ^ 2 +
          162 * (lambda ^ 2 * u) * (lambda ^ 5 * Yn) *
            (lambda ^ 6 * Zn) =
          lambda ^ 13 * (40 * T * u ^ 3 * v - 80 * T * v ^ 3 -
            243 * u * v * Xn ^ 2 - 162 * u ^ 2 * Xn * Yn +
            324 * v * Xn * Zn + 162 * v * Yn ^ 2 + 162 * u * Yn * Zn) := by
              linear_combination
                (-(lambda ^ 9 * (40 * u ^ 3 * v - 80 * v ^ 3))) * hscale
      _ = 0 := by rw [h4, mul_zero]

/-- An arbitrary nonzero first `c4` load forbids a common root. -/
theorem GCD369CubeC4LeadingFaberRowsAt_noCommonRoot
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (Xn Yn Zn u v T : K) (hT : T ≠ 0)
    (hprojective : u ≠ 0 ∨ v ≠ 0)
    (hfaber : GCD369CubeC4LeadingFaberRowsAt Xn Yn Zn u v T) :
    ∀ r : K, r ^ 3 + u * r + v = 0 →
      Xn * r ^ 2 + Yn * r + Zn = 0 → False := by
  dsimp [GCD369CubeC4LeadingFaberRowsAt] at hfaber
  have hcoeff := GCD369CubeFaberC4NormalCoefficients Xn Yn Zn u v T
  dsimp at hcoeff
  rcases hfaber with ⟨hf1, hf2, hf3, hf4⟩
  rcases hcoeff with ⟨hc1, hc2, hc3, hc4⟩
  rw [hc1] at hf1
  rw [hc2] at hf2
  rw [hc3] at hf3
  rw [hc4] at hf4
  have h1 :
      32 * T * u * v - 27 * u * Xn ^ 2 + 54 * Xn * Zn +
        27 * Yn ^ 2 = 0 :=
    (mul_eq_zero.mp hf1).resolve_left (by norm_num)
  have h2 :
      32 * T * u ^ 3 - 144 * T * v ^ 2 + 243 * v * Xn ^ 2 +
        486 * u * Xn * Yn - 486 * Yn * Zn = 0 :=
    (mul_eq_zero.mp hf2).resolve_left (by norm_num)
  have h3 : GCD369CubeNormalRow3 Xn Yn Zn u v = 0 :=
    (mul_eq_zero.mp hf3).resolve_left (by norm_num)
  have h4 :
      8 * T * u ^ 4 - 96 * T * u * v ^ 2 - 243 * u * v * Xn ^ 2 -
        162 * u ^ 2 * Xn * Yn + 324 * v * Xn * Zn +
        162 * v * Yn ^ 2 + 162 * u * Yn * Zn = 0 :=
    (mul_eq_zero.mp hf4).resolve_left (by norm_num)
  obtain ⟨lambda, hlambda, hscale⟩ :=
    GCD369CubeExistsWeightedNormalizer 5 (by norm_num) T hT
  apply GCD369CubeNoCommonRootOfWeightedScale lambda Xn Yn Zn u v
  apply GCD369CubeC4NoCommonRoot
    (lambda ^ 4 * Xn) (lambda ^ 5 * Yn) (lambda ^ 6 * Zn)
    (lambda ^ 2 * u) (lambda ^ 3 * v)
    (GCD369CubeProjectiveOfWeightedScale lambda u v hlambda hprojective)
  · calc
      32 * (lambda ^ 2 * u) * (lambda ^ 3 * v) -
          27 * (lambda ^ 2 * u) * (lambda ^ 4 * Xn) ^ 2 +
          54 * (lambda ^ 4 * Xn) * (lambda ^ 6 * Zn) +
          27 * (lambda ^ 5 * Yn) ^ 2 =
          lambda ^ 10 * (32 * T * u * v - 27 * u * Xn ^ 2 +
            54 * Xn * Zn + 27 * Yn ^ 2) := by
              linear_combination (-(lambda ^ 5 * (32 * u * v))) * hscale
      _ = 0 := by rw [h1, mul_zero]
  · calc
      32 * (lambda ^ 2 * u) ^ 3 - 144 * (lambda ^ 3 * v) ^ 2 +
          243 * (lambda ^ 3 * v) * (lambda ^ 4 * Xn) ^ 2 +
          486 * (lambda ^ 2 * u) * (lambda ^ 4 * Xn) *
            (lambda ^ 5 * Yn) -
          486 * (lambda ^ 5 * Yn) * (lambda ^ 6 * Zn) =
          lambda ^ 11 * (32 * T * u ^ 3 - 144 * T * v ^ 2 +
            243 * v * Xn ^ 2 + 486 * u * Xn * Yn - 486 * Yn * Zn) := by
              linear_combination
                (-(lambda ^ 6 * (32 * u ^ 3 - 144 * v ^ 2))) * hscale
      _ = 0 := by rw [h2, mul_zero]
  · calc
      2 * (lambda ^ 2 * u) ^ 2 * (lambda ^ 4 * Xn) ^ 2 -
          6 * (lambda ^ 3 * v) * (lambda ^ 4 * Xn) *
            (lambda ^ 5 * Yn) -
          4 * (lambda ^ 2 * u) * (lambda ^ 4 * Xn) *
            (lambda ^ 6 * Zn) -
          2 * (lambda ^ 2 * u) * (lambda ^ 5 * Yn) ^ 2 +
          3 * (lambda ^ 6 * Zn) ^ 2 =
          lambda ^ 12 * GCD369CubeNormalRow3 Xn Yn Zn u v := by
              rw [GCD369CubeNormalRow3]
              ring
      _ = 0 := by rw [h3, mul_zero]
  · calc
      8 * (lambda ^ 2 * u) ^ 4 -
          96 * (lambda ^ 2 * u) * (lambda ^ 3 * v) ^ 2 -
          243 * (lambda ^ 2 * u) * (lambda ^ 3 * v) *
            (lambda ^ 4 * Xn) ^ 2 -
          162 * (lambda ^ 2 * u) ^ 2 * (lambda ^ 4 * Xn) *
            (lambda ^ 5 * Yn) +
          324 * (lambda ^ 3 * v) * (lambda ^ 4 * Xn) *
            (lambda ^ 6 * Zn) +
          162 * (lambda ^ 3 * v) * (lambda ^ 5 * Yn) ^ 2 +
          162 * (lambda ^ 2 * u) * (lambda ^ 5 * Yn) *
            (lambda ^ 6 * Zn) =
          lambda ^ 13 * (8 * T * u ^ 4 - 96 * T * u * v ^ 2 -
            243 * u * v * Xn ^ 2 - 162 * u ^ 2 * Xn * Yn +
            324 * v * Xn * Zn + 162 * v * Yn ^ 2 + 162 * u * Yn * Zn) := by
              linear_combination
                (-(lambda ^ 8 * (8 * u ^ 4 - 96 * u * v ^ 2))) * hscale
      _ = 0 := by rw [h4, mul_zero]

/-- An arbitrary nonzero first `c2` load forbids a common root. -/
theorem GCD369CubeC2LeadingFaberRowsAt_noCommonRoot
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (Xn Yn Zn u v T : K) (hT : T ≠ 0)
    (hprojective : u ≠ 0 ∨ v ≠ 0)
    (hfaber : GCD369CubeC2LeadingFaberRowsAt Xn Yn Zn u v T) :
    ∀ r : K, r ^ 3 + u * r + v = 0 →
      Xn * r ^ 2 + Yn * r + Zn = 0 → False := by
  dsimp [GCD369CubeC2LeadingFaberRowsAt] at hfaber
  have hcoeff := GCD369CubeFaberC2NormalCoefficients Xn Yn Zn u v T
  dsimp at hcoeff
  rcases hfaber with ⟨hf1, hf2, hf3, hf4⟩
  rcases hcoeff with ⟨hc1, hc2, hc3, hc4⟩
  rw [hc1] at hf1
  rw [hc2] at hf2
  rw [hc3] at hf3
  rw [hc4] at hf4
  have h1 :
      -16 * T * v + 9 * u * Xn ^ 2 - 18 * Xn * Zn - 9 * Yn ^ 2 = 0 :=
    (mul_eq_zero.mp hf1).resolve_left (by norm_num)
  have h2 :
      8 * T * u ^ 2 + 27 * v * Xn ^ 2 + 54 * u * Xn * Yn -
        54 * Yn * Zn = 0 :=
    (mul_eq_zero.mp hf2).resolve_left (by norm_num)
  have h3 : GCD369CubeNormalRow3 Xn Yn Zn u v = 0 :=
    (mul_eq_zero.mp hf3).resolve_left (by norm_num)
  have h4 :
      16 * T * u ^ 3 - 72 * T * v ^ 2 - 243 * u * v * Xn ^ 2 -
        162 * u ^ 2 * Xn * Yn + 324 * v * Xn * Zn +
        162 * v * Yn ^ 2 + 162 * u * Yn * Zn = 0 :=
    (mul_eq_zero.mp hf4).resolve_left (by norm_num)
  obtain ⟨lambda, hlambda, hscale⟩ :=
    GCD369CubeExistsWeightedNormalizer 7 (by norm_num) T hT
  apply GCD369CubeNoCommonRootOfWeightedScale lambda Xn Yn Zn u v
  apply GCD369CubeC2NoCommonRoot
    (lambda ^ 4 * Xn) (lambda ^ 5 * Yn) (lambda ^ 6 * Zn)
    (lambda ^ 2 * u) (lambda ^ 3 * v)
    (GCD369CubeProjectiveOfWeightedScale lambda u v hlambda hprojective)
  · calc
      -16 * (lambda ^ 3 * v) +
          9 * (lambda ^ 2 * u) * (lambda ^ 4 * Xn) ^ 2 -
          18 * (lambda ^ 4 * Xn) * (lambda ^ 6 * Zn) -
          9 * (lambda ^ 5 * Yn) ^ 2 =
          lambda ^ 10 * (-16 * T * v + 9 * u * Xn ^ 2 -
            18 * Xn * Zn - 9 * Yn ^ 2) := by
              linear_combination (-(lambda ^ 3 * (-16 * v))) * hscale
      _ = 0 := by rw [h1, mul_zero]
  · calc
      8 * (lambda ^ 2 * u) ^ 2 +
          27 * (lambda ^ 3 * v) * (lambda ^ 4 * Xn) ^ 2 +
          54 * (lambda ^ 2 * u) * (lambda ^ 4 * Xn) *
            (lambda ^ 5 * Yn) -
          54 * (lambda ^ 5 * Yn) * (lambda ^ 6 * Zn) =
          lambda ^ 11 * (8 * T * u ^ 2 + 27 * v * Xn ^ 2 +
            54 * u * Xn * Yn - 54 * Yn * Zn) := by
              linear_combination (-(lambda ^ 4 * (8 * u ^ 2))) * hscale
      _ = 0 := by rw [h2, mul_zero]
  · calc
      2 * (lambda ^ 2 * u) ^ 2 * (lambda ^ 4 * Xn) ^ 2 -
          6 * (lambda ^ 3 * v) * (lambda ^ 4 * Xn) *
            (lambda ^ 5 * Yn) -
          4 * (lambda ^ 2 * u) * (lambda ^ 4 * Xn) *
            (lambda ^ 6 * Zn) -
          2 * (lambda ^ 2 * u) * (lambda ^ 5 * Yn) ^ 2 +
          3 * (lambda ^ 6 * Zn) ^ 2 =
          lambda ^ 12 * GCD369CubeNormalRow3 Xn Yn Zn u v := by
              rw [GCD369CubeNormalRow3]
              ring
      _ = 0 := by rw [h3, mul_zero]
  · calc
      16 * (lambda ^ 2 * u) ^ 3 - 72 * (lambda ^ 3 * v) ^ 2 -
          243 * (lambda ^ 2 * u) * (lambda ^ 3 * v) *
            (lambda ^ 4 * Xn) ^ 2 -
          162 * (lambda ^ 2 * u) ^ 2 * (lambda ^ 4 * Xn) *
            (lambda ^ 5 * Yn) +
          324 * (lambda ^ 3 * v) * (lambda ^ 4 * Xn) *
            (lambda ^ 6 * Zn) +
          162 * (lambda ^ 3 * v) * (lambda ^ 5 * Yn) ^ 2 +
          162 * (lambda ^ 2 * u) * (lambda ^ 5 * Yn) *
            (lambda ^ 6 * Zn) =
          lambda ^ 13 * (16 * T * u ^ 3 - 72 * T * v ^ 2 -
            243 * u * v * Xn ^ 2 - 162 * u ^ 2 * Xn * Yn +
            324 * v * Xn * Zn + 162 * v * Yn ^ 2 + 162 * u * Yn * Zn) := by
              linear_combination
                (-(lambda ^ 6 * (16 * u ^ 3 - 72 * v ^ 2))) * hscale
      _ = 0 := by rw [h4, mul_zero]

/-- An arbitrary nonzero first `c1` load forbids a common root. -/
theorem GCD369CubeC1LeadingFaberRowsAt_noCommonRoot
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (Xn Yn Zn u v T : K) (hT : T ≠ 0)
    (hprojective : u ≠ 0 ∨ v ≠ 0)
    (hfaber : GCD369CubeC1LeadingFaberRowsAt Xn Yn Zn u v T) :
    ∀ r : K, r ^ 3 + u * r + v = 0 →
      Xn * r ^ 2 + Yn * r + Zn = 0 → False := by
  dsimp [GCD369CubeC1LeadingFaberRowsAt] at hfaber
  have hcoeff := GCD369CubeFaberC1NormalCoefficients Xn Yn Zn u v T
  dsimp at hcoeff
  rcases hfaber with ⟨hf1, hf2, hf3, hf4⟩
  rcases hcoeff with ⟨hc1, hc2, hc3, hc4⟩
  rw [hc1] at hf1
  rw [hc2] at hf2
  rw [hc3] at hf3
  rw [hc4] at hf4
  have h1 :
      8 * T * u - 9 * u * Xn ^ 2 + 18 * Xn * Zn + 9 * Yn ^ 2 = 0 :=
    (mul_eq_zero.mp hf1).resolve_left (by norm_num)
  have h2 :
      -8 * T * v + 9 * v * Xn ^ 2 + 18 * u * Xn * Yn -
        18 * Yn * Zn = 0 :=
    (mul_eq_zero.mp hf2).resolve_left (by norm_num)
  have h3 : GCD369CubeNormalRow3 Xn Yn Zn u v = 0 :=
    (mul_eq_zero.mp hf3).resolve_left (by norm_num)
  have h4 :
      8 * T * u * v + 27 * u * v * Xn ^ 2 + 18 * u ^ 2 * Xn * Yn -
        36 * v * Xn * Zn - 18 * v * Yn ^ 2 - 18 * u * Yn * Zn = 0 :=
    (mul_eq_zero.mp hf4).resolve_left (by norm_num)
  obtain ⟨lambda, hlambda, hscale⟩ :=
    GCD369CubeExistsWeightedNormalizer 8 (by norm_num) T hT
  apply GCD369CubeNoCommonRootOfWeightedScale lambda Xn Yn Zn u v
  apply GCD369CubeC1NoCommonRoot
    (lambda ^ 4 * Xn) (lambda ^ 5 * Yn) (lambda ^ 6 * Zn)
    (lambda ^ 2 * u) (lambda ^ 3 * v)
    (GCD369CubeProjectiveOfWeightedScale lambda u v hlambda hprojective)
  · calc
      8 * (lambda ^ 2 * u) -
          9 * (lambda ^ 2 * u) * (lambda ^ 4 * Xn) ^ 2 +
          18 * (lambda ^ 4 * Xn) * (lambda ^ 6 * Zn) +
          9 * (lambda ^ 5 * Yn) ^ 2 =
          lambda ^ 10 * (8 * T * u - 9 * u * Xn ^ 2 +
            18 * Xn * Zn + 9 * Yn ^ 2) := by
              linear_combination (-(lambda ^ 2 * (8 * u))) * hscale
      _ = 0 := by rw [h1, mul_zero]
  · calc
      -8 * (lambda ^ 3 * v) +
          9 * (lambda ^ 3 * v) * (lambda ^ 4 * Xn) ^ 2 +
          18 * (lambda ^ 2 * u) * (lambda ^ 4 * Xn) *
            (lambda ^ 5 * Yn) -
          18 * (lambda ^ 5 * Yn) * (lambda ^ 6 * Zn) =
          lambda ^ 11 * (-8 * T * v + 9 * v * Xn ^ 2 +
            18 * u * Xn * Yn - 18 * Yn * Zn) := by
              linear_combination (-(lambda ^ 3 * (-8 * v))) * hscale
      _ = 0 := by rw [h2, mul_zero]
  · calc
      2 * (lambda ^ 2 * u) ^ 2 * (lambda ^ 4 * Xn) ^ 2 -
          6 * (lambda ^ 3 * v) * (lambda ^ 4 * Xn) *
            (lambda ^ 5 * Yn) -
          4 * (lambda ^ 2 * u) * (lambda ^ 4 * Xn) *
            (lambda ^ 6 * Zn) -
          2 * (lambda ^ 2 * u) * (lambda ^ 5 * Yn) ^ 2 +
          3 * (lambda ^ 6 * Zn) ^ 2 =
          lambda ^ 12 * GCD369CubeNormalRow3 Xn Yn Zn u v := by
              rw [GCD369CubeNormalRow3]
              ring
      _ = 0 := by rw [h3, mul_zero]
  · calc
      8 * (lambda ^ 2 * u) * (lambda ^ 3 * v) +
          27 * (lambda ^ 2 * u) * (lambda ^ 3 * v) *
            (lambda ^ 4 * Xn) ^ 2 +
          18 * (lambda ^ 2 * u) ^ 2 * (lambda ^ 4 * Xn) *
            (lambda ^ 5 * Yn) -
          36 * (lambda ^ 3 * v) * (lambda ^ 4 * Xn) *
            (lambda ^ 6 * Zn) -
          18 * (lambda ^ 3 * v) * (lambda ^ 5 * Yn) ^ 2 -
          18 * (lambda ^ 2 * u) * (lambda ^ 5 * Yn) *
            (lambda ^ 6 * Zn) =
          lambda ^ 13 * (8 * T * u * v + 27 * u * v * Xn ^ 2 +
            18 * u ^ 2 * Xn * Yn - 36 * v * Xn * Zn -
            18 * v * Yn ^ 2 - 18 * u * Yn * Zn) := by
              linear_combination (-(lambda ^ 5 * (8 * u * v))) * hscale
      _ = 0 := by rw [h4, mul_zero]

/-- An arbitrary nonzero first `rho1` target load forbids a common root. -/
theorem GCD369CubeRhoOneLeadingFaberRowsAt_noCommonRoot
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (Xn Yn Zn u v T : K) (hT : T ≠ 0)
    (hprojective : u ≠ 0 ∨ v ≠ 0)
    (hfaber : GCD369CubeRhoOneLeadingFaberRowsAt Xn Yn Zn u v T) :
    ∀ r : K, r ^ 3 + u * r + v = 0 →
      Xn * r ^ 2 + Yn * r + Zn = 0 → False := by
  dsimp [GCD369CubeRhoOneLeadingFaberRowsAt] at hfaber
  have hcoeff := GCD369CubeFaberCommonNormalCoefficients Xn Yn Zn u v
  dsimp at hcoeff
  rcases hfaber with ⟨hf1, hf2, hf3, hf4⟩
  rcases hcoeff with ⟨hc1, hc2, hc3, hc4⟩
  rw [hc1] at hf1
  rw [hc2] at hf2
  rw [hc3] at hf3
  rw [hc4] at hf4
  have h1 : GCD369CubeNormalRow1 Xn Yn Zn u + 1944 * T = 0 := by
    linear_combination (-1 / 32) * hf1
  have h2 : GCD369CubeNormalRow2 Xn Yn Zn u v = 0 :=
    (mul_eq_zero.mp hf2).resolve_left (by norm_num)
  have h3 : GCD369CubeNormalRow3 Xn Yn Zn u v = 0 :=
    (mul_eq_zero.mp hf3).resolve_left (by norm_num)
  have h4 : GCD369CubeNormalRow4 Xn Yn Zn u v = 0 :=
    (mul_eq_zero.mp hf4).resolve_left (by norm_num)
  obtain ⟨lambda, hlambda, hscale⟩ :=
    GCD369CubeExistsWeightedNormalizer 10 (by norm_num) T hT
  apply GCD369CubeNoCommonRootOfWeightedScale lambda Xn Yn Zn u v
  apply GCD369CubeRhoOneNoCommonRoot
    (lambda ^ 4 * Xn) (lambda ^ 5 * Yn) (lambda ^ 6 * Zn)
    (lambda ^ 2 * u) (lambda ^ 3 * v)
    (GCD369CubeProjectiveOfWeightedScale lambda u v hlambda hprojective)
  · calc
      729 * (lambda ^ 2 * u) * (lambda ^ 4 * Xn) ^ 2 -
          1458 * (lambda ^ 4 * Xn) * (lambda ^ 6 * Zn) -
          729 * (lambda ^ 5 * Yn) ^ 2 + 1944 =
          lambda ^ 10 * (GCD369CubeNormalRow1 Xn Yn Zn u + 1944 * T) := by
              rw [GCD369CubeNormalRow1]
              linear_combination (-1944) * hscale
      _ = 0 := by rw [h1, mul_zero]
  · calc
      -2187 * (lambda ^ 3 * v) * (lambda ^ 4 * Xn) ^ 2 -
          4374 * (lambda ^ 2 * u) * (lambda ^ 4 * Xn) *
            (lambda ^ 5 * Yn) +
          4374 * (lambda ^ 5 * Yn) * (lambda ^ 6 * Zn) =
          lambda ^ 11 * GCD369CubeNormalRow2 Xn Yn Zn u v := by
              rw [GCD369CubeNormalRow2]
              ring
      _ = 0 := by rw [h2, mul_zero]
  · calc
      2 * (lambda ^ 2 * u) ^ 2 * (lambda ^ 4 * Xn) ^ 2 -
          6 * (lambda ^ 3 * v) * (lambda ^ 4 * Xn) *
            (lambda ^ 5 * Yn) -
          4 * (lambda ^ 2 * u) * (lambda ^ 4 * Xn) *
            (lambda ^ 6 * Zn) -
          2 * (lambda ^ 2 * u) * (lambda ^ 5 * Yn) ^ 2 +
          3 * (lambda ^ 6 * Zn) ^ 2 =
          lambda ^ 12 * GCD369CubeNormalRow3 Xn Yn Zn u v := by
              rw [GCD369CubeNormalRow3]
              ring
      _ = 0 := by rw [h3, mul_zero]
  · calc
      19683 * (lambda ^ 2 * u) * (lambda ^ 3 * v) *
            (lambda ^ 4 * Xn) ^ 2 +
          13122 * (lambda ^ 2 * u) ^ 2 * (lambda ^ 4 * Xn) *
            (lambda ^ 5 * Yn) -
          26244 * (lambda ^ 3 * v) * (lambda ^ 4 * Xn) *
            (lambda ^ 6 * Zn) -
          13122 * (lambda ^ 3 * v) * (lambda ^ 5 * Yn) ^ 2 -
          13122 * (lambda ^ 2 * u) * (lambda ^ 5 * Yn) *
            (lambda ^ 6 * Zn) =
          lambda ^ 13 * GCD369CubeNormalRow4 Xn Yn Zn u v := by
              rw [GCD369CubeNormalRow4]
              ring
      _ = 0 := by rw [h4, mul_zero]

/-- An arbitrary nonzero first `rho2` target load forbids a common root. -/
theorem GCD369CubeRhoTwoLeadingFaberRowsAt_noCommonRoot
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (Xn Yn Zn u v T : K) (hT : T ≠ 0)
    (hprojective : u ≠ 0 ∨ v ≠ 0)
    (hfaber : GCD369CubeRhoTwoLeadingFaberRowsAt Xn Yn Zn u v T) :
    ∀ r : K, r ^ 3 + u * r + v = 0 →
      Xn * r ^ 2 + Yn * r + Zn = 0 → False := by
  dsimp [GCD369CubeRhoTwoLeadingFaberRowsAt] at hfaber
  have hcoeff := GCD369CubeFaberCommonNormalCoefficients Xn Yn Zn u v
  dsimp at hcoeff
  rcases hfaber with ⟨hf1, hf2, hf3, hf4⟩
  rcases hcoeff with ⟨hc1, hc2, hc3, hc4⟩
  rw [hc1] at hf1
  rw [hc2] at hf2
  rw [hc3] at hf3
  rw [hc4] at hf4
  have h1 : GCD369CubeNormalRow1 Xn Yn Zn u = 0 :=
    (mul_eq_zero.mp hf1).resolve_left (by norm_num)
  have h2 : GCD369CubeNormalRow2 Xn Yn Zn u v - 5832 * T = 0 := by
    linear_combination (1 / 32) * hf2
  have h3 : GCD369CubeNormalRow3 Xn Yn Zn u v = 0 :=
    (mul_eq_zero.mp hf3).resolve_left (by norm_num)
  have h4 : GCD369CubeNormalRow4 Xn Yn Zn u v = 0 :=
    (mul_eq_zero.mp hf4).resolve_left (by norm_num)
  obtain ⟨lambda, hlambda, hscale⟩ :=
    GCD369CubeExistsWeightedNormalizer 11 (by norm_num) T hT
  apply GCD369CubeNoCommonRootOfWeightedScale lambda Xn Yn Zn u v
  apply GCD369CubeRhoTwoNoCommonRoot
    (lambda ^ 4 * Xn) (lambda ^ 5 * Yn) (lambda ^ 6 * Zn)
    (lambda ^ 2 * u) (lambda ^ 3 * v)
    (GCD369CubeProjectiveOfWeightedScale lambda u v hlambda hprojective)
  · calc
      729 * (lambda ^ 2 * u) * (lambda ^ 4 * Xn) ^ 2 -
          1458 * (lambda ^ 4 * Xn) * (lambda ^ 6 * Zn) -
          729 * (lambda ^ 5 * Yn) ^ 2 =
          lambda ^ 10 * GCD369CubeNormalRow1 Xn Yn Zn u := by
              rw [GCD369CubeNormalRow1]
              ring
      _ = 0 := by rw [h1, mul_zero]
  · calc
      -2187 * (lambda ^ 3 * v) * (lambda ^ 4 * Xn) ^ 2 -
          4374 * (lambda ^ 2 * u) * (lambda ^ 4 * Xn) *
            (lambda ^ 5 * Yn) +
          4374 * (lambda ^ 5 * Yn) * (lambda ^ 6 * Zn) - 5832 =
          lambda ^ 11 * (GCD369CubeNormalRow2 Xn Yn Zn u v - 5832 * T) := by
              rw [GCD369CubeNormalRow2]
              linear_combination 5832 * hscale
      _ = 0 := by rw [h2, mul_zero]
  · calc
      2 * (lambda ^ 2 * u) ^ 2 * (lambda ^ 4 * Xn) ^ 2 -
          6 * (lambda ^ 3 * v) * (lambda ^ 4 * Xn) *
            (lambda ^ 5 * Yn) -
          4 * (lambda ^ 2 * u) * (lambda ^ 4 * Xn) *
            (lambda ^ 6 * Zn) -
          2 * (lambda ^ 2 * u) * (lambda ^ 5 * Yn) ^ 2 +
          3 * (lambda ^ 6 * Zn) ^ 2 =
          lambda ^ 12 * GCD369CubeNormalRow3 Xn Yn Zn u v := by
              rw [GCD369CubeNormalRow3]
              ring
      _ = 0 := by rw [h3, mul_zero]
  · calc
      19683 * (lambda ^ 2 * u) * (lambda ^ 3 * v) *
            (lambda ^ 4 * Xn) ^ 2 +
          13122 * (lambda ^ 2 * u) ^ 2 * (lambda ^ 4 * Xn) *
            (lambda ^ 5 * Yn) -
          26244 * (lambda ^ 3 * v) * (lambda ^ 4 * Xn) *
            (lambda ^ 6 * Zn) -
          13122 * (lambda ^ 3 * v) * (lambda ^ 5 * Yn) ^ 2 -
          13122 * (lambda ^ 2 * u) * (lambda ^ 5 * Yn) *
            (lambda ^ 6 * Zn) =
          lambda ^ 13 * GCD369CubeNormalRow4 Xn Yn Zn u v := by
              rw [GCD369CubeNormalRow4]
              ring
      _ = 0 := by rw [h4, mul_zero]

/-! ## Arbitrary-load sum and source boundary -/

/-- The eight exact early Faber alternatives with an arbitrary nonzero first
load.  Each constructor retains both the load and its nonvanishing proof. -/
inductive GCD369CubeArbitraryEarlyFaberLoad {K : Type u} [Field K]
    (Xn Yn Zn u v : K) : Type u where
  | d (T : K) (hT : T ≠ 0) (hprojective : u ≠ 0 ∨ v ≠ 0)
      (hfaber : GCD369CubeDLeadingFaberRowsAt Xn Yn Zn u v T)
  | c7 (T : K) (hT : T ≠ 0) (hprojective : u ≠ 0 ∨ v ≠ 0)
      (hfaber : GCD369CubeC7LeadingFaberRowsAt Xn Yn Zn u v T)
  | c5 (T : K) (hT : T ≠ 0) (hprojective : u ≠ 0 ∨ v ≠ 0)
      (hfaber : GCD369CubeC5LeadingFaberRowsAt Xn Yn Zn u v T)
  | c4 (T : K) (hT : T ≠ 0) (hprojective : u ≠ 0 ∨ v ≠ 0)
      (hfaber : GCD369CubeC4LeadingFaberRowsAt Xn Yn Zn u v T)
  | c2 (T : K) (hT : T ≠ 0) (hprojective : u ≠ 0 ∨ v ≠ 0)
      (hfaber : GCD369CubeC2LeadingFaberRowsAt Xn Yn Zn u v T)
  | c1 (T : K) (hT : T ≠ 0) (hprojective : u ≠ 0 ∨ v ≠ 0)
      (hfaber : GCD369CubeC1LeadingFaberRowsAt Xn Yn Zn u v T)
  | rhoOne (T : K) (hT : T ≠ 0) (hprojective : u ≠ 0 ∨ v ≠ 0)
      (hfaber : GCD369CubeRhoOneLeadingFaberRowsAt Xn Yn Zn u v T)
  | rhoTwo (T : K) (hT : T ≠ 0) (hprojective : u ≠ 0 ∨ v ≠ 0)
      (hfaber : GCD369CubeRhoTwoLeadingFaberRowsAt Xn Yn Zn u v T)

namespace GCD369CubeArbitraryEarlyFaberLoad

/-- Scaled weight of the arbitrary first nonzero load. -/
def weight {K : Type*} [Field K] {Xn Yn Zn u v : K}
    (L : GCD369CubeArbitraryEarlyFaberLoad Xn Yn Zn u v) : ℕ :=
  match L with
  | .d .. => 1
  | .c7 .. => 2
  | .c5 .. => 4
  | .c4 .. => 5
  | .c2 .. => 7
  | .c1 .. => 8
  | .rhoOne .. => 10
  | .rhoTwo .. => 11

/-- The arbitrary-load sum has exactly the eight audited early weights. -/
theorem weight_mem {K : Type*} [Field K] {Xn Yn Zn u v : K}
    (L : GCD369CubeArbitraryEarlyFaberLoad Xn Yn Zn u v) :
    L.weight ∈ ([1, 2, 4, 5, 7, 8, 10, 11] : List ℕ) := by
  cases L <;> simp [weight]

/-- The arbitrary exact Faber alternative supplies the original-coordinate
no-common-root certificate after internal weighted normalization. -/
theorem noCommonRoot {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {Xn Yn Zn u v : K} (L : GCD369CubeArbitraryEarlyFaberLoad Xn Yn Zn u v) :
    ∀ r : K, r ^ 3 + u * r + v = 0 →
      Xn * r ^ 2 + Yn * r + Zn = 0 → False := by
  cases L with
  | d T hT hprojective hfaber =>
      exact GCD369CubeDLeadingFaberRowsAt_noCommonRoot
        Xn Yn Zn u v T hT hprojective hfaber
  | c7 T hT hprojective hfaber =>
      exact GCD369CubeC7LeadingFaberRowsAt_noCommonRoot
        Xn Yn Zn u v T hT hprojective hfaber
  | c5 T hT hprojective hfaber =>
      exact GCD369CubeC5LeadingFaberRowsAt_noCommonRoot
        Xn Yn Zn u v T hT hprojective hfaber
  | c4 T hT hprojective hfaber =>
      exact GCD369CubeC4LeadingFaberRowsAt_noCommonRoot
        Xn Yn Zn u v T hT hprojective hfaber
  | c2 T hT hprojective hfaber =>
      exact GCD369CubeC2LeadingFaberRowsAt_noCommonRoot
        Xn Yn Zn u v T hT hprojective hfaber
  | c1 T hT hprojective hfaber =>
      exact GCD369CubeC1LeadingFaberRowsAt_noCommonRoot
        Xn Yn Zn u v T hT hprojective hfaber
  | rhoOne T hT hprojective hfaber =>
      exact GCD369CubeRhoOneLeadingFaberRowsAt_noCommonRoot
        Xn Yn Zn u v T hT hprojective hfaber
  | rhoTwo T hT hprojective hfaber =>
      exact GCD369CubeRhoTwoLeadingFaberRowsAt_noCommonRoot
        Xn Yn Zn u v T hT hprojective hfaber

end GCD369CubeArbitraryEarlyFaberLoad

/-- Early source-boundary data with the actual nonzero Faber load retained;
there is no normalized coefficient among its inputs. -/
structure GCD369CubeArbitraryFaberEarlyBoundaryData
    (K : Type*) [Field K] where
  Xn : K
  Yn : K
  Zn : K
  u : K
  v : K
  load : GCD369CubeArbitraryEarlyFaberLoad Xn Yn Zn u v
  q : ℚ
  a : K
  h : K
  r : K
  EF : HahnSeries ℚ K
  EG : HahnSeries ℚ K
  ha : a ≠ 0
  hh : h ≠ 0
  hKroot : r ^ 3 + u * r + v = 0
  hEF : (↑(1 : ℚ) : WithTop ℚ) < EF.orderTop
  hEG : (↑(3 / 2 : ℚ) : WithTop ℚ) < EG.orderTop
  hfregular : (↑((12 : ℚ) / load.weight) : WithTop ℚ) ≤
    let A : HahnSeries ℚ K := HahnSeries.single q a
    let B : HahnSeries ℚ K := HahnSeries.single 0
      (Xn * r ^ 2 + Yn * r + Zn)
    let H : HahnSeries ℚ K := HahnSeries.single 1 h
    (A ^ 2 + H * B + EF).orderTop
  hgregular : (↑((18 : ℚ) / load.weight) : WithTop ℚ) ≤
    let A : HahnSeries ℚ K := HahnSeries.single q a
    let B : HahnSeries ℚ K := HahnSeries.single 0
      (Xn * r ^ 2 + Yn * r + Zn)
    let H : HahnSeries ℚ K := HahnSeries.single 1 h
    let C32 : HahnSeries ℚ K := HahnSeries.single 0 (3 / 2)
    (A ^ 3 + C32 * H * A * B + EG).orderTop

/-- Every arbitrary nonzero early Faber landing violates the original source
boundary inequalities. -/
theorem GCD369CubeArbitraryFaberEarlyBoundaryDataEmpty
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (D : GCD369CubeArbitraryFaberEarlyBoundaryData K) : False := by
  exact GCD369CubeEarlyCommonCubicBoundaryExclusion
    D.load.weight D.load.weight_mem D.q D.a D.h D.Xn D.Yn D.Zn D.u D.v D.r
      D.ha D.hh D.load.noCommonRoot D.hKroot D.EF D.EG D.hEF D.hEG
      D.hfregular D.hgregular

/-- The previous finite landing sum, enlarged only by the source-facing
arbitrary early-load constructor. -/
inductive GCD369CubeTrajectoryLandingWithArbitraryEarly
    (K : Type*) [Field K] [CharZero K] : Prop where
  | certified (L : GCD369CubeTrajectoryLanding K)
  | arbitraryEarly (D : GCD369CubeArbitraryFaberEarlyBoundaryData K)

/-- The enlarged trajectory landing sum is empty. -/
theorem GCD369CubeTrajectoryLandingWithArbitraryEarlyEmpty
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (L : GCD369CubeTrajectoryLandingWithArbitraryEarly K) : False := by
  cases L with
  | certified L => exact GCD369CubeTrajectoryLandingEmpty L
  | arbitraryEarly D => exact GCD369CubeArbitraryFaberEarlyBoundaryDataEmpty D

#print axioms GCD369CubeExistsWeightedNormalizer
#print axioms GCD369CubeDLeadingFaberRowsAt_noCommonRoot
#print axioms GCD369CubeC7LeadingFaberRowsAt_noCommonRoot
#print axioms GCD369CubeC5LeadingFaberRowsAt_noCommonRoot
#print axioms GCD369CubeC4LeadingFaberRowsAt_noCommonRoot
#print axioms GCD369CubeC2LeadingFaberRowsAt_noCommonRoot
#print axioms GCD369CubeC1LeadingFaberRowsAt_noCommonRoot
#print axioms GCD369CubeRhoOneLeadingFaberRowsAt_noCommonRoot
#print axioms GCD369CubeRhoTwoLeadingFaberRowsAt_noCommonRoot
#print axioms GCD369CubeArbitraryEarlyFaberLoad.noCommonRoot
#print axioms GCD369CubeArbitraryFaberEarlyBoundaryDataEmpty
#print axioms GCD369CubeTrajectoryLandingWithArbitraryEarlyEmpty
