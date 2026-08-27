import InfinityExpansion
import FiniteEarlyNormal

noncomputable section

open Polynomial

/-! # The first transverse load at infinity

This file connects the lightweight common-coefficient packet produced at
infinity to the generic exact Faber coefficient identities.  No finite-place
boundary value is used: the only inputs are the pole packet, its common-cubic
leading coordinates, and the first nonzero transverse normal jet.
-/

/-- Ground-field constants expanded at infinity are the canonical constants
of the regular Hahn local ring. -/
@[simp] theorem GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity_eq_constant
    {k : Type*} [Field k] (c : k) :
    GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity c =
      GCD369CubeHahnRegular.constant c := by
  apply Subtype.ext
  simp [GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity,
    GCD369CubeHahnRegular.constant, RatFunc.algebraMap_eq_C,
    GCD369CubeRatFuncHahnAtInfinity_C]

namespace GCD369CubeHahnCommonCoefficientData

/-- The direct constant half agrees with the canonical rational constant once
the generic finite-jet algebra is available. -/
theorem half_eq_ratCast
    {k : Type*} [Field k] [CharZero k] :
    GCD369CubeHahnRegular.half (k := k) =
      GCD369CubeHahnRegular.ratCast (1 / 2) := by
  apply Subtype.ext
  simp [GCD369CubeHahnRegular.half,
    GCD369CubeHahnRegular.ratCast,
    GCD369CubeHahnRegular.constant]

theorem two_mul_half
    {k : Type*} [Field k] [CharZero k] :
    (2 : GCD369CubeHahnRegular k) *
      GCD369CubeHahnRegular.half = 1 := by
  rw [half_eq_ratCast]
  exact GCD369CubeHahnRegular.two_mul_ratCast_half

/-- The top two scaled coefficients are exactly twice the moving cubic
coordinates. -/
theorem regular4_eq_two_cubicU
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k) :
    D.faber.scale.regular4 = 2 * D.cubicU := by
  dsimp only [cubicU]
  linear_combination
    -D.faber.scale.regular4 * (two_mul_half (k := k))

theorem regular3_eq_two_cubicV
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k) :
    D.faber.scale.regular3 = 2 * D.cubicV := by
  dsimp only [cubicV]
  linear_combination
    -D.faber.scale.regular3 * (two_mul_half (k := k))

/-- Reconstruct the lower three scaled coefficients from the normalized
first transverse jet. -/
theorem TransverseScale.regular2_eq
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale) :
    D.faber.scale.regular2 = D.cubicU ^ 2 +
      T.Xn * monomial T.delta T.hdelta.le := by
  have hn := T.hnormal2
  dsimp only [normal2] at hn
  linear_combination hn

theorem TransverseScale.regular1_eq
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale) :
    D.faber.scale.regular1 = 2 * D.cubicU * D.cubicV +
      T.Yn * monomial T.delta T.hdelta.le := by
  have hn := T.hnormal1
  dsimp only [normal1] at hn
  linear_combination hn

theorem TransverseScale.regular0_eq
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale) :
    D.faber.scale.regular0 = D.cubicV ^ 2 +
      T.Zn * monomial T.delta T.hdelta.le := by
  have hn := T.hnormal0
  dsimp only [normal0] at hn
  linear_combination hn

/-- The two identical monomial implementations are equal as regular Hahn
series; this exposes the generic coefficient lemmas. -/
theorem monomial_eq_regularMonomial
    {k : Type*} [Field k] (delta : ℚ) (hdelta : 0 ≤ delta) :
    monomial (k := k) delta hdelta =
      GCD369CubeHahnRegular.monomial delta hdelta := by
  apply Subtype.ext
  rfl

/-- Exact first zero-high numerator identity at the infinity transverse
scale. -/
theorem TransverseScale.zeroHighN1Expansion
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale) :
    729 * GCD369CubeFaberN1
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 =
      (-32 * GCD369CubeNormalRow1 T.Xn T.Yn T.Zn D.cubicU) *
        (monomial T.delta T.hdelta.le) ^ 2 := by
  let H : GCD369CubeHahnRegular k := monomial T.delta T.hdelta.le
  have hp := (GCD369CubeFaberCommonNormalNumeratorsCommRing
    T.Xn T.Yn T.Zn D.cubicU D.cubicV).1
  have h := congrArg
    (fun p : (GCD369CubeHahnRegular k)[X] => p.eval H) hp
  simp only [GCD369CubeFaberN1, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat] at h
  rw [T.regular0_eq, T.regular1_eq, T.regular2_eq,
    D.regular3_eq_two_cubicV, D.regular4_eq_two_cubicU]
  simpa only [H, GCD369CubeFaberN1] using h

/-- Exact second zero-high numerator identity. -/
theorem TransverseScale.zeroHighN2Expansion
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale) :
    2187 * GCD369CubeFaberN2
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 =
      (32 * GCD369CubeNormalRow2
        T.Xn T.Yn T.Zn D.cubicU D.cubicV) *
        (monomial T.delta T.hdelta.le) ^ 2 := by
  let H : GCD369CubeHahnRegular k := monomial T.delta T.hdelta.le
  have hp := (GCD369CubeFaberCommonNormalNumeratorsCommRing
    T.Xn T.Yn T.Zn D.cubicU D.cubicV).2.1
  have h := congrArg
    (fun p : (GCD369CubeHahnRegular k)[X] => p.eval H) hp
  simp only [GCD369CubeFaberN2, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat] at h
  rw [T.regular0_eq, T.regular1_eq, T.regular2_eq,
    D.regular3_eq_two_cubicV, D.regular4_eq_two_cubicU]
  simpa only [H, GCD369CubeFaberN2] using h

/-- Exact third zero-high numerator identity. -/
theorem TransverseScale.zeroHighN3Expansion
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale) :
    GCD369CubeFaberN3
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 =
      (128 * GCD369CubeNormalRow3
        T.Xn T.Yn T.Zn D.cubicU D.cubicV) *
          (monomial T.delta T.hdelta.le) ^ 2 -
        (64 * T.Xn ^ 3) * (monomial T.delta T.hdelta.le) ^ 3 := by
  let H : GCD369CubeHahnRegular k := monomial T.delta T.hdelta.le
  have hp := (GCD369CubeFaberCommonNormalNumeratorsCommRing
    T.Xn T.Yn T.Zn D.cubicU D.cubicV).2.2.1
  have h := congrArg
    (fun p : (GCD369CubeHahnRegular k)[X] => p.eval H) hp
  simp only [GCD369CubeFaberN3, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat] at h
  rw [T.regular0_eq, T.regular1_eq, T.regular2_eq,
    D.regular3_eq_two_cubicV, D.regular4_eq_two_cubicU]
  simpa only [H, GCD369CubeFaberN3] using h

/-- Exact fourth zero-high numerator identity. -/
theorem TransverseScale.zeroHighN4Expansion
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale) :
    6561 * GCD369CubeFaberN4
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 =
      (32 * GCD369CubeNormalRow4
        T.Xn T.Yn T.Zn D.cubicU D.cubicV) *
          (monomial T.delta T.hdelta.le) ^ 2 -
        (314928 * T.Yn * T.Xn ^ 2) *
          (monomial T.delta T.hdelta.le) ^ 3 := by
  let H : GCD369CubeHahnRegular k := monomial T.delta T.hdelta.le
  have hp := (GCD369CubeFaberCommonNormalNumeratorsCommRing
    T.Xn T.Yn T.Zn D.cubicU D.cubicV).2.2.2
  have h := congrArg (Polynomial.evalRingHom H) hp
  simp only [map_add, map_mul, map_sub, map_pow, map_ofNat,
    GCD369CubeFaberN4_map, Polynomial.coe_evalRingHom,
    Polynomial.eval_C, Polynomial.eval_X] at h
  rw [T.regular0_eq, T.regular1_eq, T.regular2_eq,
    D.regular3_eq_two_cubicV, D.regular4_eq_two_cubicU]
  simpa only [H] using h

/-- The coefficient at twice the first transverse order is the first
universal normal row on the residue jet. -/
theorem TransverseScale.zeroHighN1Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale) :
    (729 * GCD369CubeFaberN1
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) =
      -32 * GCD369CubeNormalRow1
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u := by
  have h := congrArg
    (fun x : GCD369CubeHahnRegular k =>
      x.1.coeff (((2 : ℕ) : ℚ) * T.delta))
    T.zeroHighN1Expansion
  rw [monomial_eq_regularMonomial,
    GCD369CubeHahnRegular.coeff_mul_monomial_pow_at
      T.delta T.hdelta 2] at h
  simpa only [GCD369CubeNormalRow1, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, D.constantCoeff_cubicU,
    Nat.cast_ofNat] using h

/-- Coefficient form of the second universal normal row. -/
theorem TransverseScale.zeroHighN2Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale) :
    (2187 * GCD369CubeFaberN2
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) =
      32 * GCD369CubeNormalRow2
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v := by
  have h := congrArg
    (fun x : GCD369CubeHahnRegular k =>
      x.1.coeff (((2 : ℕ) : ℚ) * T.delta))
    T.zeroHighN2Expansion
  rw [monomial_eq_regularMonomial,
    GCD369CubeHahnRegular.coeff_mul_monomial_pow_at
      T.delta T.hdelta 2] at h
  simpa only [GCD369CubeNormalRow2, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, D.constantCoeff_cubicU,
    D.constantCoeff_cubicV, Nat.cast_ofNat] using h

/-- Coefficient form of the third universal normal row; the cubic error is
strictly too high to contribute. -/
theorem TransverseScale.zeroHighN3Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale) :
    (GCD369CubeFaberN3
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) =
      128 * GCD369CubeNormalRow3
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v := by
  have h := congrArg
    (fun x : GCD369CubeHahnRegular k =>
      x.1.coeff (((2 : ℕ) : ℚ) * T.delta))
    T.zeroHighN3Expansion
  rw [monomial_eq_regularMonomial,
    GCD369CubeHahnRegular.coeff_quadratic_sub_cubic
      T.delta T.hdelta] at h
  simpa only [GCD369CubeNormalRow3, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, D.constantCoeff_cubicU,
    D.constantCoeff_cubicV, Nat.cast_ofNat] using h

/-- Coefficient form of the fourth universal normal row. -/
theorem TransverseScale.zeroHighN4Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale) :
    (6561 * GCD369CubeFaberN4
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) =
      32 * GCD369CubeNormalRow4
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v := by
  have h := congrArg
    (fun x : GCD369CubeHahnRegular k =>
      x.1.coeff (((2 : ℕ) : ℚ) * T.delta))
    T.zeroHighN4Expansion
  rw [monomial_eq_regularMonomial,
    GCD369CubeHahnRegular.coeff_quadratic_sub_cubic
      T.delta T.hdelta] at h
  simpa only [GCD369CubeNormalRow4, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, D.constantCoeff_cubicU,
    D.constantCoeff_cubicV, Nat.cast_ofNat] using h

/-- Strictly before the weight-one load, the first transverse residue obeys
all four universal zero-load normal rows. -/
theorem TransverseScale.zeroLoadLeadingRows_before_d
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (Kd Kc7 Kc5 Kc4 Kc3 Kc2 Kc1 Kr1 Kr2 Kr3 Kr4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant Kd)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant Kc7)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant Kc5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant Kc4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant Kc3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant Kc2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant Kc1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant Kr1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant Kr2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant Kr3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant Kr4)
    (hearly : 2 * T.delta < D.faber.scale.p) :
    GCD369CubeNormalRow1
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u = 0 ∧
    GCD369CubeNormalRow2
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v = 0 ∧
    GCD369CubeNormalRow3
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v = 0 ∧
    GCD369CubeNormalRow4
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v = 0 := by
  have hz := D.faber.zeroHighNCoeff_zero_before_d
    Kd Kc7 Kc5 Kc4 Kc3 Kc2 Kc1 Kr1 Kr2 Kr3 Kr4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4
    (2 * T.delta) (mul_nonneg (by norm_num) T.hdelta.le) hearly
  rcases hz with ⟨h1, h2, h3, h4⟩
  constructor
  · have hc :
        (729 * GCD369CubeFaberN1
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4).1.coeff (2 * T.delta) =
        -32 * GCD369CubeNormalRow1
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u := by
      convert T.zeroHighN1Coeff using 1 <;> norm_num
    rw [hc] at h1
    exact (mul_eq_zero.mp h1).resolve_left (by norm_num)
  constructor
  · have hc :
        (2187 * GCD369CubeFaberN2
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4).1.coeff (2 * T.delta) =
        32 * GCD369CubeNormalRow2
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v := by
      convert T.zeroHighN2Coeff using 1 <;> norm_num
    rw [hc] at h2
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  constructor
  · have hcoeff :
        (243 * GCD369CubeFaberN3
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4).1.coeff (2 * T.delta) =
        (243 : k) *
          (GCD369CubeFaberN3
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4).1.coeff (2 * T.delta) := by
      exact GCD369CubeHahnRegular.coeff_nat_mul 243 _ _
    rw [hcoeff] at h3
    have h3' :
        (GCD369CubeFaberN3
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4).1.coeff (2 * T.delta) = 0 :=
      (mul_eq_zero.mp h3).resolve_left (by norm_num)
    have hc :
        (GCD369CubeFaberN3
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4).1.coeff (2 * T.delta) =
        128 * GCD369CubeNormalRow3
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v := by
      convert T.zeroHighN3Coeff using 1 <;> norm_num
    rw [hc] at h3'
    exact (mul_eq_zero.mp h3').resolve_left (by norm_num)
  · have hc :
        (6561 * GCD369CubeFaberN4
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4).1.coeff (2 * T.delta) =
        32 * GCD369CubeNormalRow4
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v := by
      convert T.zeroHighN4Coeff using 1 <;> norm_num
    rw [hc] at h4
    exact (mul_eq_zero.mp h4).resolve_left (by norm_num)

/-- A first transverse jet below the weight-one scale forces the leading
common cubic to be singular. -/
theorem TransverseScale.discriminant_zero_before_d
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (Kd Kc7 Kc5 Kc4 Kc3 Kc2 Kc1 Kr1 Kr2 Kr3 Kr4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant Kd)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant Kc7)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant Kc5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant Kc4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant Kc3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant Kc2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant Kc1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant Kr1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant Kr2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant Kr3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant Kr4)
    (hearly : 2 * T.delta < D.faber.scale.p) :
    4 * D.u ^ 3 + 27 * D.v ^ 2 = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := T.zeroLoadLeadingRows_before_d
    Kd Kc7 Kc5 Kc4 Kc3 Kc2 Kc1 Kr1 Kr2 Kr3 Kr4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 hearly
  obtain ⟨r, _hX, hu, hv, _hY, _hZ⟩ :=
    GCD369CubeZeroLoadNormal_parametrization
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn)
      D.u D.v T.hleading h1 h2 h3 h4
  rw [hu, hv]
  ring

/-- Ordered first-transverse dichotomy: either the common cubic is already
singular at an earlier normal jet, or the weight-one load is no later than
twice the transverse order. -/
theorem TransverseScale.early_singular_or_d_not_later
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (Kd Kc7 Kc5 Kc4 Kc3 Kc2 Kc1 Kr1 Kr2 Kr3 Kr4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant Kd)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant Kc7)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant Kc5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant Kc4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant Kc3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant Kc2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant Kc1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant Kr1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant Kr2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant Kr3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant Kr4) :
    (2 * T.delta < D.faber.scale.p ∧
      4 * D.u ^ 3 + 27 * D.v ^ 2 = 0) ∨
      D.faber.scale.p ≤ 2 * T.delta := by
  rcases lt_or_ge (2 * T.delta) D.faber.scale.p with hearly | hlater
  · exact Or.inl ⟨hearly,
      T.discriminant_zero_before_d
        Kd Kc7 Kc5 Kc4 Kc3 Kc2 Kc1 Kr1 Kr2 Kr3 Kr4
        hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 hearly⟩
  · exact Or.inr hlater

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubePolynomialSource

/-- All eleven target/source parameters in the infinity Faber packet are
literal ground-field constants. -/
theorem infinityFaberPoleData_constant_loads
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k)
    (hpole :
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAtInfinity
        (S.normalizedP.coeff 4)).order < 0) :
    let F := S.infinityFaberPoleData hpole
    let P := S.faberConstantParameters
    let R := S.faberFirstIntegralConstants
    F.d = GCD369CubeHahnRegular.constant P.d ∧
    F.c7 = GCD369CubeHahnRegular.constant P.c7 ∧
    F.c5 = GCD369CubeHahnRegular.constant P.c5 ∧
    F.c4 = GCD369CubeHahnRegular.constant P.c4 ∧
    F.c3 = GCD369CubeHahnRegular.constant P.c3 ∧
    F.c2 = GCD369CubeHahnRegular.constant P.c2 ∧
    F.c1 = GCD369CubeHahnRegular.constant P.c1 ∧
    F.rho1 = GCD369CubeHahnRegular.constant R.rho1 ∧
    F.rho2 = GCD369CubeHahnRegular.constant R.rho2 ∧
    F.rho3 = GCD369CubeHahnRegular.constant R.rho3 ∧
    F.rho4 = GCD369CubeHahnRegular.constant R.rho4 := by
  dsimp only
  change
    GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity
        S.faberConstantParameters.d =
          GCD369CubeHahnRegular.constant S.faberConstantParameters.d ∧
    GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity
        S.faberConstantParameters.c7 =
          GCD369CubeHahnRegular.constant S.faberConstantParameters.c7 ∧
    GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity
        S.faberConstantParameters.c5 =
          GCD369CubeHahnRegular.constant S.faberConstantParameters.c5 ∧
    GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity
        S.faberConstantParameters.c4 =
          GCD369CubeHahnRegular.constant S.faberConstantParameters.c4 ∧
    GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity
        S.faberConstantParameters.c3 =
          GCD369CubeHahnRegular.constant S.faberConstantParameters.c3 ∧
    GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity
        S.faberConstantParameters.c2 =
          GCD369CubeHahnRegular.constant S.faberConstantParameters.c2 ∧
    GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity
        S.faberConstantParameters.c1 =
          GCD369CubeHahnRegular.constant S.faberConstantParameters.c1 ∧
    GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity
        S.faberFirstIntegralConstants.rho1 =
          GCD369CubeHahnRegular.constant S.faberFirstIntegralConstants.rho1 ∧
    GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity
        S.faberFirstIntegralConstants.rho2 =
          GCD369CubeHahnRegular.constant S.faberFirstIntegralConstants.rho2 ∧
    GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity
        S.faberFirstIntegralConstants.rho3 =
          GCD369CubeHahnRegular.constant S.faberFirstIntegralConstants.rho3 ∧
    GCD369CubeHahnRegular.ofRatFuncConstantAtInfinity
        S.faberFirstIntegralConstants.rho4 =
          GCD369CubeHahnRegular.constant S.faberFirstIntegralConstants.rho4
  simp

/-- Source-facing square-versus-first-transverse dichotomy. -/
theorem infinity_normals_zero_or_transverseScale
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0) :
    let D := S.infinityCommonCoefficientData hsdegree
    (D.normal2 = 0 ∧ D.normal1 = 0 ∧ D.normal0 = 0) ∨
      Nonempty D.TransverseScale := by
  dsimp only
  exact (S.infinityCommonCoefficientData hsdegree).normals_zero_or_transverseScale

/-- For the canonical infinity packet, every first transverse scale satisfies
the ordered early-singular versus weight-one-not-later dichotomy. -/
theorem infinity_firstTransverse_early_singular_or_d_not_later
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0) :
    let D := S.infinityCommonCoefficientData hsdegree
    ∀ T : D.TransverseScale,
      (2 * T.delta < D.faber.scale.p ∧
        4 * D.u ^ 3 + 27 * D.v ^ 2 = 0) ∨
        D.faber.scale.p ≤ 2 * T.delta := by
  dsimp only
  intro T
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  obtain ⟨hd, hc7, hc5, hc4, hc3, hc2, hc1,
      hr1, hr2, hr3, hr4⟩ :=
    S.infinityFaberPoleData_constant_loads hpole
  have hd' :
      (S.infinityCommonCoefficientData hsdegree).faber.d =
        GCD369CubeHahnRegular.constant P.d := by
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hd
  have hc7' :
      (S.infinityCommonCoefficientData hsdegree).faber.c7 =
        GCD369CubeHahnRegular.constant P.c7 := by
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hc7
  have hc5' :
      (S.infinityCommonCoefficientData hsdegree).faber.c5 =
        GCD369CubeHahnRegular.constant P.c5 := by
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hc5
  have hc4' :
      (S.infinityCommonCoefficientData hsdegree).faber.c4 =
        GCD369CubeHahnRegular.constant P.c4 := by
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hc4
  have hc3' :
      (S.infinityCommonCoefficientData hsdegree).faber.c3 =
        GCD369CubeHahnRegular.constant P.c3 := by
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hc3
  have hc2' :
      (S.infinityCommonCoefficientData hsdegree).faber.c2 =
        GCD369CubeHahnRegular.constant P.c2 := by
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hc2
  have hc1' :
      (S.infinityCommonCoefficientData hsdegree).faber.c1 =
        GCD369CubeHahnRegular.constant P.c1 := by
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hc1
  have hr1' :
      (S.infinityCommonCoefficientData hsdegree).faber.rho1 =
        GCD369CubeHahnRegular.constant R.rho1 := by
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hr1
  have hr2' :
      (S.infinityCommonCoefficientData hsdegree).faber.rho2 =
        GCD369CubeHahnRegular.constant R.rho2 := by
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hr2
  have hr3' :
      (S.infinityCommonCoefficientData hsdegree).faber.rho3 =
        GCD369CubeHahnRegular.constant R.rho3 := by
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hr3
  have hr4' :
      (S.infinityCommonCoefficientData hsdegree).faber.rho4 =
        GCD369CubeHahnRegular.constant R.rho4 := by
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hr4
  exact T.early_singular_or_d_not_later
    P.d P.c7 P.c5 P.c4 P.c3 P.c2 P.c1
    R.rho1 R.rho2 R.rho3 R.rho4
    hd' hc7' hc5' hc4' hc3' hc2' hc1'
    hr1' hr2' hr3' hr4'

end GCD369CubePolynomialSource
