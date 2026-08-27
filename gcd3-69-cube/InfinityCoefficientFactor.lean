import InfinityFirstLoad

/-! # Prescribed transverse factors for the infinity coefficient packet

This file supplies the coefficient-only counterpart of
`GCD369CubeHahnCommonValueData.TransverseFactor`.  It factors the three
common-cubic normal coordinates at any prescribed positive Hahn scale and
contains no recovered source coordinate or finite-place value data.
-/

noncomputable section

open Polynomial

namespace GCD369CubeHahnCommonCoefficientData

/-- A transverse factorization at a prescribed positive Hahn scale.  In
contrast with `TransverseScale`, the residue normal jet may vanish. -/
structure TransverseFactor
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k) where
  delta : ℚ
  hdelta : 0 < delta
  Xn : GCD369CubeHahnRegular k
  Yn : GCD369CubeHahnRegular k
  Zn : GCD369CubeHahnRegular k
  hnormal2 : D.normal2 = monomial delta hdelta.le * Xn
  hnormal1 : D.normal1 = monomial delta hdelta.le * Yn
  hnormal0 : D.normal0 = monomial delta hdelta.le * Zn

/-- Forget the nonzero-residue condition on an intrinsic transverse scale. -/
def TransverseScale.factor
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale) :
    D.TransverseFactor where
  delta := T.delta
  hdelta := T.hdelta
  Xn := T.Xn
  Yn := T.Yn
  Zn := T.Zn
  hnormal2 := T.hnormal2
  hnormal1 := T.hnormal1
  hnormal0 := T.hnormal0

/-- Factor all three normal coordinates at a positive scale bounded by each
of their Hahn orders. -/
noncomputable def transverseFactorOfBounds
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k) (delta : ℚ)
    (hdelta : 0 < delta)
    (h2 : (↑delta : WithTop ℚ) ≤ D.normal2.1.orderTop)
    (h1 : (↑delta : WithTop ℚ) ≤ D.normal1.1.orderTop)
    (h0 : (↑delta : WithTop ℚ) ≤ D.normal0.1.orderTop) :
    D.TransverseFactor where
  delta := delta
  hdelta := hdelta
  Xn := shift D.normal2 delta h2
  Yn := shift D.normal1 delta h1
  Zn := shift D.normal0 delta h0
  hnormal2 := (monomial_mul_shift D.normal2 delta hdelta.le h2).symm
  hnormal1 := (monomial_mul_shift D.normal1 delta hdelta.le h1).symm
  hnormal0 := (monomial_mul_shift D.normal0 delta hdelta.le h0).symm

/-- Reconstruct the lower three scaled coefficients from a prescribed
transverse factor. -/
theorem TransverseFactor.regular2_eq
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor) :
    D.faber.scale.regular2 = D.cubicU ^ 2 +
      T.Xn * monomial T.delta T.hdelta.le := by
  have hn := T.hnormal2
  dsimp only [normal2] at hn
  linear_combination hn

theorem TransverseFactor.regular1_eq
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor) :
    D.faber.scale.regular1 = 2 * D.cubicU * D.cubicV +
      T.Yn * monomial T.delta T.hdelta.le := by
  have hn := T.hnormal1
  dsimp only [normal1] at hn
  linear_combination hn

theorem TransverseFactor.regular0_eq
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor) :
    D.faber.scale.regular0 = D.cubicV ^ 2 +
      T.Zn * monomial T.delta T.hdelta.le := by
  have hn := T.hnormal0
  dsimp only [normal0] at hn
  linear_combination hn

/-- Exact first zero-high numerator identity at a prescribed transverse
scale. -/
theorem TransverseFactor.zeroHighN1Expansion
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor) :
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
theorem TransverseFactor.zeroHighN2Expansion
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor) :
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

/-- Exact third zero-high numerator identity, including its cubic-order
remainder. -/
theorem TransverseFactor.zeroHighN3Expansion
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor) :
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

/-- Exact fourth zero-high numerator identity, including its cubic-order
remainder. -/
theorem TransverseFactor.zeroHighN4Expansion
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor) :
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

/-- The coefficient at twice the prescribed transverse scale is the first
universal normal row on the residue jet. -/
theorem TransverseFactor.zeroHighN1Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor) :
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
theorem TransverseFactor.zeroHighN2Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor) :
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

/-- Coefficient form of the third universal normal row; its cubic remainder
is strictly above twice a positive scale. -/
theorem TransverseFactor.zeroHighN3Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor) :
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
theorem TransverseFactor.zeroHighN4Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor) :
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

end GCD369CubeHahnCommonCoefficientData

#print axioms GCD369CubeHahnCommonCoefficientData.TransverseScale.factor
#print axioms GCD369CubeHahnCommonCoefficientData.transverseFactorOfBounds
#print axioms GCD369CubeHahnCommonCoefficientData.TransverseFactor.zeroHighN4Coeff
