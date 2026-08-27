import InfinityExpansion

noncomputable section

open Polynomial

/-! # The constant-core infinity degree landing at the `rho2` scale

The moving common cubic does not itself have polynomial coefficients after
weighted rescaling.  Its three normal coordinates nevertheless do: they are
the weighted infinity expansions of the literal polynomial corrections

`a2 - (a4 / 2)^2`, `a1 - 2 (a4 / 2) (a3 / 2)`, and
`a0 - (a3 / 2)^2`.

Consequently a nonzero transverse residue at order `delta` records the exact
natural degree `w * p - delta`, for weights `w = 4,5,6`.  At a first `rho2`
landing, `3p = 1` and `2 delta = 11p`, giving the three impossible degrees
`-1/2`, `-1/6`, and `1/6`.
-/

/-- A nonzero residue of a shifted weighted polynomial expansion records the
literal degree of that polynomial. -/
theorem GCD369CubeRatFuncHahnAtInfinity_natDegree_eq_weight_mul_sub_delta
    {k : Type*} [Field k]
    (p delta : ℚ) (w : ℕ) (f : k[X])
    (Xn : GCD369CubeHahnRegular k)
    (hscaled :
      (HahnSeries.single p 1) ^ w *
          GCD369CubeRatFuncHahnAtInfinity
            (algebraMap k[X] (RatFunc k) f) =
        HahnSeries.single delta 1 * Xn.1)
    (hlead : GCD369CubeHahnRegular.constantCoeff Xn ≠ 0) :
    (f.natDegree : ℚ) = (w : ℚ) * p - delta := by
  let Hf := GCD369CubeRatFuncHahnAtInfinity
    (algebraMap k[X] (RatFunc k) f)
  have hXn : Xn.1 ≠ 0 := by
    intro hzero
    apply hlead
    change Xn.1.coeff 0 = 0
    rw [hzero]
    rfl
  have hf : f ≠ 0 := by
    intro hzero
    subst f
    simp only [map_zero, mul_zero] at hscaled
    exact (mul_ne_zero (HahnSeries.single_ne_zero one_ne_zero) hXn)
      hscaled.symm
  have hHf : Hf ≠ 0 :=
    GCD369CubeRatFuncHahnAtInfinity_polynomial_ne_zero f hf
  have ht : HahnSeries.single p (1 : k) ≠ 0 :=
    HahnSeries.single_ne_zero one_ne_zero
  have hdelta : HahnSeries.single delta (1 : k) ≠ 0 :=
    HahnSeries.single_ne_zero one_ne_zero
  have hXorder : Xn.1.order = 0 := by
    apply le_antisymm
    · exact HahnSeries.order_le_of_coeff_ne_zero hlead
    · exact HahnSeries.zero_le_orderTop_iff.mp Xn.2
  have horder := congrArg HahnSeries.order hscaled
  rw [HahnSeries.order_mul (pow_ne_zero w ht) hHf,
    HahnSeries.order_pow, HahnSeries.order_single one_ne_zero,
    GCD369CubeRatFuncHahnAtInfinity_order_polynomial f hf,
    HahnSeries.order_mul hdelta hXn,
    HahnSeries.order_single one_ne_zero, hXorder] at horder
  simp only [nsmul_eq_mul, add_zero] at horder
  linarith

namespace GCD369CubePolynomialSource

/-- Literal polynomial underlying the weight-four normal coordinate. -/
noncomputable def constantCoreNormal2Polynomial
    {k : Type*} [Field k] (S : GCD369CubePolynomialSource k) : k[X] :=
  let P := S.constantCoreNormalizedPPolynomial
  P.coeff 2 - (C (2 : k)⁻¹ * P.coeff 4) ^ 2

/-- Literal polynomial underlying the weight-five normal coordinate. -/
noncomputable def constantCoreNormal1Polynomial
    {k : Type*} [Field k] (S : GCD369CubePolynomialSource k) : k[X] :=
  let P := S.constantCoreNormalizedPPolynomial
  P.coeff 1 - 2 * (C (2 : k)⁻¹ * P.coeff 4) *
    (C (2 : k)⁻¹ * P.coeff 3)

/-- Literal polynomial underlying the weight-six normal coordinate. -/
noncomputable def constantCoreNormal0Polynomial
    {k : Type*} [Field k] (S : GCD369CubePolynomialSource k) : k[X] :=
  let P := S.constantCoreNormalizedPPolynomial
  P.coeff 0 - (C (2 : k)⁻¹ * P.coeff 3) ^ 2

/-- The weight-four moving normal coordinate is the scaled infinity
expansion of an actual polynomial. -/
theorem infinity_normal2_polynomial
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0) :
    let D := S.infinityCommonCoefficientData hsdegree
    D.normal2.1 = D.faber.scale.t ^ 4 *
      GCD369CubeRatFuncHahnAtInfinity
        (algebraMap k[X] (RatFunc k) S.constantCoreNormal2Polynomial) := by
  let D := S.infinityCommonCoefficientData hsdegree
  let P := S.constantCoreNormalizedPPolynomial
  have ha2 : D.faber.scale.a2 =
      GCD369CubeRatFuncHahnAtInfinity
        (algebraMap k[X] (RatFunc k) (P.coeff 2)) := by
    change GCD369CubeRatFuncHahnAtInfinity (S.normalizedP.coeff 2) = _
    rw [S.constantCoreNormalizedP_coeff hsdegree 2]
  have ha4 : D.faber.scale.a4 =
      GCD369CubeRatFuncHahnAtInfinity
        (algebraMap k[X] (RatFunc k) (P.coeff 4)) := by
    change GCD369CubeRatFuncHahnAtInfinity (S.normalizedP.coeff 4) = _
    rw [S.constantCoreNormalizedP_coeff hsdegree 4]
  change D.faber.scale.scaled2 -
      (HahnSeries.C (2 : k)⁻¹ * D.faber.scale.scaled4) ^ 2 = _
  rw [GCD369CubeHahnPoleScale.scaled2,
    GCD369CubeHahnPoleScale.scaled4, ha2, ha4]
  dsimp only [constantCoreNormal2Polynomial, P]
  simp only [map_sub, map_pow, map_mul, map_inv₀, map_ofNat,
    RatFunc.algebraMap_C]
  dsimp only [D]
  ring

/-- The weight-five moving normal coordinate is the scaled infinity
expansion of an actual polynomial. -/
theorem infinity_normal1_polynomial
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0) :
    let D := S.infinityCommonCoefficientData hsdegree
    D.normal1.1 = D.faber.scale.t ^ 5 *
      GCD369CubeRatFuncHahnAtInfinity
        (algebraMap k[X] (RatFunc k) S.constantCoreNormal1Polynomial) := by
  let D := S.infinityCommonCoefficientData hsdegree
  let P := S.constantCoreNormalizedPPolynomial
  have ha1 : D.faber.scale.a1 =
      GCD369CubeRatFuncHahnAtInfinity
        (algebraMap k[X] (RatFunc k) (P.coeff 1)) := by
    change GCD369CubeRatFuncHahnAtInfinity (S.normalizedP.coeff 1) = _
    rw [S.constantCoreNormalizedP_coeff hsdegree 1]
  have ha3 : D.faber.scale.a3 =
      GCD369CubeRatFuncHahnAtInfinity
        (algebraMap k[X] (RatFunc k) (P.coeff 3)) := by
    change GCD369CubeRatFuncHahnAtInfinity (S.normalizedP.coeff 3) = _
    rw [S.constantCoreNormalizedP_coeff hsdegree 3]
  have ha4 : D.faber.scale.a4 =
      GCD369CubeRatFuncHahnAtInfinity
        (algebraMap k[X] (RatFunc k) (P.coeff 4)) := by
    change GCD369CubeRatFuncHahnAtInfinity (S.normalizedP.coeff 4) = _
    rw [S.constantCoreNormalizedP_coeff hsdegree 4]
  change D.faber.scale.scaled1 -
      2 * (HahnSeries.C (2 : k)⁻¹ * D.faber.scale.scaled4) *
        (HahnSeries.C (2 : k)⁻¹ * D.faber.scale.scaled3) = _
  rw [GCD369CubeHahnPoleScale.scaled1,
    GCD369CubeHahnPoleScale.scaled3,
    GCD369CubeHahnPoleScale.scaled4, ha1, ha3, ha4]
  dsimp only [constantCoreNormal1Polynomial, P]
  simp only [map_sub, map_mul, map_inv₀, map_ofNat,
    RatFunc.algebraMap_C]
  dsimp only [D]
  ring

/-- The weight-six moving normal coordinate is the scaled infinity
expansion of an actual polynomial. -/
theorem infinity_normal0_polynomial
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0) :
    let D := S.infinityCommonCoefficientData hsdegree
    D.normal0.1 = D.faber.scale.t ^ 6 *
      GCD369CubeRatFuncHahnAtInfinity
        (algebraMap k[X] (RatFunc k) S.constantCoreNormal0Polynomial) := by
  let D := S.infinityCommonCoefficientData hsdegree
  let P := S.constantCoreNormalizedPPolynomial
  have ha0 : D.faber.scale.a0 =
      GCD369CubeRatFuncHahnAtInfinity
        (algebraMap k[X] (RatFunc k) (P.coeff 0)) := by
    change GCD369CubeRatFuncHahnAtInfinity (S.normalizedP.coeff 0) = _
    rw [S.constantCoreNormalizedP_coeff hsdegree 0]
  have ha3 : D.faber.scale.a3 =
      GCD369CubeRatFuncHahnAtInfinity
        (algebraMap k[X] (RatFunc k) (P.coeff 3)) := by
    change GCD369CubeRatFuncHahnAtInfinity (S.normalizedP.coeff 3) = _
    rw [S.constantCoreNormalizedP_coeff hsdegree 3]
  change D.faber.scale.scaled0 -
      (HahnSeries.C (2 : k)⁻¹ * D.faber.scale.scaled3) ^ 2 = _
  rw [GCD369CubeHahnPoleScale.scaled0,
    GCD369CubeHahnPoleScale.scaled3, ha0, ha3]
  dsimp only [constantCoreNormal0Polynomial, P]
  simp only [map_sub, map_pow, map_mul, map_inv₀, map_ofNat,
    RatFunc.algebraMap_C]
  dsimp only [D]
  ring

/-- A first transverse `rho2` landing at infinity reaches one of the three
impossible correction-degree rows.  No auxiliary numerator or denominator
presentation is selected by the caller: the degrees belong to the literal
constant-core normalized source polynomials. -/
theorem infinityConstantPoleDegreeLanding_of_rho2_scale
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hscale :
      3 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p = 1)
    (hdelta :
      2 * T.delta =
        11 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p) :
    GCD369CubeConstantPoleDegreeLanding := by
  let D := S.infinityCommonCoefficientData hsdegree
  rcases T.hleading with hX | hY | hZ
  · let f := S.constantCoreNormal2Polynomial
    let n := f.natDegree
    have hscaled :
        D.faber.scale.t ^ 4 *
            GCD369CubeRatFuncHahnAtInfinity
              (algebraMap k[X] (RatFunc k) f) =
          HahnSeries.single T.delta 1 * T.Xn.1 := by
      rw [← S.infinity_normal2_polynomial hsdegree]
      exact congrArg Subtype.val T.hnormal2
    have hdegree : (n : ℚ) =
        4 * D.faber.scale.p - T.delta :=
      GCD369CubeRatFuncHahnAtInfinity_natDegree_eq_weight_mul_sub_delta
        D.faber.scale.p T.delta 4 f T.Xn hscaled hX
    exact .rho2X n (by
      rw [hdegree]
      dsimp only [D] at hscale hdelta ⊢
      linarith)
  · let f := S.constantCoreNormal1Polynomial
    let n := f.natDegree
    have hscaled :
        D.faber.scale.t ^ 5 *
            GCD369CubeRatFuncHahnAtInfinity
              (algebraMap k[X] (RatFunc k) f) =
          HahnSeries.single T.delta 1 * T.Yn.1 := by
      rw [← S.infinity_normal1_polynomial hsdegree]
      exact congrArg Subtype.val T.hnormal1
    have hdegree : (n : ℚ) =
        5 * D.faber.scale.p - T.delta :=
      GCD369CubeRatFuncHahnAtInfinity_natDegree_eq_weight_mul_sub_delta
        D.faber.scale.p T.delta 5 f T.Yn hscaled hY
    exact .rho2Y n (by
      rw [hdegree]
      dsimp only [D] at hscale hdelta ⊢
      linarith)
  · let f := S.constantCoreNormal0Polynomial
    let n := f.natDegree
    have hscaled :
        D.faber.scale.t ^ 6 *
            GCD369CubeRatFuncHahnAtInfinity
              (algebraMap k[X] (RatFunc k) f) =
          HahnSeries.single T.delta 1 * T.Zn.1 := by
      rw [← S.infinity_normal0_polynomial hsdegree]
      exact congrArg Subtype.val T.hnormal0
    have hdegree : (n : ℚ) =
        6 * D.faber.scale.p - T.delta :=
      GCD369CubeRatFuncHahnAtInfinity_natDegree_eq_weight_mul_sub_delta
        D.faber.scale.p T.delta 6 f T.Zn hscaled hZ
    exact .rho2Z n (by
      rw [hdegree]
      dsimp only [D] at hscale hdelta ⊢
      linarith)

end GCD369CubePolynomialSource

#print axioms
  GCD369CubeRatFuncHahnAtInfinity_natDegree_eq_weight_mul_sub_delta
#print axioms
  GCD369CubePolynomialSource.infinity_normal2_polynomial
#print axioms
  GCD369CubePolynomialSource.infinity_normal1_polynomial
#print axioms
  GCD369CubePolynomialSource.infinity_normal0_polynomial
#print axioms
  GCD369CubePolynomialSource.infinityConstantPoleDegreeLanding_of_rho2_scale
