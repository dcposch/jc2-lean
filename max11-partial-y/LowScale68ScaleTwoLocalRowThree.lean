import LowScale68ScaleTwoLocalInitialForms

/-! # The second local initial form for the `(6,8)` scale-two branch

This module extracts the weight-ten face of the second exact first
integral at the finite root of the degree-one square scale.  It discharges
`FirstIntegralThreeLocalTopFaceRoute68` and obtains the actual source-level
equation `topRowThree68 = 0`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LocalRowThree68

variable {k : Type*} [Field k] [CharZero k]

local instance localRowThreeHahnCharZero68 : CharZero (HahnSeries ℚ k) :=
  charZero_of_injective_ringHom
    (HahnSeries.C_injective (R := k) (Γ := ℚ))

/-- Weight-ten part of the second exact first integral. -/
def firstIntegralThreeTopFaceHahn68 (A B C0 D E : HahnSeries ℚ k) :
    HahnSeries ℚ k :=
  weightedMonomial68 (-16 / 243 : k) A B C0 D E 5 0 0 0 0 +
  weightedMonomial68 (4 / 3 : k) A B C0 D E 0 0 0 2 0 +
  weightedMonomial68 (-8 / 9 : k) A B C0 D E 1 0 2 0 0 +
  weightedMonomial68 (-8 / 9 : k) A B C0 D E 0 2 1 0 0 +
  weightedMonomial68 (-8 / 9 : k) A B C0 D E 2 0 0 0 1 +
  weightedMonomial68 (8 / 3 : k) A B C0 D E 0 0 1 0 1 +
  weightedMonomial68 (20 / 27 : k) A B C0 D E 2 2 0 0 0 +
  weightedMonomial68 (40 / 81 : k) A B C0 D E 3 0 1 0 0 +
  weightedMonomial68 (-16 / 9 : k) A B C0 D E 1 1 0 1 0

/-- All terms of the second exact first integral below weight ten. -/
def firstIntegralThreeHigherHahn68
    (L beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k) : HahnSeries ℚ k :=
  weightedMonomial68 zeta A B C0 D E 0 1 0 0 0 +
  weightedMonomial68 (2 * epsilon) A B C0 D E 0 0 1 0 0 +
  weightedMonomial68 (3 * delta) A B C0 D E 0 0 0 1 0 +
  weightedMonomial68 (4 * gamma) A B C0 D E 0 0 0 0 1 +
  weightedMonomial68 (-(35 / 216 : k) * L) A B C0 D E 0 3 0 0 0 +
  weightedMonomial68 (-(2 / 3 : k) * epsilon) A B C0 D E 2 0 0 0 0 +
  weightedMonomial68 (-(2 / 3 : k) * gamma) A B C0 D E 0 2 0 0 0 +
  weightedMonomial68 ((8 / 27 : k) * gamma) A B C0 D E 3 0 0 0 0 +
  weightedMonomial68 (-(35 / 72 : k) * L) A B C0 D E 2 0 0 1 0 +
  weightedMonomial68 (-(5 / 6 : k) * beta) A B C0 D E 1 0 0 1 0 +
  weightedMonomial68 (-(5 / 6 : k) * beta) A B C0 D E 0 1 1 0 0 +
  weightedMonomial68 (-(4 / 3 : k) * gamma) A B C0 D E 1 0 1 0 0 +
  weightedMonomial68 (-(3 / 2 : k) * delta) A B C0 D E 1 1 0 0 0 +
  weightedMonomial68 ((7 / 6 : k) * L) A B C0 D E 0 1 0 0 1 +
  weightedMonomial68 ((7 / 6 : k) * L) A B C0 D E 0 0 1 1 0 +
  weightedMonomial68 ((35 / 72 : k) * beta) A B C0 D E 2 1 0 0 0 +
  weightedMonomial68 ((385 / 1296 : k) * L) A B C0 D E 3 1 0 0 0 +
  weightedMonomial68 (-(35 / 36 : k) * L) A B C0 D E 1 1 1 0 0

/-- Exact decomposition of the second first integral by local weight. -/
theorem firstIntegralThree68_eq_localFaces
    (L beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k) :
    firstIntegralThree68 (HahnSeries.C L) A B C0 D E
        (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta)
        (HahnSeries.C epsilon) (HahnSeries.C zeta) =
      firstIntegralThreeTopFaceHahn68 A B C0 D E +
        firstIntegralThreeHigherHahn68 L beta gamma delta epsilon zeta
          A B C0 D E := by
  simp only [firstIntegralThree68, firstIntegralThreeTopFaceHahn68,
    firstIntegralThreeHigherHahn68, weightedMonomial68]
  simp only [map_mul, map_div₀, map_neg, map_ofNat]
  ring

/-- All strictly sub-weight-ten terms vanish at local exponent `-50`. -/
theorem firstIntegralThreeHigherHahn68_coeff_neg50
    (L beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-10 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-15 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-20 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-25 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-30 : ℚ) : WithTop ℚ) ≤ E.orderTop) :
    (firstIntegralThreeHigherHahn68 L beta gamma delta epsilon zeta
      A B C0 D E).coeff (-50 : ℚ) = 0 := by
  have hA5 : (↑(-2 * (5 : ℚ)) : WithTop ℚ) ≤ A.orderTop := by
    norm_num
    exact hA
  have hB5 : (↑(-3 * (5 : ℚ)) : WithTop ℚ) ≤ B.orderTop := by
    norm_num
    exact hB
  have hC5 : (↑(-4 * (5 : ℚ)) : WithTop ℚ) ≤ C0.orderTop := by
    norm_num
    exact hC
  have hD5 : (↑(-5 * (5 : ℚ)) : WithTop ℚ) ≤ D.orderTop := by
    norm_num
    exact hD
  have hE5 : (↑(-6 * (5 : ℚ)) : WithTop ℚ) ≤ E.orderTop := by
    norm_num
    exact hE
  have hzero (c : k) (aA aB aC aD aE : ℕ)
      (hw : (2 : ℚ) * aA + 3 * aB + 4 * aC + 5 * aD + 6 * aE < 10) :
      (weightedMonomial68 c A B C0 D E aA aB aC aD aE).coeff
          (-50 : ℚ) = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    have h := weightedMonomial68_orderTop_gt c A B C0 D E
      aA aB aC aD aE 5 10 (by norm_num) hA5 hB5 hC5 hD5 hE5 hw
    norm_num at h
    exact h
  have h1 := hzero zeta 0 1 0 0 0 (by norm_num)
  have h2 := hzero (2 * epsilon) 0 0 1 0 0 (by norm_num)
  have h3 := hzero (3 * delta) 0 0 0 1 0 (by norm_num)
  have h4 := hzero (4 * gamma) 0 0 0 0 1 (by norm_num)
  have h5 := hzero (-(35 / 216 : k) * L) 0 3 0 0 0 (by norm_num)
  have h6 := hzero (-(2 / 3 : k) * epsilon) 2 0 0 0 0 (by norm_num)
  have h7 := hzero (-(2 / 3 : k) * gamma) 0 2 0 0 0 (by norm_num)
  have h8 := hzero ((8 / 27 : k) * gamma) 3 0 0 0 0 (by norm_num)
  have h9 := hzero (-(35 / 72 : k) * L) 2 0 0 1 0 (by norm_num)
  have h10 := hzero (-(5 / 6 : k) * beta) 1 0 0 1 0 (by norm_num)
  have h11 := hzero (-(5 / 6 : k) * beta) 0 1 1 0 0 (by norm_num)
  have h12 := hzero (-(4 / 3 : k) * gamma) 1 0 1 0 0 (by norm_num)
  have h13 := hzero (-(3 / 2 : k) * delta) 1 1 0 0 0 (by norm_num)
  have h14 := hzero ((7 / 6 : k) * L) 0 1 0 0 1 (by norm_num)
  have h15 := hzero ((7 / 6 : k) * L) 0 0 1 1 0 (by norm_num)
  have h16 := hzero ((35 / 72 : k) * beta) 2 1 0 0 0 (by norm_num)
  have h17 := hzero ((385 / 1296 : k) * L) 3 1 0 0 0 (by norm_num)
  have h18 := hzero (-(35 / 36 : k) * L) 1 1 1 0 0 (by norm_num)
  simp only [firstIntegralThreeHigherHahn68, HahnSeries.coeff_add,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15, h16, h17, h18, add_zero]

/-- The weight-ten face of the second invariant is the second scalar top
row, with its exact nonzero normalization. -/
theorem firstIntegralThreeTopFaceHahn68_coeff_neg50
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-10 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-15 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-20 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-25 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-30 : ℚ) : WithTop ℚ) ≤ E.orderTop) :
    (firstIntegralThreeTopFaceHahn68 A B C0 D E).coeff (-50 : ℚ) =
      (-4 / 243 : k) * topRowThree68 (A.coeff (-10 : ℚ))
        (B.coeff (-15 : ℚ)) (C0.coeff (-20 : ℚ))
        (D.coeff (-25 : ℚ)) (E.coeff (-30 : ℚ)) := by
  have hA5 : (↑(-2 * (5 : ℚ)) : WithTop ℚ) ≤ A.orderTop := by
    norm_num
    exact hA
  have hB5 : (↑(-3 * (5 : ℚ)) : WithTop ℚ) ≤ B.orderTop := by
    norm_num
    exact hB
  have hC5 : (↑(-4 * (5 : ℚ)) : WithTop ℚ) ≤ C0.orderTop := by
    norm_num
    exact hC
  have hD5 : (↑(-5 * (5 : ℚ)) : WithTop ℚ) ≤ D.orderTop := by
    norm_num
    exact hD
  have hE5 : (↑(-6 * (5 : ℚ)) : WithTop ℚ) ≤ E.orderTop := by
    norm_num
    exact hE
  have h1 := weightedMonomial68_coeff_at_weight
    (-16 / 243 : k) A B C0 D E 5 0 0 0 0 5 hA5 hB5 hC5 hD5 hE5
  have h2 := weightedMonomial68_coeff_at_weight
    (4 / 3 : k) A B C0 D E 0 0 0 2 0 5 hA5 hB5 hC5 hD5 hE5
  have h3 := weightedMonomial68_coeff_at_weight
    (-8 / 9 : k) A B C0 D E 1 0 2 0 0 5 hA5 hB5 hC5 hD5 hE5
  have h4 := weightedMonomial68_coeff_at_weight
    (-8 / 9 : k) A B C0 D E 0 2 1 0 0 5 hA5 hB5 hC5 hD5 hE5
  have h5 := weightedMonomial68_coeff_at_weight
    (-8 / 9 : k) A B C0 D E 2 0 0 0 1 5 hA5 hB5 hC5 hD5 hE5
  have h6 := weightedMonomial68_coeff_at_weight
    (8 / 3 : k) A B C0 D E 0 0 1 0 1 5 hA5 hB5 hC5 hD5 hE5
  have h7 := weightedMonomial68_coeff_at_weight
    (20 / 27 : k) A B C0 D E 2 2 0 0 0 5 hA5 hB5 hC5 hD5 hE5
  have h8 := weightedMonomial68_coeff_at_weight
    (40 / 81 : k) A B C0 D E 3 0 1 0 0 5 hA5 hB5 hC5 hD5 hE5
  have h9 := weightedMonomial68_coeff_at_weight
    (-16 / 9 : k) A B C0 D E 1 1 0 1 0 5 hA5 hB5 hC5 hD5 hE5
  have h1' :
      (weightedMonomial68 (-16 / 243 : k) A B C0 D E 5 0 0 0 0).coeff
          (-50 : ℚ) = (-16 / 243 : k) * (A.coeff (-10 : ℚ)) ^ 5 := by
    convert h1 using 1 <;> norm_num
  have h2' :
      (weightedMonomial68 (4 / 3 : k) A B C0 D E 0 0 0 2 0).coeff
          (-50 : ℚ) = (4 / 3 : k) * (D.coeff (-25 : ℚ)) ^ 2 := by
    convert h2 using 1 <;> norm_num
  have h3' :
      (weightedMonomial68 (-8 / 9 : k) A B C0 D E 1 0 2 0 0).coeff
          (-50 : ℚ) = (-8 / 9 : k) * A.coeff (-10 : ℚ) *
            (C0.coeff (-20 : ℚ)) ^ 2 := by
    convert h3 using 1 <;> norm_num
  have h4' :
      (weightedMonomial68 (-8 / 9 : k) A B C0 D E 0 2 1 0 0).coeff
          (-50 : ℚ) = (-8 / 9 : k) * (B.coeff (-15 : ℚ)) ^ 2 *
            C0.coeff (-20 : ℚ) := by
    convert h4 using 1 <;> norm_num
  have h5' :
      (weightedMonomial68 (-8 / 9 : k) A B C0 D E 2 0 0 0 1).coeff
          (-50 : ℚ) = (-8 / 9 : k) * (A.coeff (-10 : ℚ)) ^ 2 *
            E.coeff (-30 : ℚ) := by
    convert h5 using 1 <;> norm_num
  have h6' :
      (weightedMonomial68 (8 / 3 : k) A B C0 D E 0 0 1 0 1).coeff
          (-50 : ℚ) = (8 / 3 : k) * C0.coeff (-20 : ℚ) *
            E.coeff (-30 : ℚ) := by
    convert h6 using 1 <;> norm_num
  have h7' :
      (weightedMonomial68 (20 / 27 : k) A B C0 D E 2 2 0 0 0).coeff
          (-50 : ℚ) = (20 / 27 : k) * (A.coeff (-10 : ℚ)) ^ 2 *
            (B.coeff (-15 : ℚ)) ^ 2 := by
    convert h7 using 1 <;> norm_num
  have h8' :
      (weightedMonomial68 (40 / 81 : k) A B C0 D E 3 0 1 0 0).coeff
          (-50 : ℚ) = (40 / 81 : k) * (A.coeff (-10 : ℚ)) ^ 3 *
            C0.coeff (-20 : ℚ) := by
    convert h8 using 1 <;> norm_num
  have h9' :
      (weightedMonomial68 (-16 / 9 : k) A B C0 D E 1 1 0 1 0).coeff
          (-50 : ℚ) = (-16 / 9 : k) * A.coeff (-10 : ℚ) *
            B.coeff (-15 : ℚ) * D.coeff (-25 : ℚ) := by
    convert h9 using 1 <;> norm_num
  simp only [firstIntegralThreeTopFaceHahn68, HahnSeries.coeff_add]
  rw [h1', h2', h3', h4', h5', h6', h7', h8', h9']
  simp only [topRowThree68]
  ring

/-- Complete second local initial-form extraction at exponent `-50`. -/
theorem firstIntegralThree68_coeff_neg50
    (L beta gamma delta epsilon zeta : k)
    (A B C0 D E : HahnSeries ℚ k)
    (hA : (↑(-10 : ℚ) : WithTop ℚ) ≤ A.orderTop)
    (hB : (↑(-15 : ℚ) : WithTop ℚ) ≤ B.orderTop)
    (hC : (↑(-20 : ℚ) : WithTop ℚ) ≤ C0.orderTop)
    (hD : (↑(-25 : ℚ) : WithTop ℚ) ≤ D.orderTop)
    (hE : (↑(-30 : ℚ) : WithTop ℚ) ≤ E.orderTop) :
    (firstIntegralThree68 (HahnSeries.C L) A B C0 D E
      (HahnSeries.C beta) (HahnSeries.C gamma) (HahnSeries.C delta)
      (HahnSeries.C epsilon) (HahnSeries.C zeta)).coeff (-50 : ℚ) =
      (-4 / 243 : k) * topRowThree68 (A.coeff (-10 : ℚ))
        (B.coeff (-15 : ℚ)) (C0.coeff (-20 : ℚ))
        (D.coeff (-25 : ℚ)) (E.coeff (-30 : ℚ)) := by
  rw [firstIntegralThree68_eq_localFaces,
    HahnSeries.coeff_add,
    firstIntegralThreeTopFaceHahn68_coeff_neg50 A B C0 D E
      hA hB hC hD hE,
    firstIntegralThreeHigherHahn68_coeff_neg50
      L beta gamma delta epsilon zeta A B C0 D E hA hB hC hD hE,
    add_zero]

/-- The previously isolated second-invariant route is fully discharged. -/
theorem firstIntegralThreeLocalTopFaceRoute68 :
    FirstIntegralThreeLocalTopFaceRoute68 (k := k) := by
  intro L beta gamma delta epsilon zeta A B C0 D E hA hB hC hD hE
  exact firstIntegralThree68_coeff_neg50
    L beta gamma delta epsilon zeta A B C0 D E hA hB hC hD hE

/-- The second genuine local face forced by the square-source integrated
package: its five worst-pole coefficients satisfy `topRowThree68 = 0`. -/
theorem SquareConstantLIntegratedLocalRootData68.topRowThree_zero
    {p q : k[X][X]} {j l : k} {h0 H : k[X]}
    (T : SquareConstantLIntegratedLocalRootData68 p q j h0 l)
    (hp : p.natDegree = 6) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) :
    topRowThree68
        ((ratFuncAtHahn46 T.root T.source.A).coeff (-10 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.B).coeff (-15 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.C0).coeff (-20 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.D).coeff (-25 : ℚ))
        ((ratFuncAtHahn46 T.root T.source.E).coeff (-30 : ℚ)) = 0 := by
  let AH : HahnSeries ℚ k := ratFuncAtHahn46 T.root T.source.A
  let BH : HahnSeries ℚ k := ratFuncAtHahn46 T.root T.source.B
  let CH : HahnSeries ℚ k := ratFuncAtHahn46 T.root T.source.C0
  let DH : HahnSeries ℚ k := ratFuncAtHahn46 T.root T.source.D
  let EH : HahnSeries ℚ k := ratFuncAtHahn46 T.root T.source.E
  obtain ⟨hA, hB, hC, hD, hE⟩ :=
    T.coordinateOrderBounds hp hH hp6
  obtain ⟨i4, i3, hi4, hi3⟩ := integratedFirstIntegrals_exist_ground68
    T.source.A T.source.B T.source.C0 T.source.D T.source.E
      (RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
      l T.source.alpha T.source.beta T.source.gamma T.source.delta
      T.source.epsilon T.source.zeta T.source.eta (by
        simpa only [RatFunc.algebraMap_eq_C] using T.source.bracket_eq)
  have hi3H := congrArg (ratFuncAtHahn46 T.root) hi3
  have hi3H' :
      firstIntegralThree68 (HahnSeries.C l) AH BH CH DH EH
          (HahnSeries.C T.source.beta) (HahnSeries.C T.source.gamma)
          (HahnSeries.C T.source.delta) (HahnSeries.C T.source.epsilon)
          (HahnSeries.C T.source.zeta) = HahnSeries.C i3 := by
    dsimp only [AH, BH, CH, DH, EH]
    simpa only [firstIntegralThree68, map_add, map_sub, map_neg, map_mul,
      map_pow, map_div₀, map_ofNat, map_one, RatFunc.algebraMap_eq_C,
      ratFuncAtHahn46_C] using hi3H
  have hcoeff := congrArg
    (fun x : HahnSeries ℚ k => x.coeff (-50 : ℚ)) hi3H'
  have hconst : (HahnSeries.C i3 : HahnSeries ℚ k).coeff (-50 : ℚ) = 0 := by
    simp [HahnSeries.C_apply]
  rw [hconst] at hcoeff
  have hface := firstIntegralThree68_coeff_neg50
    l T.source.beta T.source.gamma T.source.delta T.source.epsilon
      T.source.zeta AH BH CH DH EH hA hB hC hD hE
  rw [hface] at hcoeff
  have hfactor : (-4 / 243 : k) ≠ 0 := by norm_num
  dsimp only [AH, BH, CH, DH, EH] at hcoeff ⊢
  exact (mul_eq_zero.mp hcoeff).resolve_left hfactor

end LocalRowThree68

#print axioms firstIntegralThree68_eq_localFaces
#print axioms firstIntegralThreeHigherHahn68_coeff_neg50
#print axioms firstIntegralThreeTopFaceHahn68_coeff_neg50
#print axioms firstIntegralThree68_coeff_neg50
#print axioms firstIntegralThreeLocalTopFaceRoute68
#print axioms SquareConstantLIntegratedLocalRootData68.topRowThree_zero

end Max11DegreeRoutes
