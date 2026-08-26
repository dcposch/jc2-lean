import WeightedPole

noncomputable section
open Polynomial

/-! # Finite-place pole data from a literal polynomial source

This file connects the exact finite-place Hahn expansion of the normalized
polynomial source to the weighted leading-component analysis.  Whenever one
of the five low normalized sextic coefficients has a pole, the literal Faber
constants and first integrals supply all regular parameters required by
`GCD369CubeHahnFaberPoleData`.
-/

/-- A ground-field constant, expanded at a finite place, is an element of the
regular Hahn local ring. -/
noncomputable def GCD369CubeHahnRegular.ofRatFuncConstant
    {k : Type*} [Field k] (a c : k) : GCD369CubeHahnRegular k := by
  refine ⟨GCD369CubeRatFuncHahnAt a (algebraMap k (RatFunc k) c), ?_⟩
  rw [RatFunc.algebraMap_eq_C, GCD369CubeRatFuncHahnAt_C]
  change (↑(0 : ℚ) : WithTop ℚ) ≤ (HahnSeries.single 0 c).orderTop
  exact HahnSeries.orderTop_single_le

/-- A rational function identified with a ground-field constant has a
regular finite-place Hahn expansion. -/
noncomputable def GCD369CubeHahnRegular.ofRatFuncEqConstant
    {k : Type*} [Field k] (a : k) (r : RatFunc k) (c : k)
    (h : r = algebraMap k (RatFunc k) c) : GCD369CubeHahnRegular k := by
  refine ⟨GCD369CubeRatFuncHahnAt a r, ?_⟩
  rw [h]
  exact (GCD369CubeHahnRegular.ofRatFuncConstant a c).property

/-- The constant Hahn coefficient of an embedded polynomial at `a` is its
ordinary value at `a`. -/
theorem GCD369CubeRatFuncHahnAt_polynomial_coeff_zero
    {k : Type*} [Field k] (a : k) (p : k[X]) :
    (GCD369CubeRatFuncHahnAt a
      (algebraMap k[X] (RatFunc k) p)).coeff 0 = p.eval a := by
  rw [GCD369CubeRatFuncHahnAt_algebraMap,
    Polynomial.algebraMap_hahnSeries_apply]
  change (HahnSeries.ofPowerSeries ℚ k
    (↑(Polynomial.taylor a p) : PowerSeries k)).coeff ((0 : ℕ) : ℚ) = _
  rw [HahnSeries.ofPowerSeries_apply_coeff]
  simp [Polynomial.taylor_coeff_zero]

/-- If an embedded polynomial does not vanish at the center, its exact Hahn
expansion has order zero. -/
theorem GCD369CubeRatFuncHahnAt_polynomial_order_eq_zero
    {k : Type*} [Field k] (a : k) (p : k[X]) (hp : p.eval a ≠ 0) :
    (GCD369CubeRatFuncHahnAt a
      (algebraMap k[X] (RatFunc k) p)).order = 0 := by
  let x := GCD369CubeRatFuncHahnAt a
    (algebraMap k[X] (RatFunc k) p)
  have hcoeff : x.coeff 0 ≠ 0 := by
    simpa only [x, GCD369CubeRatFuncHahnAt_polynomial_coeff_zero] using hp
  have hle : x.order ≤ 0 := HahnSeries.order_le_of_coeff_ne_zero hcoeff
  have hge : (0 : ℚ) ≤ x.order :=
    HahnSeries.zero_le_orderTop_iff.mp
      (GCD369CubeRatFuncHahnAt_algebraMap_orderTop_nonneg a p)
  exact le_antisymm hle hge

set_option maxRecDepth 10000 in
/-- The terminal Faber expression preserves the regular Hahn local ring.
The only division is by its fixed nonzero scalar denominator. -/
theorem GCD369CubeFaberR5_mem_hahnRegular
    {k : Type*} [Field k]
    (a0 a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1 :
      GCD369CubeHahnRegular k) :
    GCD369CubeFaberR5
      (a0 : HahnSeries ℚ k) a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1 ∈
        GCD369CubeHahnRegular k := by
  rw [GCD369CubeFaberR5_eq_fullN5_div, div_eq_mul_inv]
  apply (GCD369CubeHahnRegular k).mul_mem
  · change (↑(GCD369CubeFaberFullN5
      a0 a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1) : HahnSeries ℚ k) ∈
        GCD369CubeHahnRegular k
    exact (GCD369CubeFaberFullN5
      a0 a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1).property
  · change (↑(0 : ℚ) : WithTop ℚ) ≤
      ((13436928 : HahnSeries ℚ k)⁻¹).orderTop
    change (↑(0 : ℚ) : WithTop ℚ) ≤
      ((HahnSeries.C (13436928 : k))⁻¹).orderTop
    rw [← map_inv₀]
    exact HahnSeries.orderTop_single_le

namespace GCD369CubePolynomialSource

/-- At the unique zero forced by the nonconstant primitive, the terminal
Faber invariant has a genuine finite-place pole. -/
theorem hahnAt_terminalFaberInvariant_order_neg
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k) (m : ℕ)
    (hm : 2 ≤ m)
    (hdenominator :
      S.faberPrimitiveData.denominator =
        Polynomial.C S.faberPrimitiveData.denominator.leadingCoeff *
          (Polynomial.X - Polynomial.C a) ^ (m - 1)) :
    (GCD369CubeRatFuncHahnAt a S.terminalFaberInvariant).order < 0 := by
  let P := S.faberPrimitiveData
  let H := GCD369CubeRatFuncHahnAt a
  have hdeneval : P.denominator.eval a = 0 := by
    rw [show P.denominator =
      Polynomial.C P.denominator.leadingCoeff *
        (Polynomial.X - Polynomial.C a) ^ (m - 1) by
      exact hdenominator]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_X]
    have hm1 : m - 1 ≠ 0 := by omega
    simp [hm1]
  have hnumeval : P.numerator.eval a ≠ 0 := by
    intro hnum
    exact (P.hreduced a hnum) hdeneval
  have hnumorder :
      (H (algebraMap k[X] (RatFunc k) P.numerator)).order = 0 :=
    GCD369CubeRatFuncHahnAt_polynomial_order_eq_zero a P.numerator hnumeval
  have hdenH :
      H (algebraMap k[X] (RatFunc k) P.denominator) =
        HahnSeries.single ((m - 1 : ℕ) : ℚ)
          P.denominator.leadingCoeff := by
    calc
      H (algebraMap k[X] (RatFunc k) P.denominator) =
          H (algebraMap k[X] (RatFunc k)
            (Polynomial.C P.denominator.leadingCoeff *
              (Polynomial.X - Polynomial.C a) ^ (m - 1))) := by
        apply congrArg H
        exact congrArg (algebraMap k[X] (RatFunc k)) hdenominator
      _ = HahnSeries.single ((m - 1 : ℕ) : ℚ)
          P.denominator.leadingCoeff :=
        GCD369CubeRatFuncHahnAt_polynomial_monomial
          a P.denominator.leadingCoeff (m - 1)
  have hlead : P.denominator.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr P.hdenominator
  have hdenne : H (algebraMap k[X] (RatFunc k) P.denominator) ≠ 0 := by
    rw [hdenH]
    exact HahnSeries.single_ne_zero hlead
  have hdenorder :
      (H (algebraMap k[X] (RatFunc k) P.denominator)).order =
        ((m - 1 : ℕ) : ℚ) := by
    rw [hdenH, HahnSeries.order_single hlead]
  have hnumne : H (algebraMap k[X] (RatFunc k) P.numerator) ≠ 0 := by
    apply HahnSeries.ne_zero_of_coeff_ne_zero
    rw [GCD369CubeRatFuncHahnAt_polynomial_coeff_zero]
    exact hnumeval
  have hinvorder :
      (H (algebraMap k[X] (RatFunc k) P.denominator))⁻¹.order =
        -(H (algebraMap k[X] (RatFunc k) P.denominator)).order := by
    have hmul := HahnSeries.order_mul (inv_ne_zero hdenne) hdenne
    rw [inv_mul_cancel₀ hdenne, HahnSeries.order_one] at hmul
    linarith
  have hvalue := congrArg H P.hvalue
  rw [_root_.map_div₀] at hvalue
  simp only [terminalFaberInvariant]
  rw [hvalue, div_eq_mul_inv,
    HahnSeries.order_mul hnumne (inv_ne_zero hdenne), hinvorder,
    hnumorder, hdenorder]
  have hmpos : (0 : ℚ) < ((m - 1 : ℕ) : ℚ) := by
    exact_mod_cast (show 0 < m - 1 by omega)
  linarith

/-- A nonconstant polynomial cube root supplies a unique finite place at
which the terminal Faber invariant is polar. -/
theorem finiteTerminalFaberPole_of_nonconstant
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : 0 < S.s.natDegree) :
    ∃ a : k, ∃ m : ℕ, 2 ≤ m ∧
      S.s = Polynomial.C S.s.leadingCoeff *
        (Polynomial.X - Polynomial.C a) ^ m ∧
      S.faberPrimitiveData.denominator =
        Polynomial.C S.faberPrimitiveData.denominator.leadingCoeff *
          (Polynomial.X - Polynomial.C a) ^ (m - 1) ∧
      (GCD369CubeRatFuncHahnAt a S.terminalFaberInvariant).order < 0 := by
  obtain ⟨a, m, hm, hs, hden⟩ :=
    S.faberPrimitive_nonconstantCore hsdegree
  exact ⟨a, m, hm, hs, hden,
    S.hahnAt_terminalFaberInvariant_order_neg a m hm hden⟩

/-- A pole of the terminal Faber invariant forces a pole in at least one of
the five normalized sextic coefficients: all higher Faber parameters are
ground-field constants, and the explicit terminal expression preserves the
regular local ring. -/
theorem finiteNormalizedCoeffPole_of_terminalPole
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hterminal :
      (GCD369CubeRatFuncHahnAt a S.terminalFaberInvariant).order < 0) :
    (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
    (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
    (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
    (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
    (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0 := by
  by_contra hpole
  simp only [not_or] at hpole
  rcases hpole with ⟨h0, h1, h2, h3, h4⟩
  let H := GCD369CubeRatFuncHahnAt a
  let N := S.faberNormalForm
  let P := S.faberConstantParameters
  let a0r : GCD369CubeHahnRegular k :=
    ⟨H (S.normalizedP.coeff 0),
      HahnSeries.zero_le_orderTop_iff.mpr (le_of_not_gt h0)⟩
  let a1r : GCD369CubeHahnRegular k :=
    ⟨H (S.normalizedP.coeff 1),
      HahnSeries.zero_le_orderTop_iff.mpr (le_of_not_gt h1)⟩
  let a2r : GCD369CubeHahnRegular k :=
    ⟨H (S.normalizedP.coeff 2),
      HahnSeries.zero_le_orderTop_iff.mpr (le_of_not_gt h2)⟩
  let a3r : GCD369CubeHahnRegular k :=
    ⟨H (S.normalizedP.coeff 3),
      HahnSeries.zero_le_orderTop_iff.mpr (le_of_not_gt h3)⟩
  let a4r : GCD369CubeHahnRegular k :=
    ⟨H (S.normalizedP.coeff 4),
      HahnSeries.zero_le_orderTop_iff.mpr (le_of_not_gt h4)⟩
  let dr := GCD369CubeHahnRegular.ofRatFuncEqConstant a N.d P.d P.hd
  let c7r := GCD369CubeHahnRegular.ofRatFuncEqConstant a N.c7 P.c7 P.hc7
  let c5r := GCD369CubeHahnRegular.ofRatFuncEqConstant a N.c5 P.c5 P.hc5
  let c4r := GCD369CubeHahnRegular.ofRatFuncEqConstant a N.c4 P.c4 P.hc4
  let c3r := GCD369CubeHahnRegular.ofRatFuncEqConstant a N.c3 P.c3 P.hc3
  let c2r := GCD369CubeHahnRegular.ofRatFuncEqConstant a N.c2 P.c2 P.hc2
  let c1r := GCD369CubeHahnRegular.ofRatFuncEqConstant a N.c1 P.c1 P.hc1
  have hregular := GCD369CubeFaberR5_mem_hahnRegular
    a0r a1r a2r a3r a4r dr c7r c5r c4r c3r c2r c1r
  have hmap := GCD369CubeFaberR5_map H
    (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
    (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
    (S.normalizedP.coeff 4)
    N.d N.c7 N.c5 N.c4 N.c3 N.c2 N.c1
  have hterminalMap :
      H S.terminalFaberInvariant =
        GCD369CubeFaberR5
          (H (S.normalizedP.coeff 0)) (H (S.normalizedP.coeff 1))
          (H (S.normalizedP.coeff 2)) (H (S.normalizedP.coeff 3))
          (H (S.normalizedP.coeff 4))
          (H N.d) (H N.c7) (H N.c5) (H N.c4)
          (H N.c3) (H N.c2) (H N.c1) := by
    simpa only [terminalFaberInvariant] using hmap
  have hregularTerminal :
      (↑(0 : ℚ) : WithTop ℚ) ≤ (H S.terminalFaberInvariant).orderTop := by
    rw [hterminalMap]
    exact hregular
  exact (not_lt_of_ge
    (HahnSeries.zero_le_orderTop_iff.mp hregularTerminal)) hterminal

/-- Thus every literal source with nonconstant cube root supplies the finite
low-coefficient pole hypothesis used by `finiteFaberPoleData`. -/
theorem finiteNormalizedCoeffPole_of_nonconstant
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : 0 < S.s.natDegree) :
    ∃ a : k,
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0 := by
  obtain ⟨a, _m, _hm, _hs, _hden, hterminal⟩ :=
    S.finiteTerminalFaberPole_of_nonconstant hsdegree
  exact ⟨a, S.finiteNormalizedCoeffPole_of_terminalPole a hterminal⟩

/-- At a finite place where at least one normalized sextic coefficient has a
pole, a literal polynomial source canonically produces the full weighted
Faber pole packet. -/
noncomputable def finiteFaberPoleData
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0) :
    GCD369CubeHahnFaberPoleData k := by
  let H := GCD369CubeRatFuncHahnAt a
  let N := S.faberNormalForm
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  let T := GCD369CubeHahnPoleScale.ofSomePole
    (H (S.normalizedP.coeff 0)) (H (S.normalizedP.coeff 1))
    (H (S.normalizedP.coeff 2)) (H (S.normalizedP.coeff 3))
    (H (S.normalizedP.coeff 4)) hpole
  have hr1src :
      GCD369CubeFaberR1
        (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
        (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
        (S.normalizedP.coeff 4)
        (algebraMap k (RatFunc k) P.d)
        (algebraMap k (RatFunc k) P.c7)
        (algebraMap k (RatFunc k) P.c5)
        (algebraMap k (RatFunc k) P.c4)
        (algebraMap k (RatFunc k) P.c3)
        (algebraMap k (RatFunc k) P.c2)
        (algebraMap k (RatFunc k) P.c1) =
      algebraMap k (RatFunc k) R.rho1 := by
    simpa only [← P.hd, ← P.hc7, ← P.hc5, ← P.hc4, ← P.hc3,
      ← P.hc2, ← P.hc1] using R.hrho1
  have hr2src :
      GCD369CubeFaberR2
        (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
        (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
        (S.normalizedP.coeff 4)
        (algebraMap k (RatFunc k) P.d)
        (algebraMap k (RatFunc k) P.c7)
        (algebraMap k (RatFunc k) P.c5)
        (algebraMap k (RatFunc k) P.c4)
        (algebraMap k (RatFunc k) P.c3)
        (algebraMap k (RatFunc k) P.c2)
        (algebraMap k (RatFunc k) P.c1) =
      algebraMap k (RatFunc k) R.rho2 := by
    simpa only [← P.hd, ← P.hc7, ← P.hc5, ← P.hc4, ← P.hc3,
      ← P.hc2, ← P.hc1] using R.hrho2
  have hr3src :
      GCD369CubeFaberR3
        (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
        (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
        (S.normalizedP.coeff 4)
        (algebraMap k (RatFunc k) P.d)
        (algebraMap k (RatFunc k) P.c7)
        (algebraMap k (RatFunc k) P.c5)
        (algebraMap k (RatFunc k) P.c4)
        (algebraMap k (RatFunc k) P.c3)
        (algebraMap k (RatFunc k) P.c2)
        (algebraMap k (RatFunc k) P.c1) =
      algebraMap k (RatFunc k) R.rho3 := by
    simpa only [← P.hd, ← P.hc7, ← P.hc5, ← P.hc4, ← P.hc3,
      ← P.hc2, ← P.hc1] using R.hrho3
  have hr4src :
      GCD369CubeFaberR4
        (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
        (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
        (S.normalizedP.coeff 4)
        (algebraMap k (RatFunc k) P.d)
        (algebraMap k (RatFunc k) P.c7)
        (algebraMap k (RatFunc k) P.c5)
        (algebraMap k (RatFunc k) P.c4)
        (algebraMap k (RatFunc k) P.c3)
        (algebraMap k (RatFunc k) P.c2)
        (algebraMap k (RatFunc k) P.c1) =
      algebraMap k (RatFunc k) R.rho4 := by
    simpa only [← P.hd, ← P.hc7, ← P.hc5, ← P.hc4, ← P.hc3,
      ← P.hc2, ← P.hc1] using R.hrho4
  refine {
    scale := T
    d := GCD369CubeHahnRegular.ofRatFuncConstant a P.d
    c7 := GCD369CubeHahnRegular.ofRatFuncConstant a P.c7
    c5 := GCD369CubeHahnRegular.ofRatFuncConstant a P.c5
    c4 := GCD369CubeHahnRegular.ofRatFuncConstant a P.c4
    c3 := GCD369CubeHahnRegular.ofRatFuncConstant a P.c3
    c2 := GCD369CubeHahnRegular.ofRatFuncConstant a P.c2
    c1 := GCD369CubeHahnRegular.ofRatFuncConstant a P.c1
    rho1 := GCD369CubeHahnRegular.ofRatFuncConstant a R.rho1
    rho2 := GCD369CubeHahnRegular.ofRatFuncConstant a R.rho2
    rho3 := GCD369CubeHahnRegular.ofRatFuncConstant a R.rho3
    rho4 := GCD369CubeHahnRegular.ofRatFuncConstant a R.rho4
    hr1 := ?_
    hr2 := ?_
    hr3 := ?_
    hr4 := ?_
  }
  · change GCD369CubeFaberR1
      (H (S.normalizedP.coeff 0)) (H (S.normalizedP.coeff 1))
      (H (S.normalizedP.coeff 2)) (H (S.normalizedP.coeff 3))
      (H (S.normalizedP.coeff 4))
      (H (algebraMap k (RatFunc k) P.d))
      (H (algebraMap k (RatFunc k) P.c7))
      (H (algebraMap k (RatFunc k) P.c5))
      (H (algebraMap k (RatFunc k) P.c4))
      (H (algebraMap k (RatFunc k) P.c3))
      (H (algebraMap k (RatFunc k) P.c2))
      (H (algebraMap k (RatFunc k) P.c1)) =
      H (algebraMap k (RatFunc k) R.rho1)
    exact (GCD369CubeFaberR_map H _ _ _ _ _ _ _ _ _ _ _ _).1.symm.trans
      (congrArg H hr1src)
  · change GCD369CubeFaberR2
      (H (S.normalizedP.coeff 0)) (H (S.normalizedP.coeff 1))
      (H (S.normalizedP.coeff 2)) (H (S.normalizedP.coeff 3))
      (H (S.normalizedP.coeff 4))
      (H (algebraMap k (RatFunc k) P.d))
      (H (algebraMap k (RatFunc k) P.c7))
      (H (algebraMap k (RatFunc k) P.c5))
      (H (algebraMap k (RatFunc k) P.c4))
      (H (algebraMap k (RatFunc k) P.c3))
      (H (algebraMap k (RatFunc k) P.c2))
      (H (algebraMap k (RatFunc k) P.c1)) =
      H (algebraMap k (RatFunc k) R.rho2)
    exact (GCD369CubeFaberR_map H _ _ _ _ _ _ _ _ _ _ _ _).2.1.symm.trans
      (congrArg H hr2src)
  · change GCD369CubeFaberR3
      (H (S.normalizedP.coeff 0)) (H (S.normalizedP.coeff 1))
      (H (S.normalizedP.coeff 2)) (H (S.normalizedP.coeff 3))
      (H (S.normalizedP.coeff 4))
      (H (algebraMap k (RatFunc k) P.d))
      (H (algebraMap k (RatFunc k) P.c7))
      (H (algebraMap k (RatFunc k) P.c5))
      (H (algebraMap k (RatFunc k) P.c4))
      (H (algebraMap k (RatFunc k) P.c3))
      (H (algebraMap k (RatFunc k) P.c2))
      (H (algebraMap k (RatFunc k) P.c1)) =
      H (algebraMap k (RatFunc k) R.rho3)
    exact (GCD369CubeFaberR_map H _ _ _ _ _ _ _ _ _ _ _ _).2.2.1.symm.trans
      (congrArg H hr3src)
  · change GCD369CubeFaberR4
      (H (S.normalizedP.coeff 0)) (H (S.normalizedP.coeff 1))
      (H (S.normalizedP.coeff 2)) (H (S.normalizedP.coeff 3))
      (H (S.normalizedP.coeff 4))
      (H (algebraMap k (RatFunc k) P.d))
      (H (algebraMap k (RatFunc k) P.c7))
      (H (algebraMap k (RatFunc k) P.c5))
      (H (algebraMap k (RatFunc k) P.c4))
      (H (algebraMap k (RatFunc k) P.c3))
      (H (algebraMap k (RatFunc k) P.c2))
      (H (algebraMap k (RatFunc k) P.c1)) =
      H (algebraMap k (RatFunc k) R.rho4)
    exact (GCD369CubeFaberR_map H _ _ _ _ _ _ _ _ _ _ _ _).2.2.2.symm.trans
      (congrArg H hr4src)

/-- The same finite pole therefore produces the exact nonzero leading Faber
source consumed by the common-cubic/DS classification. -/
noncomputable def finiteLeadingFaberSource
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0) :
    GCD369CubeLeadingFaberSource k :=
  (S.finiteFaberPoleData a hpole).toLeadingFaberSource

/-- A nonconstant literal polynomial source therefore supplies a complete
finite weighted Faber pole packet. -/
theorem finiteFaberPoleData_nonempty_of_nonconstant
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : 0 < S.s.natDegree) :
    Nonempty (GCD369CubeHahnFaberPoleData k) := by
  obtain ⟨a, hpole⟩ := S.finiteNormalizedCoeffPole_of_nonconstant hsdegree
  exact ⟨S.finiteFaberPoleData a hpole⟩

/-- In particular the nonconstant source reaches the exact nonzero leading
Faber component classified into the common-cubic and DS branches. -/
theorem finiteLeadingFaberSource_nonempty_of_nonconstant
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : 0 < S.s.natDegree) :
    Nonempty (GCD369CubeLeadingFaberSource k) := by
  obtain ⟨a, hpole⟩ := S.finiteNormalizedCoeffPole_of_nonconstant hsdegree
  exact ⟨S.finiteLeadingFaberSource a hpole⟩

end GCD369CubePolynomialSource

#print axioms GCD369CubeHahnRegular.ofRatFuncConstant
#print axioms GCD369CubeRatFuncHahnAt_polynomial_order_eq_zero
#print axioms GCD369CubeFaberR5_mem_hahnRegular
#print axioms GCD369CubePolynomialSource.finiteTerminalFaberPole_of_nonconstant
#print axioms GCD369CubePolynomialSource.finiteNormalizedCoeffPole_of_nonconstant
#print axioms GCD369CubePolynomialSource.finiteFaberPoleData
#print axioms GCD369CubePolynomialSource.finiteLeadingFaberSource
#print axioms
  GCD369CubePolynomialSource.finiteFaberPoleData_nonempty_of_nonconstant
#print axioms
  GCD369CubePolynomialSource.finiteLeadingFaberSource_nonempty_of_nonconstant
