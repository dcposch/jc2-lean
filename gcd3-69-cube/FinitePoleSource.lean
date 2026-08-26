import WeightedPole

noncomputable section

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

namespace GCD369CubePolynomialSource

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

end GCD369CubePolynomialSource

#print axioms GCD369CubeHahnRegular.ofRatFuncConstant
#print axioms GCD369CubePolynomialSource.finiteFaberPoleData
#print axioms GCD369CubePolynomialSource.finiteLeadingFaberSource
