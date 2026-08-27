import FiniteCommonSource

noncomputable section
open Polynomial

/-! # Finite-place pole data in the target-normalized gauge

`finiteFaberPoleData` always uses the canonical Faber peeling of its source.
On the `d = 0` stratum the first-target translation produces an explicit
certified normal form with `c₃ = 0` and barred `c₁`.  This file generalizes
the finite pole constructor to an arbitrary certified normal form, then
specializes it to that gauge.  The resulting packet is built from the
translated literal source, so it shares the pole scale of
`(S.targetNormalizedSource).finiteCommonValueData`.
-/

namespace GCD369CubePolynomialSource

/-- At a finite place where at least one normalized sextic coefficient has a
pole, any certified Faber normal form with ground-field constants and first
integrals produces the full weighted Faber pole packet. -/
noncomputable def finiteFaberPoleDataAt
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k)
    (N : GCD369CubeFaberNormalForm
      (S.normalizedP.coeff 0) (S.normalizedP.coeff 1)
      (S.normalizedP.coeff 2) (S.normalizedP.coeff 3)
      (S.normalizedP.coeff 4) S.normalizedQ)
    (P : GCD369CubeFaberConstantParameters N)
    (R : GCD369CubeFaberFirstIntegralConstantsAt S N)
    (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0) :
    GCD369CubeHahnFaberPoleData k := by
  let H := GCD369CubeRatFuncHahnAt a
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

/-- Explicit ground-field representatives of the target-normalized Faber
form: `d = c₃ = 0` and the barred value of `c₁`. -/
noncomputable def targetNormalizedFaberConstantParameters
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k)
    (hd : S.faberConstantParameters.d = 0) :
    GCD369CubeFaberConstantParameters
      (S.targetNormalizedFaberNormalForm hd) where
  d := 0
  c7 := S.faberConstantParameters.c7
  c6 := S.faberConstantParameters.c6
  c5 := S.faberConstantParameters.c5
  c4 := S.faberConstantParameters.c4
  c3 := 0
  c2 := S.faberConstantParameters.c2
  c1 := S.faberConstantParameters.c1 -
    7 * S.faberConstantParameters.c7 *
      S.faberConstantParameters.c3 / 9
  c0 := S.faberConstantParameters.c0 -
    2 * S.faberConstantParameters.c6 *
      S.faberConstantParameters.c3 / 3
  hd := by
    simp [targetNormalizedFaberNormalForm]
  hc7 := by
    simp [targetNormalizedFaberNormalForm]
  hc6 := by
    simp [targetNormalizedFaberNormalForm]
  hc5 := by
    simp [targetNormalizedFaberNormalForm]
  hc4 := by
    simp [targetNormalizedFaberNormalForm]
  hc3 := by
    simp [targetNormalizedFaberNormalForm]
  hc2 := by
    simp [targetNormalizedFaberNormalForm]
  hc1 := by
    simp [targetNormalizedFaberNormalForm]
  hc0 := by
    simp [targetNormalizedFaberNormalForm]

/-- Finite weighted Faber pole packet of the canonical `c₃ = 0` translation,
with the explicit target-normalized constants. -/
noncomputable def finiteTargetNormalizedPoleData
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hd : S.faberConstantParameters.d = 0)
    (hpole :
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 4)).order < 0) :
    GCD369CubeHahnFaberPoleData k :=
  S.targetNormalizedSource.finiteFaberPoleDataAt
    (S.targetNormalizedFaberNormalForm hd)
    (S.targetNormalizedFaberConstantParameters hd)
    (S.targetNormalizedFirstIntegralConstants hd) a hpole

/-- The packet uses the same pole scale as the canonical finite construction
on the translated source, hence the same scale as
`(S.targetNormalizedSource).finiteCommonValueData`. -/
theorem finiteTargetNormalizedPoleData_scale
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hd : S.faberConstantParameters.d = 0)
    (hpole :
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 4)).order < 0) :
    (S.finiteTargetNormalizedPoleData a hd hpole).scale =
      (S.targetNormalizedSource.finiteFaberPoleData a hpole).scale :=
  rfl

theorem finiteTargetNormalizedPoleData_commonScale
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hd : S.faberConstantParameters.d = 0)
    (hpole :
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 4)).order < 0) :
    (S.targetNormalizedSource.finiteCommonValueData a hpole).normal.sextic.scale =
      (S.finiteTargetNormalizedPoleData a hd hpole).scale :=
  rfl

/-- Explicit Hahn fields of the target-normalized packet. -/
theorem finiteTargetNormalizedPoleData_fields
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hd : S.faberConstantParameters.d = 0)
    (hpole :
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 4)).order < 0) :
    let F := S.finiteTargetNormalizedPoleData a hd hpole
    let P := S.faberConstantParameters
    let R := S.targetNormalizedFirstIntegralConstants hd
    F.d = GCD369CubeHahnRegular.ofRatFuncConstant a (0 : k) ∧
    F.c7 = GCD369CubeHahnRegular.ofRatFuncConstant a P.c7 ∧
    F.c5 = GCD369CubeHahnRegular.ofRatFuncConstant a P.c5 ∧
    F.c4 = GCD369CubeHahnRegular.ofRatFuncConstant a P.c4 ∧
    F.c3 = GCD369CubeHahnRegular.ofRatFuncConstant a (0 : k) ∧
    F.c2 = GCD369CubeHahnRegular.ofRatFuncConstant a P.c2 ∧
    F.c1 = GCD369CubeHahnRegular.ofRatFuncConstant a
      (P.c1 - 7 * P.c7 * P.c3 / 9) ∧
    F.rho1 = GCD369CubeHahnRegular.ofRatFuncConstant a R.rho1 ∧
    F.rho2 = GCD369CubeHahnRegular.ofRatFuncConstant a R.rho2 ∧
    F.rho3 = GCD369CubeHahnRegular.ofRatFuncConstant a R.rho3 ∧
    F.rho4 = GCD369CubeHahnRegular.ofRatFuncConstant a R.rho4 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- In particular the vanishing parameters are the zero element of the
regular Hahn local ring. -/
theorem finiteTargetNormalizedPoleData_zero
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hd : S.faberConstantParameters.d = 0)
    (hpole :
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a
        (S.targetNormalizedSource.normalizedP.coeff 4)).order < 0) :
    let F := S.finiteTargetNormalizedPoleData a hd hpole
    F.d = GCD369CubeHahnRegular.constant 0 ∧
    F.c3 = GCD369CubeHahnRegular.constant 0 := by
  dsimp only
  have h := S.finiteTargetNormalizedPoleData_fields a hd hpole
  exact ⟨h.1.trans (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a (0 : k)),
    h.2.2.2.2.1.trans
      (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a (0 : k))⟩

end GCD369CubePolynomialSource

#print axioms GCD369CubePolynomialSource.finiteFaberPoleDataAt
#print axioms
  GCD369CubePolynomialSource.targetNormalizedFaberConstantParameters
#print axioms GCD369CubePolynomialSource.finiteTargetNormalizedPoleData
#print axioms GCD369CubePolynomialSource.finiteTargetNormalizedPoleData_scale
#print axioms
  GCD369CubePolynomialSource.finiteTargetNormalizedPoleData_commonScale
#print axioms GCD369CubePolynomialSource.finiteTargetNormalizedPoleData_fields
#print axioms GCD369CubePolynomialSource.finiteTargetNormalizedPoleData_zero
