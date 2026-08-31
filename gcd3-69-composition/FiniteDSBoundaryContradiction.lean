import FiniteBoundarySource

noncomputable section
open Polynomial

/-! # Finite-pole exclusion of a global Davenport--Stothers sheet

`finiteLeadingComponent_common` already forces every finite polar leading
packet onto a nonzero common cubic.  A global Davenport--Stothers
parametrization of the depressed-sextic coefficients is weighted-homogeneous
of the wrong type: it makes the odd leading coordinates vanish and imposes
`5 a₄² = 8 a₂`.  Transporting those identities to the regular Hahn local
ring produces a vanishing common-cubic pair, which is impossible.

On the zero later-invariant fibre the same identities are the DS branch of
the exact leading classification, so that branch is empty as soon as a
coefficient pole is present.  Combined with the existing common-cubic
vanishing of `r₅`, the whole zero fibre is then terminally empty without an
original-boundary DS witness.
-/

namespace GCD369CubePolynomialSource

/-- Global vanishing of `a₃` together with the DS quadric `5 a₄² = 8 a₂`
cannot occur at a finite coefficient pole: the leading packet would have
to be a common cubic with both coordinates zero. -/
theorem finiteDSRelations_impossible_of_coeff_pole
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0)
    (ha3 : S.normalizedP.coeff 3 = 0)
    (ha42 : 5 * (S.normalizedP.coeff 4) ^ 2 =
      8 * S.normalizedP.coeff 2) : False := by
  let H := GCD369CubeRatFuncHahnAt a
  obtain ⟨u, v, hprojective, hlead4, hlead3, hlead2, _hlead1, _hlead0⟩ :=
    S.finiteLeadingComponent_common a hpole
  rcases S.finiteSexticValueData_source_fields a hpole with
    ⟨_, _, ha2H, ha3H, ha4H, _⟩
  let Sc := (S.finiteSexticValueData a hpole).scale
  have hscaled3 : Sc.scaled3 = 0 := by
    dsimp only [GCD369CubeHahnPoleScale.scaled3]
    rw [ha3H, ha3, map_zero, mul_zero]
  have hleading3 : Sc.leading3 = 0 := by
    change Sc.scaled3.coeff 0 = 0
    rw [hscaled3]
    simp
  have hv : v = 0 := by
    have h2v : (2 : k) * v = 0 := by
      rw [← hlead3, hleading3]
    exact (mul_eq_zero.mp h2v).resolve_left (by norm_num)
  have hmap42 := congrArg H ha42
  simp only [map_mul, map_pow, map_ofNat] at hmap42
  have hscaled42 : 5 * Sc.scaled4 ^ 2 = 8 * Sc.scaled2 := by
    dsimp only [GCD369CubeHahnPoleScale.scaled4,
      GCD369CubeHahnPoleScale.scaled2]
    rw [ha4H, ha2H]
    calc
      5 * (Sc.t ^ 2 * H (S.normalizedP.coeff 4)) ^ 2 =
          Sc.t ^ 4 * (5 * H (S.normalizedP.coeff 4) ^ 2) := by ring
      _ = Sc.t ^ 4 * (8 * H (S.normalizedP.coeff 2)) := by rw [hmap42]
      _ = 8 * (Sc.t ^ 4 * H (S.normalizedP.coeff 2)) := by ring
  have hregular42 :
      (5 : GCD369CubeHahnRegular k) * Sc.regular4 ^ 2 =
        8 * Sc.regular2 := by
    apply Subtype.ext
    exact hscaled42
  have hleading42 :=
    congrArg GCD369CubeHahnRegular.constantCoeff hregular42
  simp only [map_mul, map_pow, map_ofNat] at hleading42
  change 5 * Sc.leading4 ^ 2 = 8 * Sc.leading2 at hleading42
  rw [hlead4, hlead2] at hleading42
  have h12 : (12 : k) * u ^ 2 = 0 := by
    linear_combination hleading42
  have hu : u = 0 :=
    (sq_eq_zero_iff).mp ((mul_eq_zero.mp h12).resolve_left (by norm_num))
  exact hprojective.elim (fun h => h hu) (fun h => h hv)

/-- The five global Davenport--Stothers coefficient identities therefore
cannot occur at a finite coefficient pole. -/
theorem finiteDSParametrization_impossible_of_coeff_pole
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0)
    (lambda : RatFunc k)
    (ha4 : S.normalizedP.coeff 4 = 4 * lambda)
    (ha3 : S.normalizedP.coeff 3 = 0)
    (ha2 : S.normalizedP.coeff 2 = 10 * lambda ^ 2)
    (_ha1 : S.normalizedP.coeff 1 = 0)
    (_ha0 : S.normalizedP.coeff 0 = 6 * lambda ^ 3) : False := by
  have ha42 : 5 * (S.normalizedP.coeff 4) ^ 2 =
      8 * S.normalizedP.coeff 2 := by
    rw [ha4, ha2]
    ring
  exact S.finiteDSRelations_impossible_of_coeff_pole a hpole ha3 ha42

/-- A nonconstant cube root supplies such a pole internally. -/
theorem finiteDSRelations_impossible_of_nonconstant
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k)
    (hsdegree : 0 < S.s.natDegree)
    (ha3 : S.normalizedP.coeff 3 = 0)
    (ha42 : 5 * (S.normalizedP.coeff 4) ^ 2 =
      8 * S.normalizedP.coeff 2) : False := by
  obtain ⟨a, hpole⟩ := S.finiteNormalizedCoeffPole_of_nonconstant hsdegree
  exact S.finiteDSRelations_impossible_of_coeff_pole a hpole ha3 ha42

end GCD369CubePolynomialSource

namespace GCD369CubeLaterInvariantSource

/-- On the zero later-invariant fibre, the DS branch of the exact leading
classification is the five global identities already excluded by a finite
coefficient pole of a matching polynomial source. -/
theorem zero_DS_impossible_of_coeff_pole
    {k : Type*} [Field k] [CharZero k]
    (L : GCD369CubeLaterInvariantSource (RatFunc k))
    (S : GCD369CubePolynomialSource k)
    (ha0 : L.a0 = S.normalizedP.coeff 0)
    (ha1 : L.a1 = S.normalizedP.coeff 1)
    (ha2 : L.a2 = S.normalizedP.coeff 2)
    (ha3 : L.a3 = S.normalizedP.coeff 3)
    (ha4 : L.a4 = S.normalizedP.coeff 4)
    (_hrho3 : L.rho3 = 0) (_hrho4 : L.rho4 = 0)
    (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0)
    (lam : RatFunc k)
    (hlam4 : L.a4 = 4 * lam)
    (hlam3 : L.a3 = 0)
    (hlam2 : L.a2 = 10 * lam ^ 2)
    (hlam1 : L.a1 = 0)
    (hlam0 : L.a0 = 6 * lam ^ 3) : False :=
  S.finiteDSParametrization_impossible_of_coeff_pole a hpole lam
    (ha4.symm.trans hlam4) (ha3.symm.trans hlam3) (ha2.symm.trans hlam2)
    (ha1.symm.trans hlam1) (ha0.symm.trans hlam0)

/-- Consequently the zero later-invariant fibre cannot satisfy a terminal
Keller derivative at a finite coefficient pole.  The common-cubic branch
still collapses by vanishing of `r₅`; the DS branch is the finite-pole
contradiction above, so no original-boundary witness is required. -/
theorem zero_empty_of_coeff_pole
    {k : Type*} [Field k] [CharZero k]
    (L : GCD369CubeLaterInvariantSource (RatFunc k))
    (S : GCD369CubePolynomialSource k)
    (ha0 : L.a0 = S.normalizedP.coeff 0)
    (ha1 : L.a1 = S.normalizedP.coeff 1)
    (ha2 : L.a2 = S.normalizedP.coeff 2)
    (ha3 : L.a3 = S.normalizedP.coeff 3)
    (ha4 : L.a4 = S.normalizedP.coeff 4)
    (hrho3 : L.rho3 = 0) (hrho4 : L.rho4 = 0)
    (j : k) (hj : j ≠ 0) (s : k[X]) (_hs : s ≠ 0)
    (hterminal :
      algebraMap k[X] (RatFunc k) s *
          GCD369CubeRatFuncDerivative
            (GCD369CubeFaberR5
              L.a0 L.a1 L.a2 L.a3 L.a4 0 0 0 0 0 0 0) =
        algebraMap k (RatFunc k) j)
    (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0) :
    False := by
  have hjmap : algebraMap k (RatFunc k) j ≠ 0 := by
    rw [RatFunc.algebraMap_eq_C]
    simpa using RatFunc.C_injective.ne hj
  have hr3zero :
      GCD369CubeFaberR3 L.a0 L.a1 L.a2 L.a3 L.a4 0 0 0 0 0 0 0 = 0 :=
    L.hr3.trans hrho3
  have hr4zero :
      GCD369CubeFaberR4 L.a0 L.a1 L.a2 L.a3 L.a4 0 0 0 0 0 0 0 = 0 :=
    L.hr4.trans hrho4
  rcases GCD369CubeFaberLeadingComponentClassification
      L.a0 L.a1 L.a2 L.a3 L.a4 L.hr1 L.hr2 hr3zero hr4zero with
    hcommon | hds
  · rcases hcommon with ⟨u, v, hLa4, hLa3, hLa2, hLa1, hLa0⟩
    have hr5zero :
        GCD369CubeFaberR5 L.a0 L.a1 L.a2 L.a3 L.a4 0 0 0 0 0 0 0 = 0 := by
      rw [hLa0, hLa1, hLa2, hLa3, hLa4]
      exact (GCD369CubeFaberCommonValues u v).2.2.2.2
    rw [hr5zero, GCD369CubeRatFuncDerivative_zero, mul_zero] at hterminal
    exact hjmap hterminal.symm
  · rcases hds with ⟨lam, hlam4, hlam3, hlam2, hlam1, hlam0⟩
    exact L.zero_DS_impossible_of_coeff_pole S ha0 ha1 ha2 ha3 ha4
      hrho3 hrho4 a hpole lam hlam4 hlam3 hlam2 hlam1 hlam0

end GCD369CubeLaterInvariantSource

#print axioms
  GCD369CubePolynomialSource.finiteDSRelations_impossible_of_coeff_pole
#print axioms
  GCD369CubePolynomialSource.finiteDSParametrization_impossible_of_coeff_pole
#print axioms
  GCD369CubePolynomialSource.finiteDSRelations_impossible_of_nonconstant
#print axioms
  GCD369CubeLaterInvariantSource.zero_DS_impossible_of_coeff_pole
#print axioms
  GCD369CubeLaterInvariantSource.zero_empty_of_coeff_pole
