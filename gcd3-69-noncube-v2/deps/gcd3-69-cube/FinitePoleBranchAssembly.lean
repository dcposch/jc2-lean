import FiniteSimpleSourceStrictPolynomial
import FiniteSimpleSourceTiedPolynomial

/-! # Late singular finite-pole branch assembly

A literal polynomial source and an arbitrary finite low-coefficient pole
already produce canonical Faber constants and a first transverse jet.  On
that jet the existing double-root lift and strict simple-root obstruction
compose without any further load routing: if the first active source scale
meets or exceeds the intrinsic cubic exponent then the recovered coordinate
is the remaining simple root of the singular leading cubic, and the strict
inequality is inconsistent.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- If `3 * delta < p`, the late zero-load split has already forced the
simple-root residue packet, and the source-facing strict obstruction then
excludes it. -/
theorem TransverseScale.simpleRoot_strictLate_inconsistent_from_source
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant D0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hrho1 : F.rho1 = GCD369CubeHahnRegular.constant Rho1)
    (hrho2 : F.rho2 = GCD369CubeHahnRegular.constant Rho2)
    (hrho3 : F.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : F.rho4 = GCD369CubeHahnRegular.constant Rho4)
    (hp : 3 * T.delta < F.scale.p) : False := by
  obtain ⟨r0, hr0, hA0, hu, hv, hY, hZ, hx⟩ :=
    T.source_coordinate_is_simpleRoot_at_or_after_cubic F hscale
      D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4 (le_of_lt hp)
  exact T.factor.simpleRoot_strictLate_inconsistent_from_source F hscale
    D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
    (by simpa only [TransverseScale.factor] using hp)
    r0 (GCD369CubeHahnRegular.constantCoeff T.Xn) hr0 hA0
    (by rw [S.constantCoeff_cubicU]; exact hu)
    (by rw [S.constantCoeff_cubicV]; exact hv)
    hx rfl
    (by simpa only [TransverseScale.factor] using hY)
    (by simpa only [TransverseScale.factor] using hZ)

/-- The late singular branch on a first transverse jet: cubic scale or later
forces the simple-root residue packet, and the strict inequality is then
impossible. -/
theorem TransverseScale.late_simpleRoot_or_strictFalse
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant D0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hrho1 : F.rho1 = GCD369CubeHahnRegular.constant Rho1)
    (hrho2 : F.rho2 = GCD369CubeHahnRegular.constant Rho2)
    (hrho3 : F.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : F.rho4 = GCD369CubeHahnRegular.constant Rho4) :
    (3 * T.delta ≤ F.scale.p →
      let x := GCD369CubeHahnRegular.constantCoeff
        S.normal.sextic.regularX
      ∃ r : k, r ≠ 0 ∧
        GCD369CubeHahnRegular.constantCoeff T.Xn ≠ 0 ∧
        S.u = -3 * r ^ 2 ∧ S.v = 2 * r ^ 3 ∧
        GCD369CubeHahnRegular.constantCoeff T.Yn =
          r * GCD369CubeHahnRegular.constantCoeff T.Xn ∧
        GCD369CubeHahnRegular.constantCoeff T.Zn =
          -2 * r ^ 2 * GCD369CubeHahnRegular.constantCoeff T.Xn ∧
        x = -2 * r) ∧
    (3 * T.delta < F.scale.p → False) := by
  constructor
  · intro hp
    exact T.source_coordinate_is_simpleRoot_at_or_after_cubic F hscale
      D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4 hp
  · intro hp
    exact T.simpleRoot_strictLate_inconsistent_from_source F hscale
      D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4 hp

end GCD369CubeHahnCommonValueData

namespace GCD369CubePolynomialSource

/-- Literal Faber constants instantiate the late singular assembly at an
arbitrary finite low-coefficient pole.  The first transverse jet remains
an assumption; no cubic-scale inequality is required up front. -/
theorem finite_pole_late_simpleRoot_or_strictFalse
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0)
    (T : (S.finiteCommonValueData a hpole).TransverseScale) :
    (3 * T.delta ≤ (S.finiteFaberPoleData a hpole).scale.p →
      let C := S.finiteCommonValueData a hpole
      let x := GCD369CubeHahnRegular.constantCoeff
        C.normal.sextic.regularX
      ∃ r : k, r ≠ 0 ∧
        GCD369CubeHahnRegular.constantCoeff T.Xn ≠ 0 ∧
        C.u = -3 * r ^ 2 ∧ C.v = 2 * r ^ 3 ∧
        GCD369CubeHahnRegular.constantCoeff T.Yn =
          r * GCD369CubeHahnRegular.constantCoeff T.Xn ∧
        GCD369CubeHahnRegular.constantCoeff T.Zn =
          -2 * r ^ 2 * GCD369CubeHahnRegular.constantCoeff T.Xn ∧
        x = -2 * r) ∧
    (3 * T.delta < (S.finiteFaberPoleData a hpole).scale.p → False) := by
  constructor
  · intro hp
    exact S.finite_source_coordinate_is_simpleRoot_at_or_after_cubic
      a hpole T hp
  · intro hp
    exact S.finite_simpleRoot_strictLate_inconsistent_from_source
      a hpole T hp

/-- Once the canonical weight-one parameter vanishes, the singular late
branch is empty both strictly after the cubic scale and at the exact tie. -/
theorem finite_pole_singular_late_inconsistent
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0)
    (T : (S.finiteCommonValueData a hpole).TransverseScale)
    (hd : S.faberConstantParameters.d = 0)
    (hlate : 3 * T.delta ≤ (S.finiteFaberPoleData a hpole).scale.p) :
    False := by
  rcases eq_or_lt_of_le hlate with htie | hstrict
  · exact S.finite_simpleRoot_tied_inconsistent_from_source
      a hpole T hd htie.symm
  · exact S.finite_simpleRoot_strictLate_inconsistent_from_source
      a hpole T hstrict

end GCD369CubePolynomialSource

#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.simpleRoot_strictLate_inconsistent_from_source
#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.late_simpleRoot_or_strictFalse
#print axioms
  GCD369CubePolynomialSource.finite_pole_late_simpleRoot_or_strictFalse
#print axioms
  GCD369CubePolynomialSource.finite_pole_singular_late_inconsistent
