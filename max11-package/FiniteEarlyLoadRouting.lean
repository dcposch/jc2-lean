import FiniteRootLift
import FiniteDoubleHahn

/-! # Routing before the first transverse normal

If the canonical first transverse order is strictly later than the
half-`d` scale, factoring the normal coordinates at that half-scale produces
the zero residue jet.  The literal weight-one rows then contradict the
recovered common-cubic root unless the source coefficient `d` vanishes.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- A canonical transverse scale bounds all three normal orders from below. -/
theorem TransverseScale.normal_orderTop_lower
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale) :
    (↑T.delta : WithTop ℚ) ≤ S.normal2.1.orderTop ∧
      (↑T.delta : WithTop ℚ) ≤ S.normal1.1.orderTop ∧
      (↑T.delta : WithTop ℚ) ≤ S.normal0.1.orderTop := by
  constructor
  · rw [T.hnormal2]
    exact GCD369CubeHahnRegular.monomial_mul_orderTop_lower
      T.delta T.hdelta.le T.Xn
  constructor
  · rw [T.hnormal1]
    exact GCD369CubeHahnRegular.monomial_mul_orderTop_lower
      T.delta T.hdelta.le T.Yn
  · rw [T.hnormal0]
    exact GCD369CubeHahnRegular.monomial_mul_orderTop_lower
      T.delta T.hdelta.le T.Zn

/-- If the weight-one load arrives strictly before the canonical transverse
normal, its coefficient must vanish.  This is the source-facing routing
lemma for the strict branch `p < 2 * delta`. -/
theorem TransverseScale.d_eq_zero_before_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (D C7 C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant D)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : F.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : F.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : F.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : F.rho4 = GCD369CubeHahnRegular.constant R4)
    (hbefore : F.scale.p < 2 * T.delta) :
    D = 0 := by
  have hhalf : F.scale.p / 2 < T.delta := by linarith
  obtain ⟨hn2, hn1, hn0⟩ := T.normal_orderTop_lower
  have hb2 : (↑(F.scale.p / 2) : WithTop ℚ) ≤ S.normal2.1.orderTop :=
    (WithTop.coe_le_coe.mpr hhalf.le).trans hn2
  have hb1 : (↑(F.scale.p / 2) : WithTop ℚ) ≤ S.normal1.1.orderTop :=
    (WithTop.coe_le_coe.mpr hhalf.le).trans hn1
  have hb0 : (↑(F.scale.p / 2) : WithTop ℚ) ≤ S.normal0.1.orderTop :=
    (WithTop.coe_le_coe.mpr hhalf.le).trans hn0
  let U := S.transverseFactorOfBounds (F.scale.p / 2)
    (div_pos F.scale.hp (by norm_num)) hb2 hb1 hb0
  have hX : GCD369CubeHahnRegular.constantCoeff U.Xn = 0 := by
    dsimp only [U, transverseFactorOfBounds]
    rw [GCD369CubeHahnRegular.constantCoeff_shift]
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact (WithTop.coe_lt_coe.mpr hhalf).trans_le hn2
  have hY : GCD369CubeHahnRegular.constantCoeff U.Yn = 0 := by
    dsimp only [U, transverseFactorOfBounds]
    rw [GCD369CubeHahnRegular.constantCoeff_shift]
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact (WithTop.coe_lt_coe.mpr hhalf).trans_le hn1
  have hZ : GCD369CubeHahnRegular.constantCoeff U.Zn = 0 := by
    dsimp only [U, transverseFactorOfBounds]
    rw [GCD369CubeHahnRegular.constantCoeff_shift]
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact (WithTop.coe_lt_coe.mpr hhalf).trans_le hn0
  have hrows : GCD369CubeDLeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff U.Xn)
      (GCD369CubeHahnRegular.constantCoeff U.Yn)
      (GCD369CubeHahnRegular.constantCoeff U.Zn) S.u S.v D := by
    simpa only [U] using S.dLeadingFaberRowsAt_of_bounds F hscale
      D C7 C5 C4 C3 C2 C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 hb2 hb1 hb0
  by_contra hD
  have hnocommon := GCD369CubeDLeadingFaberRowsAt_noCommonRoot
    (GCD369CubeHahnRegular.constantCoeff U.Xn)
    (GCD369CubeHahnRegular.constantCoeff U.Yn)
    (GCD369CubeHahnRegular.constantCoeff U.Zn)
    S.u S.v D hD S.hprojective hrows
  apply hnocommon
    (GCD369CubeHahnRegular.constantCoeff S.normal.sextic.regularX)
    S.leadingCubicRoot
  rw [hX, hY, hZ]
  ring

end GCD369CubeHahnCommonValueData

namespace GCD369CubePolynomialSource

/-- At a canonical finite pole, a weight-one load strictly preceding the
first transverse normal is zero. -/
theorem finite_d_eq_zero_before_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (a : k)
    (hpole :
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 0)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 1)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 2)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 3)).order < 0 ∨
      (GCD369CubeRatFuncHahnAt a (S.normalizedP.coeff 4)).order < 0)
    (T : (S.finiteCommonValueData a hpole).TransverseScale)
    (hbefore : (S.finiteFaberPoleData a hpole).scale.p < 2 * T.delta) :
    S.faberConstantParameters.d = 0 := by
  let C := S.finiteCommonValueData a hpole
  let F := S.finiteFaberPoleData a hpole
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  change F.scale.p < 2 * T.delta at hbefore
  exact T.d_eq_zero_before_transverse F rfl
    P.d P.c7 P.c5 P.c4 P.c3 P.c2 P.c1
    R.rho1 R.rho2 R.rho3 R.rho4
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.d)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.c7)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.c5)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.c4)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.c3)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.c2)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a P.c1)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a R.rho1)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a R.rho2)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a R.rho3)
    (GCD369CubeHahnRegular.ofRatFuncConstant_eq_constant a R.rho4)
    hbefore

end GCD369CubePolynomialSource

#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.normal_orderTop_lower
#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.d_eq_zero_before_transverse
#print axioms
  GCD369CubePolynomialSource.finite_d_eq_zero_before_transverse
