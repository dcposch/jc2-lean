import InfinityC1Before
import FiniteRho1Extraction
import TargetNormalization
import FiniteTargetNormalizedParameters

/-! # The strict-before weight-ten `rho1` load at infinity

After the source loads through `c1` vanish, the first-integral value `rho1`
is the next load, at weight ten.  If `10p < 2δ`, factoring at `5p` gives a
zero residue normal jet, while the four primitive numerator coefficients
give the arbitrary-`rho1` packet.  Its common-root obstruction kills a
nonzero load.
-/

noncomputable section

namespace GCD369CubeHahnCommonCoefficientData

/-- The four primitive quadratic coefficients with first-row value
`62208 * R` are the arbitrary-`rho1` Faber packet. -/
theorem TransverseFactor.rhoOneBeforeLeadingFaberRowsAt
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (R : k)
    (h1 : (729 * GCD369CubeFaberN1
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 62208 * R)
    (h2 : (2187 * GCD369CubeFaberN2
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h3 : (GCD369CubeFaberN3
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h4 : (6561 * GCD369CubeFaberN4
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0) :
    GCD369CubeRhoOneLeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v R := by
  dsimp [GCD369CubeRhoOneLeadingFaberRowsAt]
  have hc := GCD369CubeFaberCommonNormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v
  dsimp only at hc
  rcases hc with ⟨hc1, hc2, hc3, hc4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc1, ← T.zeroHighN1Coeff]
    exact h1
  · rw [hc2, ← T.zeroHighN2Coeff]
    exact h2
  · rw [hc3, ← T.zeroHighN3Coeff]
    exact h3
  · rw [hc4, ← T.zeroHighN4Coeff]
    exact h4

/-- Coefficient-data lift of the four primitive weight-ten equations to the
arbitrary-`rho1` row packet at the prescribed half-load scale. -/
theorem rho1BeforeLeadingFaberRowsAt_of_bounds
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k)
    (R1 R2 R3 R4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant 0)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant 0)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (hnormal2 : (↑((10 * D.faber.scale.p) / 2) : WithTop ℚ) ≤
      D.normal2.1.orderTop)
    (hnormal1 : (↑((10 * D.faber.scale.p) / 2) : WithTop ℚ) ≤
      D.normal1.1.orderTop)
    (hnormal0 : (↑((10 * D.faber.scale.p) / 2) : WithTop ℚ) ≤
      D.normal0.1.orderTop) :
    let T := D.transverseFactorOfBounds ((10 * D.faber.scale.p) / 2)
      (div_pos (mul_pos (by norm_num) D.faber.scale.hp) (by norm_num))
      hnormal2 hnormal1 hnormal0
    GCD369CubeRhoOneLeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v R1 := by
  dsimp only
  let T := D.transverseFactorOfBounds ((10 * D.faber.scale.p) / 2)
    (div_pos (mul_pos (by norm_num) D.faber.scale.hp) (by norm_num))
    hnormal2 hnormal1 hnormal0
  have hz := D.faber.rho1NCoeff R1 R2 R3 R4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4
  apply T.rhoOneBeforeLeadingFaberRowsAt R1
  · have h := hz.1
    have hTdelta : T.delta = (10 * D.faber.scale.p) / 2 := rfl
    simp only [hTdelta]
    convert h using 1 <;> norm_num <;> ring_nf
  · have h := hz.2.1
    have hTdelta : T.delta = (10 * D.faber.scale.p) / 2 := rfl
    simp only [hTdelta]
    convert h using 1 <;> norm_num <;> ring_nf
  · have h := hz.2.2.1
    have hTdelta : T.delta = (10 * D.faber.scale.p) / 2 := rfl
    simp only [hTdelta]
    convert h using 1 <;> norm_num <;> ring_nf
  · have h := hz.2.2.2
    have hTdelta : T.delta = (10 * D.faber.scale.p) / 2 := rfl
    simp only [hTdelta]
    convert h using 1 <;> norm_num <;> ring_nf

set_option maxHeartbeats 4000000 in
/-- A weight-ten `rho1` load strictly before the first transverse normal
must vanish. -/
theorem TransverseScale.rho1_eq_zero_strict_before
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (R1 R2 R3 R4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant 0)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant 0)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (hbefore : 10 * D.faber.scale.p < 2 * T.delta) :
    R1 = 0 := by
  let e : ℚ := ((10 : ℚ) * D.faber.scale.p) / 2
  have he : 0 < e := by
    dsimp only [e]
    exact div_pos (mul_pos (by norm_num) D.faber.scale.hp) (by norm_num)
  have hedelt : e < T.delta := by
    dsimp only [e]
    linarith
  obtain ⟨hn2, hn1, hn0⟩ := T.normal_orderTop_lower_coeff
  have hb2 : (↑e : WithTop ℚ) ≤ D.normal2.1.orderTop :=
    (WithTop.coe_le_coe.mpr hedelt.le).trans hn2
  have hb1 : (↑e : WithTop ℚ) ≤ D.normal1.1.orderTop :=
    (WithTop.coe_le_coe.mpr hedelt.le).trans hn1
  have hb0 : (↑e : WithTop ℚ) ≤ D.normal0.1.orderTop :=
    (WithTop.coe_le_coe.mpr hedelt.le).trans hn0
  let U := D.transverseFactorOfBounds e he hb2 hb1 hb0
  have hX : GCD369CubeHahnRegular.constantCoeff U.Xn = 0 := by
    dsimp only [U, transverseFactorOfBounds]
    rw [constantCoeff_shift]
    exact HahnSeries.coeff_eq_zero_of_lt_orderTop
      ((WithTop.coe_lt_coe.mpr hedelt).trans_le hn2)
  have hY : GCD369CubeHahnRegular.constantCoeff U.Yn = 0 := by
    dsimp only [U, transverseFactorOfBounds]
    rw [constantCoeff_shift]
    exact HahnSeries.coeff_eq_zero_of_lt_orderTop
      ((WithTop.coe_lt_coe.mpr hedelt).trans_le hn1)
  have hZ : GCD369CubeHahnRegular.constantCoeff U.Zn = 0 := by
    dsimp only [U, transverseFactorOfBounds]
    rw [constantCoeff_shift]
    exact HahnSeries.coeff_eq_zero_of_lt_orderTop
      ((WithTop.coe_lt_coe.mpr hedelt).trans_le hn0)
  have hrows : GCD369CubeRhoOneLeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff U.Xn)
      (GCD369CubeHahnRegular.constantCoeff U.Yn)
      (GCD369CubeHahnRegular.constantCoeff U.Zn) D.u D.v R1 := by
    simpa only [U, e] using D.rho1BeforeLeadingFaberRowsAt_of_bounds
      R1 R2 R3 R4 hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 hb2 hb1 hb0
  by_contra hR1
  have hnocommon := GCD369CubeRhoOneLeadingFaberRowsAt_noCommonRoot
    (GCD369CubeHahnRegular.constantCoeff U.Xn)
    (GCD369CubeHahnRegular.constantCoeff U.Yn)
    (GCD369CubeHahnRegular.constantCoeff U.Zn)
    D.u D.v R1 hR1 D.hprojective hrows
  obtain ⟨r, hr⟩ := GCD369CubeExistsDepressedCubicRoot D.u D.v
  exact hnocommon r hr (by rw [hX, hY, hZ]; ring)

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubePolynomialSource

/-- Generic source-facing strict-before routing for the first first-integral
load, with every source load through `c1` explicitly zero. -/
theorem infinity_rho1_eq_zero_strict_before
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hd0 : S.faberConstantParameters.d = 0)
    (hc70 : S.faberConstantParameters.c7 = 0)
    (hc50 : S.faberConstantParameters.c5 = 0)
    (hc40 : S.faberConstantParameters.c4 = 0)
    (hc30 : S.faberConstantParameters.c3 = 0)
    (hc20 : S.faberConstantParameters.c2 = 0)
    (hc10 : S.faberConstantParameters.c1 = 0)
    (hbefore :
      10 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p <
        2 * T.delta) :
    S.faberFirstIntegralConstants.rho1 = 0 := by
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  obtain ⟨hd, hc7, hc5, hc4, hc3, hc2, hc1,
      hr1, hr2, hr3, hr4⟩ :=
    S.infinityFaberPoleData_constant_loads hpole
  apply T.rho1_eq_zero_strict_before R.rho1 R.rho2 R.rho3 R.rho4
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    simpa only [P, hd0] using hd
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    simpa only [P, hc70] using hc7
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    simpa only [P, hc50] using hc5
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    simpa only [P, hc40] using hc4
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    simpa only [P, hc30] using hc3
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    simpa only [P, hc20] using hc2
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    simpa only [P, hc10] using hc1
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hr1
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hr2
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hr3
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hr4
  · exact hbefore

/-- Target-normalized wrapper: `d = c3 = 0` is canonical, while the genuine
earlier source loads are supplied explicitly. -/
theorem targetNormalized_infinity_rho1_eq_zero_strict_before
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (hd0 : S.faberConstantParameters.d = 0)
    (T : let U := S.targetNormalizedSource
      let hsdegreeU : U.s.natDegree = 0 := by
        simpa [U, targetNormalizedSource] using hsdegree
      (U.infinityCommonCoefficientData hsdegreeU).TransverseScale)
    (hc70 : S.targetNormalizedSource.faberConstantParameters.c7 = 0)
    (hc50 : S.targetNormalizedSource.faberConstantParameters.c5 = 0)
    (hc40 : S.targetNormalizedSource.faberConstantParameters.c4 = 0)
    (hc20 : S.targetNormalizedSource.faberConstantParameters.c2 = 0)
    (hc10 : S.targetNormalizedSource.faberConstantParameters.c1 = 0)
    (hbefore : let U := S.targetNormalizedSource
      let hsdegreeU : U.s.natDegree = 0 := by
        simpa [U, targetNormalizedSource] using hsdegree
      10 * (U.infinityCommonCoefficientData hsdegreeU).faber.scale.p <
        2 * T.delta) :
    S.targetNormalizedSource.faberFirstIntegralConstants.rho1 = 0 := by
  let U := S.targetNormalizedSource
  have hsdegreeU : U.s.natDegree = 0 := by
    simpa [U, targetNormalizedSource] using hsdegree
  let Q := U.faberConstantParameters
  obtain ⟨hQd, _hQc7, _hQc6, _hQc5, _hQc4, hQc3, _hQc2,
      _hQc1, _hQc0⟩ := S.targetNormalizedCanonicalParameters hd0
  apply U.infinity_rho1_eq_zero_strict_before hsdegreeU T
  · simpa only [Q, U] using hQd
  · simpa only [Q, U] using hc70
  · simpa only [Q, U] using hc50
  · simpa only [Q, U] using hc40
  · simpa only [Q, U] using hQc3
  · simpa only [Q, U] using hc20
  · simpa only [Q, U] using hc10
  · simpa only [U, hsdegreeU] using hbefore

end GCD369CubePolynomialSource

#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseFactor.rhoOneBeforeLeadingFaberRowsAt
#print axioms
  GCD369CubeHahnCommonCoefficientData.rho1BeforeLeadingFaberRowsAt_of_bounds
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.rho1_eq_zero_strict_before
#print axioms GCD369CubePolynomialSource.infinity_rho1_eq_zero_strict_before
#print axioms
  GCD369CubePolynomialSource.targetNormalized_infinity_rho1_eq_zero_strict_before
