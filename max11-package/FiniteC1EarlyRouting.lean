import FiniteArbitraryLoadStrict
import FiniteArbitraryLoadTied
import FiniteC1RootLift
import FiniteC1SourceElimination

/-! # Routing the weight-eight `c1` load

After the weight-one, weight-two, weight-four, weight-five, gauge
weight-six, and weight-seven parameters have vanished, `c1` is the next
possible source load.  Its factor scale is `(8p)/2`.  Strictly before the
canonical transverse normal, the arbitrary-load common-root obstruction
kills it; at equality, the forced cubic resonance `3 * alpha = 6 * p`
still lies below the weight-eight ninth-Faber threshold.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- If the weight-eight `c1` load arrives strictly before the canonical
transverse normal, its coefficient vanishes. -/
theorem TransverseScale.c1_eq_zero_before_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (C1 R1 R2 R3 R4 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant 0)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : F.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : F.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : F.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : F.rho4 = GCD369CubeHahnRegular.constant R4)
    (hbefore : (8 * F.scale.p) / 2 < T.delta) :
    C1 = 0 := by
  obtain ⟨hn2, hn1, hn0⟩ := T.normal_orderTop_lower
  have hs : 0 < (8 * F.scale.p) / 2 := by
    exact div_pos (mul_pos (by norm_num) F.scale.hp) (by norm_num)
  have hb2 : (↑((8 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal2.1.orderTop :=
    (WithTop.coe_le_coe.mpr hbefore.le).trans hn2
  have hb1 : (↑((8 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal1.1.orderTop :=
    (WithTop.coe_le_coe.mpr hbefore.le).trans hn1
  have hb0 : (↑((8 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal0.1.orderTop :=
    (WithTop.coe_le_coe.mpr hbefore.le).trans hn0
  let U := S.transverseFactorOfBounds ((8 * F.scale.p) / 2)
    hs hb2 hb1 hb0
  have hrows : GCD369CubeC1LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff U.Xn)
      (GCD369CubeHahnRegular.constantCoeff U.Yn)
      (GCD369CubeHahnRegular.constantCoeff U.Zn) S.u S.v C1 := by
    simpa only [U] using S.c1LeadingFaberRowsAt_of_bounds F hscale
      C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 hb2 hb1 hb0
  by_contra hC1
  let load : GCD369CubeArbitraryEarlyFaberLoad
      (GCD369CubeHahnRegular.constantCoeff U.Xn)
      (GCD369CubeHahnRegular.constantCoeff U.Yn)
      (GCD369CubeHahnRegular.constantCoeff U.Zn) S.u S.v :=
    .c1 C1 hC1 S.hprojective hrows
  apply T.arbitraryEarlyLoad_strict_before_transverse
    ((8 * F.scale.p) / 2) hs hbefore
  simpa only [U] using load

/-- If the weight-eight `c1` load ties the canonical transverse normal, its
coefficient also vanishes.  The vanished weight-one through weight-seven
source terms extend the ninth-Faber coefficient gap through the weight-eight
threshold, which still covers the forced resonance `6 p`. -/
theorem TransverseScale.c1_eq_zero_at_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (C1 R1 R2 R3 R4 : k)
    (hdNormal : S.normal.d = 0)
    (hc7Normal : S.normal.c7 = 0)
    (hc5Normal : S.normal.c5 = 0)
    (hc4Normal : S.normal.c4 = 0)
    (hc3Normal : S.normal.c3 = 0)
    (hc2Normal : S.normal.c2 = 0)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant 0)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : F.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : F.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : F.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : F.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : (8 * F.scale.p) / 2 = T.delta) :
    C1 = 0 := by
  obtain ⟨hn2, hn1, hn0⟩ := T.normal_orderTop_lower
  have hs : 0 < (8 * F.scale.p) / 2 := by
    exact div_pos (mul_pos (by norm_num) F.scale.hp) (by norm_num)
  have hb2 : (↑((8 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal2.1.orderTop := by
    rw [htie]
    exact hn2
  have hb1 : (↑((8 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal1.1.orderTop := by
    rw [htie]
    exact hn1
  have hb0 : (↑((8 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal0.1.orderTop := by
    rw [htie]
    exact hn0
  let U := S.transverseFactorOfBounds ((8 * F.scale.p) / 2)
    hs hb2 hb1 hb0
  have hUdelta : U.delta = T.delta := by
    dsimp only [U, transverseFactorOfBounds]
    rw [htie]
  have hrows : GCD369CubeC1LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff U.Xn)
      (GCD369CubeHahnRegular.constantCoeff U.Yn)
      (GCD369CubeHahnRegular.constantCoeff U.Zn) S.u S.v C1 := by
    simpa only [U] using S.c1LeadingFaberRowsAt_of_bounds F hscale
      C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 hb2 hb1 hb0
  by_contra hC1
  let load : GCD369CubeArbitraryEarlyFaberLoad
      (GCD369CubeHahnRegular.constantCoeff U.Xn)
      (GCD369CubeHahnRegular.constantCoeff U.Yn)
      (GCD369CubeHahnRegular.constantCoeff U.Zn) S.u S.v :=
    .c1 C1 hC1 S.hprojective hrows
  have hbeforeSource : U.delta < 6 * S.normal.sextic.scale.p := by
    rw [hUdelta, ← htie, hscale]
    nlinarith [F.scale.hp]
  obtain ⟨alpha, a, halpha, ha, hKorder, hlcK, hresonance⟩ :=
    U.cubic_resonance_of_arbitraryEarlyLoad load hbeforeSource
  apply U.reducedFaberNine_inconsistent_of_exact_cubic_order_before_c1
    hdNormal hc7Normal hc5Normal hc4Normal hc3Normal hc2Normal
    alpha 0 a halpha ha hKorder hlcK
  · exact (show (↑(0 : ℚ) : WithTop ℚ) ≤
      (GCD369CubeHahnRegular.ratCast (3 / 8) * U.Xn *
        (U.Xn * S.normal.sextic.regularX + 2 * U.Yn)).1.orderTop from
      (GCD369CubeHahnRegular.ratCast (3 / 8) * U.Xn *
        (U.Xn * S.normal.sextic.regularX + 2 * U.Yn)).2)
  · nlinarith [U.hdelta]
  · nlinarith [hresonance, hbeforeSource]
  · rw [hscale]
    nlinarith [hresonance, hUdelta, htie, F.scale.hp]

/-- The complete weight-eight active-load branch: once `d=c7=c5=c4=c3=c2=0`,
arrival of `c1` no later than the transverse normal forces `c1=0`. -/
theorem TransverseScale.c1_eq_zero_at_or_before_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (C1 R1 R2 R3 R4 : k)
    (hdNormal : S.normal.d = 0)
    (hc7Normal : S.normal.c7 = 0)
    (hc5Normal : S.normal.c5 = 0)
    (hc4Normal : S.normal.c4 = 0)
    (hc3Normal : S.normal.c3 = 0)
    (hc2Normal : S.normal.c2 = 0)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant 0)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : F.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : F.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : F.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : F.rho4 = GCD369CubeHahnRegular.constant R4)
    (hle : (8 * F.scale.p) / 2 ≤ T.delta) :
    C1 = 0 := by
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact T.c1_eq_zero_before_transverse F hscale
      C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 hlt
  · exact T.c1_eq_zero_at_transverse F hscale
      C1 R1 R2 R3 R4 hdNormal hc7Normal hc5Normal hc4Normal
      hc3Normal hc2Normal
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 heq

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.c1_eq_zero_before_transverse
#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.c1_eq_zero_at_transverse
#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.c1_eq_zero_at_or_before_transverse
