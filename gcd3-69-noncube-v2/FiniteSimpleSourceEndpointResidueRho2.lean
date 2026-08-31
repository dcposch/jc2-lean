import FiniteDoubleSourceNonicRho2
import FiniteSimpleSourceChart

/-! # The simple-source residue at the balanced `rho2` endpoint

At `11 * p = 3 * delta`, a nonzero residue in the half-scale transverse
coordinate would put the literal source transverse value at order
`3 * delta / 2`.  The simple-root chart and the reduced ninth-Faber
identity exclude every possible order of the source-root displacement.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- At the weight-eleven endpoint, a transverse value of exact order
`delta + delta / 2` is incompatible with a cubic value of order at least
`delta`. -/
theorem TransverseFactor.sourceSextic_inconsistent_of_half_residue_at_rho2
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (hEq : 11 * S.normal.sextic.scale.p = 3 * T.delta)
    (hK : (↑T.delta : WithTop ℚ) ≤ S.cubicValue.1.orderTop)
    (hphi : S.transverseValue.1.orderTop =
      (↑(T.delta + T.delta / 2) : WithTop ℚ)) : False := by
  have hKsq : (↑(2 * T.delta) : WithTop ℚ) ≤
      (S.cubicValue.1 ^ 2).orderTop := by
    by_cases hz : S.cubicValue.1 = 0
    · simp [hz]
    rw [pow_two, HahnSeries.orderTop_mul]
    rw [show 2 * T.delta = T.delta + T.delta by ring,
      WithTop.coe_add]
    exact add_le_add hK hK
  have horders : S.transverseValue.1.orderTop <
      (S.cubicValue.1 ^ 2).orderTop := by
    rw [hphi]
    exact (WithTop.coe_lt_coe.mpr (by nlinarith [T.hdelta])).trans_le hKsq
  have hsource := S.commonNormalEquation_orderTop_lower
  change (↑((6 : ℚ) * S.normal.sextic.scale.p) : WithTop ℚ) ≤
    (S.cubicValue.1 ^ 2 + S.transverseValue.1).orderTop at hsource
  rw [HahnSeries.orderTop_add_eq_right horders, hphi,
    WithTop.coe_le_coe] at hsource
  nlinarith [hEq, T.hdelta]

set_option maxHeartbeats 8000000 in
/-- On the simple source-root branch at the balanced weight-eleven resonance,
the exact quadratic moving-root coordinate has zero half-scale `B`
residue. -/
theorem TransverseFactor.simpleRoot_quadratic_B_residue_zero_at_rho2
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (hd : S.normal.d = 0)
    (hc7 : S.normal.c7 = 0)
    (hc5 : S.normal.c5 = 0)
    (hc4 : S.normal.c4 = 0)
    (hc3 : S.normal.c3 = 0)
    (hc2 : S.normal.c2 = 0)
    (hc1 : S.normal.c1 = 0)
    (hEq : 11 * S.normal.sextic.scale.p = 3 * T.delta)
    (r0 A0 : k) (r d B q : GCD369CubeHahnRegular k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hx : GCD369CubeHahnRegular.constantCoeff
      S.normal.sextic.regularX = -2 * r0)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0)
    (hD : S.cubicU + 3 * r ^ 2 =
      GCD369CubeHahnRegular.monomial (T.delta / 2)
        (div_nonneg T.hdelta.le (by norm_num)) ^ 2 * d)
    (hB : T.Yn - r * T.Xn =
      GCD369CubeHahnRegular.monomial (T.delta / 2)
        (div_nonneg T.hdelta.le (by norm_num)) * B)
    (hC : T.Zn + 2 * r ^ 2 * T.Xn =
      GCD369CubeHahnRegular.monomial (T.delta / 2)
        (div_nonneg T.hdelta.le (by norm_num)) ^ 2 * q -
      GCD369CubeHahnRegular.monomial (T.delta / 2)
        (div_nonneg T.hdelta.le (by norm_num)) * r * B) :
    GCD369CubeHahnRegular.constantCoeff B = 0 := by
  by_contra hB0
  let gamma : ℚ := T.delta / 2
  have hgamma : 0 < gamma := by dsimp only [gamma]; nlinarith [T.hdelta]
  let M : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial gamma hgamma.le
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  have hMdef : GCD369CubeHahnRegular.monomial (T.delta / 2)
      (div_nonneg T.hdelta.le (by norm_num)) = M := by
    apply Subtype.ext
    rfl
  rw [hMdef] at hD hB hC
  have hM2 : M ^ 2 = H := by
    apply Subtype.ext
    change (HahnSeries.single gamma (1 : k)) ^ 2 =
      HahnSeries.single T.delta 1
    rw [pow_two, HahnSeries.single_mul_single]
    dsimp only [gamma]
    congr 1 <;> ring
  rw [hM2] at hD hC
  let e : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.ratCast (-2 / 3) * d * r
  let w : GCD369CubeHahnRegular k := S.normal.sextic.regularX + 2 * r
  let N : GCD369CubeHahnRegular k := M * B
  let Rw : GCD369CubeHahnRegular k :=
    9 * r ^ 2 - 6 * r * w + w ^ 2
  let Us : GCD369CubeHahnRegular k := w - 3 * r
  have hU : S.cubicU = -3 * r ^ 2 + H * d := by
    linear_combination hD
  have hscalar : (3 : GCD369CubeHahnRegular k) *
      GCD369CubeHahnRegular.ratCast (-2 / 3) = -2 := by
    calc
      _ = GCD369CubeHahnRegular.ratCast 3 *
          GCD369CubeHahnRegular.ratCast (-2 / 3) := by rw [map_ofNat]
      _ = GCD369CubeHahnRegular.ratCast (3 * (-2 / 3)) :=
        (map_mul _ _ _).symm
      _ = GCD369CubeHahnRegular.ratCast (-2) := by norm_num
      _ = -2 := by rw [map_neg, map_ofNat]
  have hre : 3 * e + 2 * d * r = 0 := by
    dsimp only [e]
    calc
      _ = (3 * GCD369CubeHahnRegular.ratCast (-2 / 3)) * d * r +
          2 * d * r := by ring
      _ = 0 := by rw [hscalar]; ring
  have hV : S.cubicV = 2 * r ^ 3 + H * e := by
    have hroot' := hroot
    rw [hU] at hroot'
    have hthree : (3 : GCD369CubeHahnRegular k) ≠ 0 := by
      intro hz
      have hc := congrArg GCD369CubeHahnRegular.constantCoeff hz
      simp only [map_ofNat, map_zero] at hc
      exact (by norm_num : (3 : k) ≠ 0) hc
    apply mul_left_cancel₀ hthree
    linear_combination hroot' - H * hre
  have hw0 : GCD369CubeHahnRegular.constantCoeff w = 0 := by
    dsimp only [w]
    simp only [map_add, map_mul, map_ofNat, hx, hr]
    ring
  have hxcoord : S.normal.sextic.regularX = -2 * r + w := by
    dsimp only [w]
    ring
  have hYcoord : T.Yn = r * T.Xn + M * B + H * 0 := by
    linear_combination hB
  have hZcoord : T.Zn = -2 * r ^ 2 * T.Xn - M * r * B + H * q := by
    linear_combination hC
  have hcharts := T.simpleRoot_chart_equations
    r w d e B 0 q hxcoord (by simpa only [H] using hU)
    (by simpa only [H] using hV) hre
    (by simpa only [M, H] using hYcoord)
    (by simpa only [M, H] using hZcoord)
  have hMord := GCD369CubeHahnRegular.monomial_orderTop_and_leadingCoeff
    (k := k) gamma hgamma.le
  have hBord := GCD369CubeHahnRegular.orderTop_eq_zero_of_constantCoeff_ne_zero
    B hB0
  have hNdata := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
    M B gamma 0 hMord.1 hBord.1
  have hN : N.1.orderTop = (↑gamma : WithTop ℚ) := by
    simpa only [N, add_zero] using hNdata.1
  have hRwres : GCD369CubeHahnRegular.constantCoeff Rw = 9 * r0 ^ 2 := by
    dsimp only [Rw]
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
    rw [hr, hw0]
    ring
  have hRword := GCD369CubeHahnRegular.orderTop_eq_zero_of_constantCoeff_ne_zero
    Rw (by rw [hRwres]; exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hr0))
  have hUsres : GCD369CubeHahnRegular.constantCoeff Us = -3 * r0 := by
    dsimp only [Us]
    simp only [map_sub, map_mul, map_ofNat]
    rw [hr, hw0]
    ring
  have hUsord := GCD369CubeHahnRegular.orderTop_eq_zero_of_constantCoeff_ne_zero
    Us (by rw [hUsres]; exact mul_ne_zero (by norm_num) hr0)
  have hAord := GCD369CubeHahnRegular.orderTop_eq_zero_of_constantCoeff_ne_zero
    T.Xn (hX ▸ hA0)
  have hHord := GCD369CubeHahnRegular.monomial_orderTop_and_leadingCoeff
    (k := k) T.delta T.hdelta.le
  by_cases hwLate : (↑T.delta : WithTop ℚ) ≤ w.1.orderTop
  · have hKmain := GCD369CubeHahnRegular.mul_orderTop_lower
      w Rw T.delta 0 hwLate hRword.1.ge
    have hKmain' : (↑T.delta : WithTop ℚ) ≤ (w * Rw).1.orderTop := by
      simpa only [add_zero] using hKmain
    have hKhigh : (↑T.delta : WithTop ℚ) ≤
        (H * (d * w + GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r)).1.orderTop := by
      simpa only [add_zero] using GCD369CubeHahnRegular.mul_orderTop_lower
        H (d * w + GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r)
        T.delta 0 hHord.1.ge
        (d * w + GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r).2
    have hKsum := GCD369CubeHahnRegular.add_orderTop_lower
      (w * Rw)
      (H * (d * w + GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r))
      T.delta hKmain' hKhigh
    have hK : (↑T.delta : WithTop ℚ) ≤ S.cubicValue.1.orderTop := by
      rw [hcharts.1]
      simpa only [GCD369CubeSimpleSourceCubicChart, H, Rw] using hKsum
    have hAw0 := GCD369CubeHahnRegular.mul_orderTop_lower
      T.Xn w 0 T.delta hAord.1.ge hwLate
    have hAw : (↑T.delta : WithTop ℚ) ≤ (T.Xn * w).1.orderTop := by
      simpa only [zero_add] using hAw0
    have hsum0 := GCD369CubeHahnRegular.add_orderTop_eq_left_of_lt
      N (T.Xn * w) gamma T.delta hN hAw
      (by dsimp only [gamma]; nlinarith [T.hdelta])
    have hsum : (T.Xn * w + N).1.orderTop =
        (↑gamma : WithTop ℚ) := by
      rw [add_comm]
      exact hsum0.1
    have hprod := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
      (T.Xn * w + N) Us gamma 0 hsum hUsord.1
    have hprodOrder : ((T.Xn * w + N) * Us).1.orderTop =
        (↑gamma : WithTop ℚ) := by simpa only [add_zero] using hprod.1
    have htail0 := GCD369CubeHahnRegular.mul_orderTop_lower
      H q T.delta 0 hHord.1.ge q.2
    have htail : (↑T.delta : WithTop ℚ) ≤ (H * q).1.orderTop := by
      simpa only [add_zero] using htail0
    have hinner := GCD369CubeHahnRegular.add_orderTop_eq_left_of_lt
      ((T.Xn * w + N) * Us) (H * q) gamma T.delta
      hprodOrder htail (by dsimp only [gamma]; nlinarith [T.hdelta])
    have hphiData := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
      H ((T.Xn * w + N) * Us + H * q)
      T.delta gamma hHord.1 hinner.1
    have hphi : S.transverseValue.1.orderTop =
        (↑(T.delta + gamma) : WithTop ℚ) := by
      rw [hcharts.2]
      simpa only [GCD369CubeSimpleSourceTransverseChart, H, M, N, Us,
        mul_zero, zero_mul, zero_add] using hphiData.1
    exact T.sourceSextic_inconsistent_of_half_residue_at_rho2 hEq hK
      (by simpa only [gamma] using hphi)
  · have hwlt : w.1.orderTop < (↑T.delta : WithTop ℚ) := lt_of_not_ge hwLate
    have hwne : w ≠ 0 := by
      intro hz
      rw [hz] at hwlt
      simp at hwlt
    obtain ⟨alpha, halpha, hw⟩ :=
      GCD369CubeHahnRegular.exists_pos_orderTop_eq_of_constantCoeff_zero
        w hw0 hwne
    have hbelow : alpha < T.delta := by
      apply WithTop.coe_lt_coe.mp
      rw [← hw]
      exact hwlt
    let c : k := w.1.leadingCoeff
    have hc : c ≠ 0 := HahnSeries.leadingCoeff_ne_zero.mpr (by
      intro hz
      apply hwne
      exact Subtype.ext hz)
    have hwRw := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
      w Rw alpha 0 hw hRword.1
    have hmain : (w * Rw).1.orderTop = (↑alpha : WithTop ℚ) := by
      simpa only [add_zero] using hwRw.1
    have hmainLC : (w * Rw).1.leadingCoeff = c * (9 * r0 ^ 2) := by
      rw [hwRw.2, hRword.2, hRwres]
    have hhigh : (↑T.delta : WithTop ℚ) ≤
        (H * (d * w + GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r)).1.orderTop := by
      simpa only [add_zero] using GCD369CubeHahnRegular.mul_orderTop_lower
        H (d * w + GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r)
        T.delta 0 hHord.1.ge
        (d * w + GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r).2
    have hKdata := GCD369CubeHahnRegular.add_orderTop_eq_left_of_lt
      (w * Rw)
      (H * (d * w + GCD369CubeHahnRegular.ratCast (-8 / 3) * d * r))
      alpha T.delta hmain hhigh hbelow
    have hK : S.cubicValue.1.orderTop = (↑alpha : WithTop ℚ) := by
      rw [hcharts.1]
      simpa only [GCD369CubeSimpleSourceCubicChart, H, Rw] using hKdata.1
    have hKlc : S.cubicValue.1.leadingCoeff = c * (9 * r0 ^ 2) := by
      rw [hcharts.1]
      simpa only [GCD369CubeSimpleSourceCubicChart, H, Rw, hmainLC]
        using hKdata.2
    have hAwData := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
      T.Xn w 0 alpha hAord.1 hw
    have hAw : (T.Xn * w).1.orderTop = (↑alpha : WithTop ℚ) := by
      simpa only [zero_add] using hAwData.1
    by_cases hAlpha : alpha ≤ gamma
    · have hsum := GCD369CubeHahnRegular.add_orderTop_lower
        (T.Xn * w) N alpha hAw.ge
        ((WithTop.coe_le_coe.mpr hAlpha).trans_eq hN.symm)
      have hprod0 := GCD369CubeHahnRegular.mul_orderTop_lower
        (T.Xn * w + N) Us alpha 0 hsum hUsord.1.ge
      have hprod : (↑alpha : WithTop ℚ) ≤
          ((T.Xn * w + N) * Us).1.orderTop := by
        simpa only [add_zero] using hprod0
      have htail0 := GCD369CubeHahnRegular.mul_orderTop_lower
        H q T.delta 0 hHord.1.ge q.2
      have htail : (↑T.delta : WithTop ℚ) ≤ (H * q).1.orderTop := by
        simpa only [add_zero] using htail0
      have htailAlpha : (↑alpha : WithTop ℚ) ≤ (H * q).1.orderTop :=
        (WithTop.coe_le_coe.mpr hbelow.le).trans htail
      have hinner := GCD369CubeHahnRegular.add_orderTop_lower
        ((T.Xn * w + N) * Us) (H * q) alpha hprod htailAlpha
      have hphi0 := GCD369CubeHahnRegular.mul_orderTop_lower
        H ((T.Xn * w + N) * Us + H * q)
        T.delta alpha hHord.1.ge hinner
      have hphi : (↑(T.delta + alpha) : WithTop ℚ) ≤
          S.transverseValue.1.orderTop := by
        rw [hcharts.2]
        simpa only [GCD369CubeSimpleSourceTransverseChart, H, M, N, Us,
          mul_zero, zero_mul, zero_add] using hphi0
      exact T.sourceSextic_inconsistent_of_cubic_dominant
        alpha (T.delta + alpha) hK hphi (by linarith)
        (by dsimp only [gamma] at hAlpha; nlinarith [hEq])
    · have hgammaAlpha : gamma < alpha := lt_of_not_ge hAlpha
      have hsum0 := GCD369CubeHahnRegular.add_orderTop_eq_left_of_lt
        N (T.Xn * w) gamma alpha hN hAw.ge hgammaAlpha
      have hsum : (T.Xn * w + N).1.orderTop =
          (↑gamma : WithTop ℚ) := by
        rw [add_comm]
        exact hsum0.1
      have hprod := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
        (T.Xn * w + N) Us gamma 0 hsum hUsord.1
      have hprodOrder : ((T.Xn * w + N) * Us).1.orderTop =
          (↑gamma : WithTop ℚ) := by simpa only [add_zero] using hprod.1
      have htail0 := GCD369CubeHahnRegular.mul_orderTop_lower
        H q T.delta 0 hHord.1.ge q.2
      have htail : (↑T.delta : WithTop ℚ) ≤ (H * q).1.orderTop := by
        simpa only [add_zero] using htail0
      have hinner := GCD369CubeHahnRegular.add_orderTop_eq_left_of_lt
        ((T.Xn * w + N) * Us) (H * q) gamma T.delta
        hprodOrder htail (by dsimp only [gamma]; nlinarith [T.hdelta])
      have hphiData := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
        H ((T.Xn * w + N) * Us + H * q)
        T.delta gamma hHord.1 hinner.1
      have hphi : S.transverseValue.1.orderTop =
          (↑(T.delta + gamma) : WithTop ℚ) := by
        rw [hcharts.2]
        simpa only [GCD369CubeSimpleSourceTransverseChart, H, M, N, Us,
          mul_zero, zero_mul, zero_add] using hphiData.1
      have hresonance : 2 * alpha = T.delta + gamma := by
        rcases S.commonNormal_orderAlternative alpha (T.delta + gamma)
            hK hphi with hfar | hcancel
        · have hle : min (2 * alpha) (T.delta + gamma) ≤
              T.delta + gamma := min_le_right _ _
          have := hfar.trans hle
          dsimp only [gamma] at this
          nlinarith [hEq]
        · exact hcancel.1
      let L : GCD369CubeHahnRegular k :=
        T.Xn * S.normal.sextic.regularX + 2 * T.Yn
      have hLchart : L = T.Xn * w + 2 * N := by
        dsimp only [L, N]
        rw [hxcoord]
        have hY' : T.Yn = r * T.Xn + M * B := by
          linear_combination hB
        rw [hY']
        ring
      have htwo := GCD369CubeHahnRegular.orderTop_eq_zero_of_constantCoeff_ne_zero
        (2 : GCD369CubeHahnRegular k) (by
          simp only [map_ofNat]
          norm_num)
      have h2Ndata := GCD369CubeHahnRegular.mul_orderTop_and_leadingCoeff
        (2 : GCD369CubeHahnRegular k) N 0 gamma htwo.1 hN
      have h2N : (2 * N).1.orderTop = (↑gamma : WithTop ℚ) := by
        simpa only [zero_add] using h2Ndata.1
      have hLdata := GCD369CubeHahnRegular.add_orderTop_eq_left_of_lt
        (2 * N) (T.Xn * w) gamma alpha h2N hAw.ge hgammaAlpha
      have hL : L.1.orderTop = (↑gamma : WithTop ℚ) := by
        rw [hLchart, add_comm]
        exact hLdata.1
      let E : GCD369CubeHahnRegular k :=
        GCD369CubeHahnRegular.ratCast (3 / 8) * T.Xn * L
      have hscalarOrd :=
        GCD369CubeHahnRegular.orderTop_eq_zero_of_constantCoeff_ne_zero
          (GCD369CubeHahnRegular.ratCast (3 / 8) :
            GCD369CubeHahnRegular k)
          (by simp only [GCD369CubeHahnRegular.constantCoeff_ratCast]; norm_num)
      have hqA := GCD369CubeHahnRegular.mul_orderTop_lower
        (GCD369CubeHahnRegular.ratCast (3 / 8) :
          GCD369CubeHahnRegular k) T.Xn 0 0
        hscalarOrd.1.ge hAord.1.ge
      have hE0 := GCD369CubeHahnRegular.mul_orderTop_lower
        (GCD369CubeHahnRegular.ratCast (3 / 8) * T.Xn) L
        0 gamma (by simpa only [zero_add] using hqA) hL.ge
      have hE : (↑gamma : WithTop ℚ) ≤ E.1.orderTop := by
        simpa only [E, zero_add] using hE0
      exact T.reducedFaberNine_inconsistent_of_exact_cubic_order_before_later
        hd hc7 hc5 hc4 hc3 hc2 hc1 alpha gamma (c * (9 * r0 ^ 2))
        halpha
        (mul_ne_zero hc (mul_ne_zero (by norm_num) (pow_ne_zero 2 hr0)))
        hK hKlc (by simpa only [E, L] using hE)
        (by dsimp only [gamma] at hgammaAlpha hresonance ⊢;
            nlinarith [hresonance, hbelow, T.hdelta])
        (by dsimp only [gamma] at hgammaAlpha hresonance ⊢;
            nlinarith [hresonance, hbelow, hEq,
              T.hdelta, S.normal.sextic.scale.hp])
        (by dsimp only [gamma] at hgammaAlpha hresonance ⊢;
            nlinarith [hresonance, hbelow, hEq,
              T.hdelta, S.normal.sextic.scale.hp])

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.sourceSextic_inconsistent_of_half_residue_at_rho2
#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.simpleRoot_quadratic_B_residue_zero_at_rho2
