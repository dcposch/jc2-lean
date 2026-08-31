import InfinityC2Middle
import FiniteC1EarlyNormal
import FiniteDoubleC1LoadLift
import TargetNormalization
import FiniteTargetNormalizedParameters

/-! # The strict middle weight-eight load at infinity

After `d = c7 = c5 = c4 = c3 = 0`, this file treats
`2 * delta < 8 * p < 3 * delta`.  The coefficient-only zero-load rows
drive the two-stage moving-root lift to the active `c1` quadratic
contradiction.
-/

noncomputable section

namespace GCD369CubeHahnCommonCoefficientData

theorem TransverseFactor.doubleRoot_row123Coeffs_zero_before_c1_coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (hd : D.faber.d = 0) (hc7 : D.faber.c7 = 0)
    (hc5 : D.faber.c5 = 0) (hc4 : D.faber.c4 = 0)
    (hc3 : D.faber.c3 = 0)
    (hc2 : D.faber.c2 = 0)
    (r : GCD369CubeHahnRegular k)
    (hroot : 2 * D.cubicU * r + 3 * D.cubicV = 0)
    (e : ℚ) (he : 0 ≤ e) (heDelta : e < T.delta)
    (hearly : 2 * T.delta + e < 8 * D.faber.scale.p) :
    let A := T.Xn
    let Dv := D.cubicU + 3 * r ^ 2
    let B := T.Yn - r * A
    let C := T.Zn + 2 * r ^ 2 * A
    ((A ^ 2 * Dv - 2 * A * B * r - B ^ 2 - 2 * A * C).1.coeff e = 0) ∧
    ((2 * A ^ 2 * r * Dv - 3 * A * B * r ^ 2 - 3 * A * C * r +
        3 * A * B * Dv - 3 * B * C).1.coeff e = 0) ∧
    ((-2 * A ^ 2 * r ^ 2 * Dv + 6 * B ^ 2 * r ^ 2 +
        2 * A ^ 2 * Dv ^ 2 - 2 * B ^ 2 * Dv - 4 * A * C * Dv +
        3 * C ^ 2).1.coeff e = 0) := by
  dsimp only
  let A : GCD369CubeHahnRegular k := T.Xn
  let Dv : GCD369CubeHahnRegular k := D.cubicU + 3 * r ^ 2
  let B : GCD369CubeHahnRegular k := T.Yn - r * A
  let C : GCD369CubeHahnRegular k := T.Zn + 2 * r ^ 2 * A
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let R1 : GCD369CubeHahnRegular k :=
    A ^ 2 * Dv - 2 * A * B * r - B ^ 2 - 2 * A * C
  let R2 : GCD369CubeHahnRegular k :=
    2 * A ^ 2 * r * Dv - 3 * A * B * r ^ 2 - 3 * A * C * r +
      3 * A * B * Dv - 3 * B * C
  let R3 : GCD369CubeHahnRegular k :=
    -2 * A ^ 2 * r ^ 2 * Dv + 6 * B ^ 2 * r ^ 2 +
      2 * A ^ 2 * Dv ^ 2 - 2 * B ^ 2 * Dv - 4 * A * C * Dv + 3 * C ^ 2
  let N1 : GCD369CubeHahnRegular k := GCD369CubeFaberN1
    D.faber.scale.regular0 D.faber.scale.regular1 D.faber.scale.regular2
    D.faber.scale.regular3 D.faber.scale.regular4
  let N2 : GCD369CubeHahnRegular k := GCD369CubeFaberN2
    D.faber.scale.regular0 D.faber.scale.regular1 D.faber.scale.regular2
    D.faber.scale.regular3 D.faber.scale.regular4
  let N3 : GCD369CubeHahnRegular k := GCD369CubeFaberN3
    D.faber.scale.regular0 D.faber.scale.regular1 D.faber.scale.regular2
    D.faber.scale.regular3 D.faber.scale.regular4
  have hz := D.faber.zeroHighNCoeff_zero_before_c1 hd hc7 hc5 hc4 hc3 hc2
    (2 * T.delta + e) (by nlinarith [T.hdelta]) hearly
  have hexp := T.doubleRoot_zeroHigh_expansions_coeff r hroot
  have hexp1 : 729 * N1 = (-32 * (729 * R1)) * H ^ 2 := by
    simpa only [N1, R1, A, Dv, B, C, H] using hexp.1
  have hexp2 : 2187 * N2 = (32 * (-1458 * R2)) * H ^ 2 := by
    simpa only [N2, R2, A, Dv, B, C, H] using hexp.2.1
  have hexp3 : N3 = (128 * R3) * H ^ 2 - (64 * A ^ 3) * H ^ 3 := by
    simpa only [N3, R3, A, Dv, B, C, H] using hexp.2.2.1
  have hshift1 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (-32 * (729 * R1)) T.delta e T.hdelta.le 2
  have hshift2 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (32 * (-1458 * R2)) T.delta e T.hdelta.le 2
  have hshift3 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (128 * R3) T.delta e T.hdelta.le 2
  change ((-32 * (729 * R1)) * H ^ 2).1.coeff
      (e + (2 : ℚ) * T.delta) = (-32 * (729 * R1)).1.coeff e at hshift1
  change ((32 * (-1458 * R2)) * H ^ 2).1.coeff
      (e + (2 : ℚ) * T.delta) = (32 * (-1458 * R2)).1.coeff e at hshift2
  change ((128 * R3) * H ^ 2).1.coeff
      (e + (2 : ℚ) * T.delta) = (128 * R3).1.coeff e at hshift3
  have hc1 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * T.delta + e)) hexp1
  have hc2 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * T.delta + e)) hexp2
  have hc3 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * T.delta + e)) hexp3
  rw [show 2 * T.delta + e = e + (2 : ℚ) * T.delta by ring,
    hshift1] at hc1
  rw [show 2 * T.delta + e = e + (2 : ℚ) * T.delta by ring,
    hshift2] at hc2
  have hcubicShift := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (64 * A ^ 3) T.delta (e - T.delta) T.hdelta.le 3
  change ((64 * A ^ 3) * H ^ 3).1.coeff
      ((e - T.delta) + (3 : ℚ) * T.delta) =
        (64 * A ^ 3).1.coeff (e - T.delta) at hcubicShift
  have hcubicZero : (64 * A ^ 3).1.coeff (e - T.delta) = 0 :=
    GCD369CubeHahnRegular.coeff_eq_zero_of_neg _ (sub_neg.mpr heDelta)
  change N3.1.coeff (2 * T.delta + e) =
    ((128 * R3) * H ^ 2).1.coeff (2 * T.delta + e) -
      ((64 * A ^ 3) * H ^ 3).1.coeff (2 * T.delta + e) at hc3
  rw [show 2 * T.delta + e = e + (2 : ℚ) * T.delta by ring,
    hshift3] at hc3
  rw [show e + (2 : ℚ) * T.delta =
      (e - T.delta) + (3 : ℚ) * T.delta by ring,
    hcubicShift, hcubicZero, sub_zero] at hc3
  have hz1scaled : (-32 * (729 * R1)).1.coeff e = 0 := by
    calc
      _ = (729 * N1).1.coeff (e + 2 * T.delta) := hc1.symm
      _ = (729 * N1).1.coeff (2 * T.delta + e) := by
        rw [show e + 2 * T.delta = 2 * T.delta + e by ring]
      _ = 0 := by simpa only [N1] using hz.1
  have hz2scaled : (32 * (-1458 * R2)).1.coeff e = 0 := by
    calc
      _ = (2187 * N2).1.coeff (e + 2 * T.delta) := hc2.symm
      _ = (2187 * N2).1.coeff (2 * T.delta + e) := by
        rw [show e + 2 * T.delta = 2 * T.delta + e by ring]
      _ = 0 := by simpa only [N2] using hz.2.1
  have hz3N : N3.1.coeff (2 * T.delta + e) = 0 := by
    have hnat : (243 * N3).1.coeff (2 * T.delta + e) =
        (243 : k) * N3.1.coeff (2 * T.delta + e) :=
      GCD369CubeHahnRegular.coeff_nat_mul 243 N3 (2 * T.delta + e)
    have hscaled : (243 * N3).1.coeff (2 * T.delta + e) = 0 := by
      simpa only [N3] using hz.2.2.1
    rw [hnat] at hscaled
    exact (mul_eq_zero.mp hscaled).resolve_left (by norm_num)
  have hz3scaled : (128 * R3).1.coeff e = 0 := by
    calc
      _ = N3.1.coeff (e - T.delta + 3 * T.delta) := hc3.symm
      _ = N3.1.coeff (2 * T.delta + e) := by
        rw [show e - T.delta + 3 * T.delta = 2 * T.delta + e by ring]
      _ = 0 := hz3N
  have hscalar1 : -32 * (729 * R1) = (-23328 : ℤ) * R1 := by ring
  have hscalar2 : 32 * (-1458 * R2) = (-46656 : ℤ) * R2 := by ring
  rw [hscalar1, GCD369CubeHahnRegular.coeff_int_mul] at hz1scaled
  rw [hscalar2, GCD369CubeHahnRegular.coeff_int_mul] at hz2scaled
  have hcoeff128 : (128 * R3).1.coeff e = (128 : k) * R3.1.coeff e :=
    GCD369CubeHahnRegular.coeff_nat_mul 128 R3 e
  rw [hcoeff128] at hz3scaled
  have hR1zero := (mul_eq_zero.mp hz1scaled).resolve_left (by norm_num)
  have hR2zero := (mul_eq_zero.mp hz2scaled).resolve_left (by norm_num)
  have hR3zero := (mul_eq_zero.mp hz3scaled).resolve_left (by norm_num)
  exact ⟨by simpa only [R1, A, Dv, B, C] using hR1zero,
    by simpa only [R2, A, Dv, B, C] using hR2zero,
    by simpa only [R3, A, Dv, B, C] using hR3zero⟩
/-- No moving-root deviation can begin below the residual half-load scale
`8p/2-delta`. -/
theorem TransverseFactor.doubleRoot_firstCommonScale_not_below_c1Load_half_coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (hd : D.faber.d = 0) (hc7 : D.faber.c7 = 0)
    (hc5 : D.faber.c5 = 0) (hc4 : D.faber.c4 = 0)
    (hc3 : D.faber.c3 = 0)
    (hc2 : D.faber.c2 = 0)
    (_hdeltaP : T.delta < (8 * D.faber.scale.p) / 2)
    (hpDelta : 8 * D.faber.scale.p < 3 * T.delta)
    (r : GCD369CubeHahnRegular k)
    (hA : GCD369CubeHahnRegular.constantCoeff T.Xn ≠ 0)
    (hr : GCD369CubeHahnRegular.constantCoeff r ≠ 0)
    (hroot : 2 * D.cubicU * r + 3 * D.cubicV = 0)
    (J : GCD369CubeHahnRegular.TripleScale
      (D.cubicU + 3 * r ^ 2) (T.Yn - r * T.Xn)
      (T.Zn + 2 * r ^ 2 * T.Xn)) :
    ¬ J.mu < (8 * D.faber.scale.p) / 2 - T.delta := by
  intro hsmall
  let A : GCD369CubeHahnRegular k := T.Xn
  let Dv : GCD369CubeHahnRegular k := D.cubicU + 3 * r ^ 2
  let B : GCD369CubeHahnRegular k := T.Yn - r * A
  let C : GCD369CubeHahnRegular k := T.Zn + 2 * r ^ 2 * A
  change GCD369CubeHahnRegular.TripleScale Dv B C at J
  let R1 : GCD369CubeHahnRegular k :=
    A ^ 2 * Dv - 2 * A * B * r - B ^ 2 - 2 * A * C
  let R2 : GCD369CubeHahnRegular k :=
    2 * A ^ 2 * r * Dv - 3 * A * B * r ^ 2 - 3 * A * C * r +
      3 * A * B * Dv - 3 * B * C
  let R3 : GCD369CubeHahnRegular k :=
    -2 * A ^ 2 * r ^ 2 * Dv + 6 * B ^ 2 * r ^ 2 +
      2 * A ^ 2 * Dv ^ 2 - 2 * B ^ 2 * Dv - 4 * A * C * Dv + 3 * C ^ 2
  have htwoMuDelta : 2 * J.mu < T.delta := by nlinarith
  have hR1 : (↑(2 * J.mu) : WithTop ℚ) ≤ R1.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro q hq
    have hq' := WithTop.coe_lt_coe.mp hq
    by_cases hq0 : 0 ≤ q
    · have hs := T.doubleRoot_row123Coeffs_zero_before_c1_coeff hd hc7 hc5 hc4 hc3 hc2
        r hroot q hq0 (by linarith) (by linarith)
      simpa only [R1, A, Dv, B, C] using hs.1
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg R1 (lt_of_not_ge hq0)
  have hR2 : (↑(2 * J.mu) : WithTop ℚ) ≤ R2.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro q hq
    have hq' := WithTop.coe_lt_coe.mp hq
    by_cases hq0 : 0 ≤ q
    · have hs := T.doubleRoot_row123Coeffs_zero_before_c1_coeff hd hc7 hc5 hc4 hc3 hc2
        r hroot q hq0 (by linarith) (by linarith)
      simpa only [R2, A, Dv, B, C] using hs.2.1
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg R2 (lt_of_not_ge hq0)
  have hs := T.doubleRoot_row123Coeffs_zero_before_c1_coeff hd hc7 hc5 hc4 hc3 hc2
    r hroot (2 * J.mu) (by linarith [J.hmu]) htwoMuDelta (by linarith)
  exact GCD369CubeHahnRegular.doubleBlowup_quadratic_inconsistent
    A r Dv B C J (by simpa only [A] using hA) hr
    (by simpa only [R1] using hR1) (by simpa only [R2] using hR2)
    (by simpa only [R1, A, Dv, B, C] using hs.1)
    (by simpa only [R2, A, Dv, B, C] using hs.2.1)
    (by simpa only [R3, A, Dv, B, C] using hs.2.2)

/-- The first-scale exclusion gives simultaneous residual half-load order
bounds for all three moving-root deviations. -/
theorem TransverseFactor.doubleRoot_deviations_order_c1Load_half_lower_coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (hd : D.faber.d = 0) (hc7 : D.faber.c7 = 0)
    (hc5 : D.faber.c5 = 0) (hc4 : D.faber.c4 = 0)
    (hc3 : D.faber.c3 = 0)
    (hc2 : D.faber.c2 = 0)
    (hdeltaP : T.delta < (8 * D.faber.scale.p) / 2)
    (hpDelta : 8 * D.faber.scale.p < 3 * T.delta)
    (r : GCD369CubeHahnRegular k) (r0 A0 : k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hu : GCD369CubeHahnRegular.constantCoeff D.cubicU = -3 * r0 ^ 2)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r0 * A0)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r0 ^ 2 * A0)
    (hroot : 2 * D.cubicU * r + 3 * D.cubicV = 0) :
    (↑((8 * D.faber.scale.p) / 2 - T.delta) : WithTop ℚ) ≤
        (D.cubicU + 3 * r ^ 2).1.orderTop ∧
      (↑((8 * D.faber.scale.p) / 2 - T.delta) : WithTop ℚ) ≤
        (T.Yn - r * T.Xn).1.orderTop ∧
      (↑((8 * D.faber.scale.p) / 2 - T.delta) : WithTop ℚ) ≤
        (T.Zn + 2 * r ^ 2 * T.Xn).1.orderTop := by
  let Dv : GCD369CubeHahnRegular k := D.cubicU + 3 * r ^ 2
  let B : GCD369CubeHahnRegular k := T.Yn - r * T.Xn
  let C : GCD369CubeHahnRegular k := T.Zn + 2 * r ^ 2 * T.Xn
  have hD0 : GCD369CubeHahnRegular.constantCoeff Dv = 0 := by
    dsimp only [Dv]; simp only [map_add, map_mul, map_pow, map_ofNat, hu, hr]; ring
  have hB0 : GCD369CubeHahnRegular.constantCoeff B = 0 := by
    dsimp only [B]; simp only [map_sub, map_mul, hY, hr, hX]; ring
  have hC0 : GCD369CubeHahnRegular.constantCoeff C = 0 := by
    dsimp only [C]; simp only [map_add, map_mul, map_pow, map_ofNat, hZ, hr, hX]; ring
  by_cases hn : Dv ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0
  · let J := GCD369CubeHahnRegular.tripleScale Dv B C hD0 hB0 hC0 hn
    have hnot := T.doubleRoot_firstCommonScale_not_below_c1Load_half_coeff
      hd hc7 hc5 hc4 hc3 hc2 hdeltaP hpDelta r (by rw [hX]; exact hA0)
      (by rw [hr]; exact hr0) hroot J
    have hmu : (8 * D.faber.scale.p) / 2 - T.delta ≤ J.mu := le_of_not_gt hnot
    have hDmu : (↑J.mu : WithTop ℚ) ≤ Dv.1.orderTop := by
      have hm := GCD369CubeHahnRegular.monomial_mul_orderTop_lower
        J.mu J.hmu.le J.Dn
      exact hm.trans_eq (congrArg
        (fun z : GCD369CubeHahnRegular k => z.1.orderTop) J.hD).symm
    have hBmu : (↑J.mu : WithTop ℚ) ≤ B.1.orderTop := by
      have hm := GCD369CubeHahnRegular.monomial_mul_orderTop_lower
        J.mu J.hmu.le J.Bn
      exact hm.trans_eq (congrArg
        (fun z : GCD369CubeHahnRegular k => z.1.orderTop) J.hB).symm
    have hCmu : (↑J.mu : WithTop ℚ) ≤ C.1.orderTop := by
      have hm := GCD369CubeHahnRegular.monomial_mul_orderTop_lower
        J.mu J.hmu.le J.Cn
      exact hm.trans_eq (congrArg
        (fun z : GCD369CubeHahnRegular k => z.1.orderTop) J.hC).symm
    have hcoe : (↑((8 * D.faber.scale.p) / 2 - T.delta) : WithTop ℚ) ≤
        (↑J.mu : WithTop ℚ) := WithTop.coe_le_coe.mpr hmu
    exact ⟨by simpa only [Dv] using hcoe.trans hDmu,
      by simpa only [B] using hcoe.trans hBmu,
      by simpa only [C] using hcoe.trans hCmu⟩
  · simp only [not_or, not_ne_iff] at hn
    rcases hn with ⟨hDz, hBz, hCz⟩
    constructor
    · rw [show D.cubicU + 3 * r ^ 2 = Dv by rfl, hDz]
      simp
    constructor
    · rw [show T.Yn - r * T.Xn = B by rfl, hBz]
      simp
    · rw [show T.Zn + 2 * r ^ 2 * T.Xn = C by rfl, hCz]
      simp
/-- Leading residue of the first integral `c1` polynomial on the common
cubic. -/
theorem c1LoadPoly1_constantCoeff_coeff
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k) :
    let P : GCD369CubeHahnRegular k :=
      10368 * D.faber.scale.regular4
    GCD369CubeHahnRegular.constantCoeff P = 20736 * D.u := by
  dsimp only
  simp only [map_mul, map_ofNat]
  change 10368 * D.faber.scale.leading4 = _
  rw [D.ha4]
  ring

/-- Leading residue of the second integral `c1` polynomial on the common
cubic. -/
theorem c1LoadPoly2_constantCoeff_coeff
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k) :
    let P : GCD369CubeHahnRegular k :=
      31104 * D.faber.scale.regular3
    GCD369CubeHahnRegular.constantCoeff P = 62208 * D.v := by
  dsimp only
  simp only [map_mul, map_ofNat]
  change 31104 * D.faber.scale.leading3 = _
  rw [D.ha3]
  ring

/-- The third integral `c1` polynomial has vanishing residue on the common
cubic. -/
theorem c1LoadPoly3_constantCoeff_coeff
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k) :
    let P : GCD369CubeHahnRegular k :=
      41472 * D.faber.scale.regular2 -
        10368 * D.faber.scale.regular4 ^ 2
    GCD369CubeHahnRegular.constantCoeff P = 0 := by
  dsimp only
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  change
    41472 * D.faber.scale.leading2 -
      10368 * D.faber.scale.leading4 ^ 2 = 0
  rw [D.ha2, D.ha4]
  ring

/-- Leading residue of the fourth integral `c1` polynomial on the common
cubic. -/
theorem c1LoadPoly4_constantCoeff_coeff
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k) :
    let P : GCD369CubeHahnRegular k :=
      279936 * D.faber.scale.regular1 -
        93312 * D.faber.scale.regular3 *
          D.faber.scale.regular4
    GCD369CubeHahnRegular.constantCoeff P = 186624 * D.u * D.v := by
  dsimp only
  simp only [map_sub, map_mul, map_ofNat]
  change
    279936 * D.faber.scale.leading1 -
      93312 * D.faber.scale.leading3 *
        D.faber.scale.leading4 = _
  rw [D.ha1, D.ha3, D.ha4]
  ring
set_option maxHeartbeats 4000000 in
theorem TransverseFactor.doubleRoot_c1Load_coeff_of_lt
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C1 Rho1 Rho2 Rho3 Rho4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant 0)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hrho1 : D.faber.rho1 = GCD369CubeHahnRegular.constant Rho1)
    (hrho2 : D.faber.rho2 = GCD369CubeHahnRegular.constant Rho2)
    (hrho3 : D.faber.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : D.faber.rho4 = GCD369CubeHahnRegular.constant Rho4)
    (r : GCD369CubeHahnRegular k)
    (hroot : 2 * D.cubicU * r + 3 * D.cubicV = 0)
    (hu : D.u = -3 * GCD369CubeHahnRegular.constantCoeff r ^ 2)
    (hv : D.v = 2 * GCD369CubeHahnRegular.constantCoeff r ^ 3)
    (hpLT : T.delta < (8 * D.faber.scale.p) / 2)
    (hpGT : 8 * D.faber.scale.p < 3 * T.delta) :
    let A := T.Xn
    let Dv := D.cubicU + 3 * r ^ 2
    let B := T.Yn - r * A
    let C := T.Zn + 2 * r ^ 2 * A
    let R1 := A ^ 2 * Dv - 2 * A * B * r - B ^ 2 - 2 * A * C
    let R2 :=
      2 * A ^ 2 * r * Dv - 3 * A * B * r ^ 2 - 3 * A * C * r +
        3 * A * B * Dv - 3 * B * C
    let R3 :=
      -2 * A ^ 2 * r ^ 2 * Dv + 6 * B ^ 2 * r ^ 2 +
        2 * A ^ 2 * Dv ^ 2 - 2 * B ^ 2 * Dv - 4 * A * C * Dv + 3 * C ^ 2
    let R4 :=
      4374 * (-3 * r ^ 2 + Dv) *
        (A * B * r ^ 2 + 2 * B ^ 2 * r + A * C * r +
          3 * A * B * Dv - 3 * B * C)
    let lambda := 8 * D.faber.scale.p - 2 * T.delta
    let r0 := GCD369CubeHahnRegular.constantCoeff r
    ((-32 * (729 * R1)).1.coeff lambda +
        C1 * (-62208 * r0 ^ 2) = 0) ∧
    ((32 * (-1458 * R2)).1.coeff lambda +
        C1 * (124416 * r0 ^ 3) = 0) ∧
    ((128 * R3).1.coeff lambda = 0) ∧
    ((32 * R4).1.coeff lambda +
        C1 * (-1119744 * r0 ^ 5) = 0) := by
  dsimp only
  let A : GCD369CubeHahnRegular k := T.Xn
  let Dv : GCD369CubeHahnRegular k := D.cubicU + 3 * r ^ 2
  let B : GCD369CubeHahnRegular k := T.Yn - r * A
  let C : GCD369CubeHahnRegular k := T.Zn + 2 * r ^ 2 * A
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let R1 : GCD369CubeHahnRegular k :=
    A ^ 2 * Dv - 2 * A * B * r - B ^ 2 - 2 * A * C
  let R2 : GCD369CubeHahnRegular k :=
    2 * A ^ 2 * r * Dv - 3 * A * B * r ^ 2 - 3 * A * C * r +
      3 * A * B * Dv - 3 * B * C
  let R3 : GCD369CubeHahnRegular k :=
    -2 * A ^ 2 * r ^ 2 * Dv + 6 * B ^ 2 * r ^ 2 +
      2 * A ^ 2 * Dv ^ 2 - 2 * B ^ 2 * Dv - 4 * A * C * Dv + 3 * C ^ 2
  let R4 : GCD369CubeHahnRegular k :=
    4374 * (-3 * r ^ 2 + Dv) *
      (A * B * r ^ 2 + 2 * B ^ 2 * r + A * C * r +
        3 * A * B * Dv - 3 * B * C)
  let lambda : ℚ := 8 * D.faber.scale.p - 2 * T.delta
  let r0 : k := GCD369CubeHahnRegular.constantCoeff r
  let N1 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberN1
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
  let N2 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberN2
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
  let N3 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberN3
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
  let N4 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberN4
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
  let P1 : GCD369CubeHahnRegular k :=
    10368 * D.faber.scale.regular4
  let P2 : GCD369CubeHahnRegular k :=
    31104 * D.faber.scale.regular3
  let P3 : GCD369CubeHahnRegular k :=
    41472 * D.faber.scale.regular2 -
      10368 * D.faber.scale.regular4 ^ 2
  let P4 : GCD369CubeHahnRegular k :=
    279936 * D.faber.scale.regular1 -
      93312 * D.faber.scale.regular3 *
        D.faber.scale.regular4
  let c1w : GCD369CubeHahnRegular k :=
    D.faber.scale.weightedRegular 8
      (GCD369CubeHahnRegular.constant C1)
  have hlambda : 8 * D.faber.scale.p = lambda + (2 : ℚ) * T.delta := by
    dsimp only [lambda]
    ring
  have hlambda_pos : 0 < lambda := by
    dsimp only [lambda]
    linarith [hpLT]
  have hexp := T.doubleRoot_zeroHigh_expansions_coeff r hroot
  have hexp1 : 729 * N1 = (-32 * (729 * R1)) * H ^ 2 := by
    simpa only [N1, R1, A, Dv, B, C, H] using hexp.1
  have hexp2 : 2187 * N2 = (32 * (-1458 * R2)) * H ^ 2 := by
    simpa only [N2, R2, A, Dv, B, C, H] using hexp.2.1
  have hexp3 : N3 = (128 * R3) * H ^ 2 - (64 * A ^ 3) * H ^ 3 := by
    simpa only [N3, R3, A, Dv, B, C, H] using hexp.2.2.1
  have hexp4 :
      6561 * N4 =
        (32 * R4) * H ^ 2 -
          (314928 * (r * A + B) * A ^ 2) * H ^ 3 := by
    simpa only [N4, R4, A, Dv, B, C, H] using hexp.2.2.2
  have hshift1 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (-32 * (729 * R1)) T.delta lambda T.hdelta.le 2
  have hshift2 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (32 * (-1458 * R2)) T.delta lambda T.hdelta.le 2
  have hshift3 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (128 * R3) T.delta lambda T.hdelta.le 2
  have hshift4 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (32 * R4) T.delta lambda T.hdelta.le 2
  change ((-32 * (729 * R1)) * H ^ 2).1.coeff
      (lambda + (2 : ℚ) * T.delta) =
        (-32 * (729 * R1)).1.coeff lambda at hshift1
  change ((32 * (-1458 * R2)) * H ^ 2).1.coeff
      (lambda + (2 : ℚ) * T.delta) =
        (32 * (-1458 * R2)).1.coeff lambda at hshift2
  change ((128 * R3) * H ^ 2).1.coeff
      (lambda + (2 : ℚ) * T.delta) =
        (128 * R3).1.coeff lambda at hshift3
  change ((32 * R4) * H ^ 2).1.coeff
      (lambda + (2 : ℚ) * T.delta) =
        (32 * R4).1.coeff lambda at hshift4
  have hcubic3 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (64 * A ^ 3) T.delta (8 * D.faber.scale.p - 3 * T.delta) T.hdelta.le 3
  have hcubic4 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (314928 * (r * A + B) * A ^ 2) T.delta
    (8 * D.faber.scale.p - 3 * T.delta) T.hdelta.le 3
  change ((64 * A ^ 3) * H ^ 3).1.coeff
      ((8 * D.faber.scale.p - 3 * T.delta) + (3 : ℚ) * T.delta) =
        (64 * A ^ 3).1.coeff (8 * D.faber.scale.p - 3 * T.delta) at hcubic3
  change ((314928 * (r * A + B) * A ^ 2) * H ^ 3).1.coeff
      ((8 * D.faber.scale.p - 3 * T.delta) + (3 : ℚ) * T.delta) =
        (314928 * (r * A + B) * A ^ 2).1.coeff
          (8 * D.faber.scale.p - 3 * T.delta) at hcubic4
  have hneg : 8 * D.faber.scale.p - 3 * T.delta < 0 := by linarith [hpGT]
  have hcubic3zero :
      ((64 * A ^ 3) * H ^ 3).1.coeff (8 * D.faber.scale.p) = 0 := by
    have hrew : (8 * D.faber.scale.p - 3 * T.delta) + (3 : ℚ) * T.delta =
        8 * D.faber.scale.p := by ring
    rw [← hrew, hcubic3]
    exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg _ hneg
  have hcubic4zero :
      ((314928 * (r * A + B) * A ^ 2) * H ^ 3).1.coeff
          (8 * D.faber.scale.p) = 0 := by
    have hrew : (8 * D.faber.scale.p - 3 * T.delta) + (3 : ℚ) * T.delta =
        8 * D.faber.scale.p := by ring
    rw [← hrew, hcubic4]
    exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg _ hneg
  have hload1 :
      GCD369CubeHahnRegular.constantCoeff P1 = -62208 * r0 ^ 2 := by
    have hP := D.c1LoadPoly1_constantCoeff_coeff
    simpa only [P1] using
      (hP.trans (by
        rw [hu]
        exact (GCD369Cube_c1LoadRemainders_doubleRoot r0).1))
  have hload2 :
      GCD369CubeHahnRegular.constantCoeff P2 = 124416 * r0 ^ 3 := by
    have hP := D.c1LoadPoly2_constantCoeff_coeff
    simpa only [P2] using
      (hP.trans (by
        rw [hv]
        exact (GCD369Cube_c1LoadRemainders_doubleRoot r0).2.1))
  have hload3 : GCD369CubeHahnRegular.constantCoeff P3 = 0 := by
    simpa only [P3] using D.c1LoadPoly3_constantCoeff_coeff
  have hload4 :
      GCD369CubeHahnRegular.constantCoeff P4 = -1119744 * r0 ^ 5 := by
    have hP := D.c1LoadPoly4_constantCoeff_coeff
    simpa only [P4] using
      (hP.trans (by
        rw [hu, hv]
        exact (GCD369Cube_c1LoadRemainders_doubleRoot r0).2.2.2))
  have hweight1 :
      (c1w * P1).1.coeff (8 * D.faber.scale.p) =
        C1 * GCD369CubeHahnRegular.constantCoeff P1 := by
    simpa only [c1w] using
      D.faber.scale.weightedRegular_eight_constant_mul_coeff C1 P1
  have hweight2 :
      (c1w * P2).1.coeff (8 * D.faber.scale.p) =
        C1 * GCD369CubeHahnRegular.constantCoeff P2 := by
    simpa only [c1w] using
      D.faber.scale.weightedRegular_eight_constant_mul_coeff C1 P2
  have hweight3 :
      (c1w * P3).1.coeff (8 * D.faber.scale.p) =
        C1 * GCD369CubeHahnRegular.constantCoeff P3 := by
    simpa only [c1w] using
      D.faber.scale.weightedRegular_eight_constant_mul_coeff C1 P3
  have hweight4 :
      (c1w * P4).1.coeff (8 * D.faber.scale.p) =
        C1 * GCD369CubeHahnRegular.constantCoeff P4 := by
    simpa only [c1w] using
      D.faber.scale.weightedRegular_eight_constant_mul_coeff C1 P4
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hz := (D.faber.c1NCoeff_zero Rho1 Rho2 Rho3 Rho4
      hd hc7 hc5 hc4 hc3 hc2 hrho1 hrho2 hrho3 hrho4).1
    rw [hc1] at hz
    have hform :
        GCD369CubeFaberC1N1
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4 c1w =
          729 * N1 + c1w * P1 := rfl
    rw [hform] at hz
    change (729 * N1).1.coeff (8 * D.faber.scale.p) +
        (c1w * P1).1.coeff (8 * D.faber.scale.p) = 0 at hz
    rw [hweight1, hload1] at hz
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff (8 * D.faber.scale.p)) hexp1
    rw [hlambda, hshift1] at hc
    calc
      (-32 * (729 * R1)).1.coeff lambda + C1 * (-62208 * r0 ^ 2) =
          (729 * N1).1.coeff (8 * D.faber.scale.p) +
            C1 * (-62208 * r0 ^ 2) := by rw [← hc, hlambda]
      _ = 0 := by exact hz
  · have hz := (D.faber.c1NCoeff_zero Rho1 Rho2 Rho3 Rho4
      hd hc7 hc5 hc4 hc3 hc2 hrho1 hrho2 hrho3 hrho4).2.1
    rw [hc1] at hz
    have hform :
        GCD369CubeFaberC1N2
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4 c1w =
          2187 * N2 + c1w * P2 := rfl
    rw [hform] at hz
    change (2187 * N2).1.coeff (8 * D.faber.scale.p) +
        (c1w * P2).1.coeff (8 * D.faber.scale.p) = 0 at hz
    rw [hweight2, hload2] at hz
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff (8 * D.faber.scale.p)) hexp2
    rw [hlambda, hshift2] at hc
    calc
      (32 * (-1458 * R2)).1.coeff lambda + C1 * (124416 * r0 ^ 3) =
          (2187 * N2).1.coeff (8 * D.faber.scale.p) +
            C1 * (124416 * r0 ^ 3) := by rw [← hc, hlambda]
      _ = 0 := by exact hz
  · have hz := (D.faber.c1NCoeff_zero Rho1 Rho2 Rho3 Rho4
      hd hc7 hc5 hc4 hc3 hc2 hrho1 hrho2 hrho3 hrho4).2.2.1
    rw [hc1] at hz
    have hform :
        GCD369CubeFaberC1N3
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4 c1w =
          243 * N3 + c1w * P3 := rfl
    rw [hform] at hz
    change (243 * N3).1.coeff (8 * D.faber.scale.p) +
        (c1w * P3).1.coeff (8 * D.faber.scale.p) = 0 at hz
    rw [hweight3, hload3, mul_zero, add_zero] at hz
    have h243 : (243 * N3).1.coeff (8 * D.faber.scale.p) =
        (243 : k) * N3.1.coeff (8 * D.faber.scale.p) :=
      GCD369CubeHahnRegular.coeff_nat_mul
        243 N3 (8 * D.faber.scale.p)
    have hzN : N3.1.coeff (8 * D.faber.scale.p) = 0 :=
      (mul_eq_zero.mp (h243.symm.trans hz)).resolve_left (by norm_num)
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff (8 * D.faber.scale.p)) hexp3
    change N3.1.coeff (8 * D.faber.scale.p) =
        ((128 * R3) * H ^ 2).1.coeff (8 * D.faber.scale.p) -
          ((64 * A ^ 3) * H ^ 3).1.coeff (8 * D.faber.scale.p) at hc
    rw [hcubic3zero, sub_zero, hlambda, hshift3] at hc
    rw [hlambda] at hzN
    exact hc.symm.trans hzN
  · have hz := (D.faber.c1NCoeff_zero Rho1 Rho2 Rho3 Rho4
      hd hc7 hc5 hc4 hc3 hc2 hrho1 hrho2 hrho3 hrho4).2.2.2
    rw [hc1] at hz
    have hform :
        GCD369CubeFaberC1N4
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4 c1w =
          6561 * N4 + c1w * P4 := rfl
    rw [hform] at hz
    change (6561 * N4).1.coeff (8 * D.faber.scale.p) +
        (c1w * P4).1.coeff (8 * D.faber.scale.p) = 0 at hz
    rw [hweight4, hload4] at hz
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff (8 * D.faber.scale.p)) hexp4
    change (6561 * N4).1.coeff (8 * D.faber.scale.p) =
        ((32 * R4) * H ^ 2).1.coeff (8 * D.faber.scale.p) -
          ((314928 * (r * A + B) * A ^ 2) * H ^ 3).1.coeff
            (8 * D.faber.scale.p) at hc
    rw [hcubic4zero, sub_zero, hlambda, hshift4] at hc
    calc
      (32 * R4).1.coeff lambda + C1 * (-1119744 * r0 ^ 5) =
          (6561 * N4).1.coeff (8 * D.faber.scale.p) +
            C1 * (-1119744 * r0 ^ 5) := by rw [← hc, hlambda]
      _ = 0 := by exact hz
set_option maxHeartbeats 4000000 in
theorem TransverseFactor.doubleRoot_c1Load_inconsistent_of_lt_coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C1 Rho1 Rho2 Rho3 Rho4 : k)
    (hC1 : C1 ≠ 0)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant 0)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hrho1 : D.faber.rho1 = GCD369CubeHahnRegular.constant Rho1)
    (hrho2 : D.faber.rho2 = GCD369CubeHahnRegular.constant Rho2)
    (hrho3 : D.faber.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : D.faber.rho4 = GCD369CubeHahnRegular.constant Rho4)
    (r : GCD369CubeHahnRegular k) (r0 A0 : k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hu : D.u = -3 * r0 ^ 2) (hv : D.v = 2 * r0 ^ 3)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r0 * A0)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r0 ^ 2 * A0)
    (hroot : 2 * D.cubicU * r + 3 * D.cubicV = 0)
    (hdeltaP : T.delta < (8 * D.faber.scale.p) / 2)
    (hpDelta : 8 * D.faber.scale.p < 3 * T.delta) : False := by
  have hd0 : D.faber.d = 0 := by simpa using hd
  have hc70 : D.faber.c7 = 0 := by simpa using hc7
  have hc50 : D.faber.c5 = 0 := by simpa using hc5
  have hc40 : D.faber.c4 = 0 := by simpa using hc4
  have hc30 : D.faber.c3 = 0 := by simpa using hc3
  have hc20 : D.faber.c2 = 0 := by simpa using hc2
  have huc : GCD369CubeHahnRegular.constantCoeff D.cubicU = -3 * r0 ^ 2 := by
    rw [D.constantCoeff_cubicU, hu]
  have hhalf := T.doubleRoot_deviations_order_c1Load_half_lower_coeff
    hd0 hc70 hc50 hc40 hc30 hc20 hdeltaP hpDelta r r0 A0 hr0 hA0 hr huc
    hX hY hZ hroot
  let mu : ℚ := (8 * D.faber.scale.p) / 2 - T.delta
  have hmu : 0 < mu := by dsimp only [mu]; linarith
  let M : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial mu hmu.le
  let Dv : GCD369CubeHahnRegular k := D.cubicU + 3 * r ^ 2
  let B : GCD369CubeHahnRegular k := T.Yn - r * T.Xn
  let C : GCD369CubeHahnRegular k := T.Zn + 2 * r ^ 2 * T.Xn
  have hDhalf : (↑mu : WithTop ℚ) ≤ Dv.1.orderTop := by
    simpa only [mu, Dv] using hhalf.1
  have hBhalf : (↑mu : WithTop ℚ) ≤ B.1.orderTop := by
    simpa only [mu, B] using hhalf.2.1
  have hChalf : (↑mu : WithTop ℚ) ≤ C.1.orderTop := by
    simpa only [mu, C] using hhalf.2.2
  let Dn : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift Dv mu hDhalf
  let Bn : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift B mu hBhalf
  let Cn : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift C mu hChalf
  have hDfact : M * Dn = Dv := by
    simpa only [M, Dn] using GCD369CubeHahnRegular.monomial_mul_shift
      Dv mu hmu.le hDhalf
  have hBfact : M * Bn = B := by
    simpa only [M, Bn] using GCD369CubeHahnRegular.monomial_mul_shift
      B mu hmu.le hBhalf
  have hCfact : M * Cn = C := by
    simpa only [M, Cn] using GCD369CubeHahnRegular.monomial_mul_shift
      C mu hmu.le hChalf
  let Qn : GCD369CubeHahnRegular k := Cn + r * Bn
  let Row1 : GCD369CubeHahnRegular k :=
    T.Xn ^ 2 * Dv - 2 * T.Xn * B * r - B ^ 2 - 2 * T.Xn * C
  let Row2 : GCD369CubeHahnRegular k :=
    2 * T.Xn ^ 2 * r * Dv - 3 * T.Xn * B * r ^ 2 - 3 * T.Xn * C * r +
      3 * T.Xn * B * Dv - 3 * B * C
  have hRow1 : (↑(2 * mu) : WithTop ℚ) ≤ Row1.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro e he
    have he' : e < 2 * mu := WithTop.coe_lt_coe.mp he
    by_cases he0 : 0 ≤ e
    · have hrows := T.doubleRoot_row123Coeffs_zero_before_c1_coeff
        hd0 hc70 hc50 hc40 hc30 hc20 r hroot e he0 (by
          dsimp only [mu] at he'
          nlinarith [hpDelta]) (by
          dsimp only [mu] at he'
          have htwice : 2 * ((8 * D.faber.scale.p) / 2 - T.delta) =
              8 * D.faber.scale.p - 2 * T.delta := by ring
          linarith)
      simpa only [Row1, Dv, B, C] using hrows.1
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg Row1
        (lt_of_not_ge he0)
  have hRow2 : (↑(2 * mu) : WithTop ℚ) ≤ Row2.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro e he
    have he' : e < 2 * mu := WithTop.coe_lt_coe.mp he
    by_cases he0 : 0 ≤ e
    · have hrows := T.doubleRoot_row123Coeffs_zero_before_c1_coeff
        hd0 hc70 hc50 hc40 hc30 hc20 r hroot e he0 (by
          dsimp only [mu] at he'
          nlinarith [hpDelta]) (by
          dsimp only [mu] at he'
          have htwice : 2 * ((8 * D.faber.scale.p) / 2 - T.delta) =
              8 * D.faber.scale.p - 2 * T.delta := by ring
          linarith)
      simpa only [Row2, Dv, B, C] using hrows.2.1
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg Row2
        (lt_of_not_ge he0)
  let FRow1 : GCD369CubeHahnRegular k :=
    M * (T.Xn ^ 2 * Dn - 2 * T.Xn * Qn) - M ^ 2 * Bn ^ 2
  let FRow2 : GCD369CubeHahnRegular k :=
    M * (2 * T.Xn ^ 2 * r * Dn - 3 * T.Xn * r * Qn) +
      M ^ 2 * (3 * T.Xn * Bn * Dn - 3 * Bn * Cn)
  have hfac1 : Row1 = FRow1 := by
    dsimp only [Row1, FRow1, Qn]
    rw [← hDfact, ← hBfact, ← hCfact]
    ring
  have hfac2 : Row2 = FRow2 := by
    dsimp only [Row2, FRow2, Qn]
    rw [← hDfact, ← hBfact, ← hCfact]
    ring
  have hFRow1 : (↑(2 * mu) : WithTop ℚ) ≤ FRow1.1.orderTop :=
    hRow1.trans_eq (congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.orderTop) hfac1)
  have hFRow2 : (↑(2 * mu) : WithTop ℚ) ≤ FRow2.1.orderTop :=
    hRow2.trans_eq (congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.orderTop) hfac2)
  have hlift :=
    GCD369CubeHahnRegular.doubleBlowup_kernelRemainders_order_lower_of_factoredRows
      mu hmu T.Xn r Dn Bn Cn (by rw [hX]; exact hA0)
      (by rw [hr]; exact hr0)
      (by simpa only [FRow1, M, Qn] using hFRow1)
      (by simpa only [FRow2, M, Qn] using hFRow2)
  let d : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift Dn mu hlift.1
  let q : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift Qn mu hlift.2
  have hdnfact : M * d = Dn := by
    simpa only [M, d] using GCD369CubeHahnRegular.monomial_mul_shift
      Dn mu hmu.le hlift.1
  have hqnfact : M * q = Qn := by
    simpa only [M, q] using GCD369CubeHahnRegular.monomial_mul_shift
      Qn mu hmu.le hlift.2
  let Dq : GCD369CubeHahnRegular k := M ^ 2 * d
  let Bq : GCD369CubeHahnRegular k := M * Bn
  let Cq : GCD369CubeHahnRegular k := M ^ 2 * q - M * r * Bn
  have hDq : Dv = Dq := by
    calc
      Dv = M * Dn := hDfact.symm
      _ = M * (M * d) := congrArg (fun z => M * z) hdnfact.symm
      _ = Dq := by dsimp only [Dq]; ring
  have hBq : B = Bq := by simpa only [Bq] using hBfact.symm
  have hCn : Cn = M * q - r * Bn := by
    dsimp only [Qn] at hqnfact
    linear_combination -hqnfact
  have hCq : C = Cq := by
    calc
      C = M * Cn := hCfact.symm
      _ = M * (M * q - r * Bn) := congrArg (fun z => M * z) hCn
      _ = Cq := by dsimp only [Cq]; ring
  let Row3 : GCD369CubeHahnRegular k :=
    -2 * T.Xn ^ 2 * r ^ 2 * Dv + 6 * B ^ 2 * r ^ 2 +
      2 * T.Xn ^ 2 * Dv ^ 2 - 2 * B ^ 2 * Dv - 4 * T.Xn * C * Dv + 3 * C ^ 2
  let Row4 : GCD369CubeHahnRegular k :=
    4374 * (-3 * r ^ 2 + Dv) *
      (T.Xn * B * r ^ 2 + 2 * B ^ 2 * r + T.Xn * C * r +
        3 * T.Xn * B * Dv - 3 * B * C)
  have hu' : D.u = -3 * GCD369CubeHahnRegular.constantCoeff r ^ 2 := by
    rw [hr]
    exact hu
  have hv' : D.v = 2 * GCD369CubeHahnRegular.constantCoeff r ^ 3 := by
    rw [hr]
    exact hv
  have hload := T.doubleRoot_c1Load_coeff_of_lt
    C1 Rho1 Rho2 Rho3 Rho4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
    r hroot hu' hv' hdeltaP hpDelta
  dsimp only at hload
  have hlambda : 8 * D.faber.scale.p - 2 * T.delta = 2 * mu := by
    dsimp only [mu]
    ring
  rw [hlambda, hr] at hload
  have hload1 : (-32 * (729 * Row1)).1.coeff (2 * mu) +
      C1 * (-62208 * r0 ^ 2) = 0 := by
    simpa only [Row1, Dv, B, C] using hload.1
  have hload2 : (32 * (-1458 * Row2)).1.coeff (2 * mu) +
      C1 * (124416 * r0 ^ 3) = 0 := by
    simpa only [Row2, Dv, B, C] using hload.2.1
  have hload3 : (128 * Row3).1.coeff (2 * mu) = 0 := by
    simpa only [Row3, Dv, B, C] using hload.2.2.1
  have hload4 : (32 * Row4).1.coeff (2 * mu) +
      C1 * (-1119744 * r0 ^ 5) = 0 := by
    simpa only [Row4, Dv, B, C] using hload.2.2.2
  dsimp only [Row1, Row2, Row3, Row4] at hload1 hload2 hload3 hload4
  rw [hDq, hBq, hCq] at hload1 hload2 hload3 hload4
  let QR1 : GCD369CubeHahnRegular k :=
    T.Xn ^ 2 * Dq - 2 * T.Xn * Bq * r - Bq ^ 2 - 2 * T.Xn * Cq
  let QR2 : GCD369CubeHahnRegular k :=
    2 * T.Xn ^ 2 * r * Dq - 3 * T.Xn * Bq * r ^ 2 -
      3 * T.Xn * Cq * r + 3 * T.Xn * Bq * Dq - 3 * Bq * Cq
  let QR3 : GCD369CubeHahnRegular k :=
    -2 * T.Xn ^ 2 * r ^ 2 * Dq + 6 * Bq ^ 2 * r ^ 2 +
      2 * T.Xn ^ 2 * Dq ^ 2 - 2 * Bq ^ 2 * Dq -
        4 * T.Xn * Cq * Dq + 3 * Cq ^ 2
  let QR4 : GCD369CubeHahnRegular k :=
    4374 * (-3 * r ^ 2 + Dq) *
      (T.Xn * Bq * r ^ 2 + 2 * Bq ^ 2 * r + T.Xn * Cq * r +
        3 * T.Xn * Bq * Dq - 3 * Bq * Cq)
  have hload1q : (-32 * (729 * QR1)).1.coeff (2 * mu) +
      C1 * (-62208 * r0 ^ 2) = 0 := by
    simpa only [QR1] using hload1
  have hload2q : (32 * (-1458 * QR2)).1.coeff (2 * mu) +
      C1 * (124416 * r0 ^ 3) = 0 := by
    simpa only [QR2] using hload2
  have hload3q : (128 * QR3).1.coeff (2 * mu) = 0 := by
    simpa only [QR3] using hload3
  have hload4q : (32 * QR4).1.coeff (2 * mu) +
      C1 * (-1119744 * r0 ^ 5) = 0 := by
    simpa only [QR4] using hload4
  have hquad := GCD369CubeHahnRegular.doubleBlowup_quadratic_coefficients
    mu hmu T.Xn r d Bn q
  have hq1 : QR1.1.coeff (2 * mu) =
      A0 ^ 2 * GCD369CubeHahnRegular.constantCoeff d -
        2 * A0 * GCD369CubeHahnRegular.constantCoeff q -
          GCD369CubeHahnRegular.constantCoeff Bn ^ 2 := by
    simpa only [QR1, Dq, Bq, Cq, M, hX, hr] using hquad.1
  have hq2 : QR2.1.coeff (2 * mu) =
      2 * A0 ^ 2 * r0 * GCD369CubeHahnRegular.constantCoeff d -
        3 * A0 * r0 * GCD369CubeHahnRegular.constantCoeff q +
          3 * r0 * GCD369CubeHahnRegular.constantCoeff Bn ^ 2 := by
    simpa only [QR2, Dq, Bq, Cq, M, hX, hr] using hquad.2.1
  have hq3 : QR3.1.coeff (2 * mu) =
      -2 * A0 ^ 2 * r0 ^ 2 * GCD369CubeHahnRegular.constantCoeff d +
        9 * r0 ^ 2 * GCD369CubeHahnRegular.constantCoeff Bn ^ 2 := by
    simpa only [QR3, Dq, Bq, Cq, M, hX, hr] using hquad.2.2
  have hq4 : QR4.1.coeff (2 * mu) =
      -13122 * A0 * r0 ^ 3 * GCD369CubeHahnRegular.constantCoeff q -
        65610 * r0 ^ 3 * GCD369CubeHahnRegular.constantCoeff Bn ^ 2 := by
    simpa only [QR4, Dq, Bq, Cq, M, hX, hr] using
      (GCD369CubeHahnRegular.doubleBlowup_quadratic_row4_coefficient
        mu hmu T.Xn r d Bn q)
  have hs1 : -32 * (729 * QR1) = (-23328 : ℤ) * QR1 := by ring
  have hs2 : 32 * (-1458 * QR2) = (-46656 : ℤ) * QR2 := by ring
  rw [hs1, GCD369CubeHahnRegular.coeff_int_mul, hq1] at hload1q
  rw [hs2, GCD369CubeHahnRegular.coeff_int_mul, hq2] at hload2q
  have hs3 : (128 * QR3).1.coeff (2 * mu) =
      (128 : k) * QR3.1.coeff (2 * mu) :=
    GCD369CubeHahnRegular.coeff_nat_mul 128 QR3 (2 * mu)
  rw [hs3, hq3] at hload3q
  have hs4 : (32 * QR4).1.coeff (2 * mu) =
      (32 : k) * QR4.1.coeff (2 * mu) :=
    GCD369CubeHahnRegular.coeff_nat_mul 32 QR4 (2 * mu)
  rw [hs4, hq4] at hload4q
  apply GCD369CubeDoubleBlowup_c1Load_quadratic_beforeCubic_inconsistent
    A0 (GCD369CubeHahnRegular.constantCoeff Bn)
      (GCD369CubeHahnRegular.constantCoeff q) r0
      (GCD369CubeHahnRegular.constantCoeff d) C1 hr0 hC1
  · linear_combination hload1q
  · linear_combination hload2q
  · exact (mul_eq_zero.mp hload3q).resolve_left (by norm_num)
  · linear_combination hload4q
theorem TransverseFactor.zeroLoadLeadingRows_before_c1_coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (hd : D.faber.d = 0)
    (hc7 : D.faber.c7 = 0)
    (hc5 : D.faber.c5 = 0)
    (hc4 : D.faber.c4 = 0)
    (hc3 : D.faber.c3 = 0)
    (hc2 : D.faber.c2 = 0)
    (hearly : 2 * T.delta < 8 * D.faber.scale.p) :
    GCD369CubeNormalRow1
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u = 0 ∧
    GCD369CubeNormalRow2
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v = 0 ∧
    GCD369CubeNormalRow3
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v = 0 ∧
    GCD369CubeNormalRow4
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v = 0 := by
  have hz := D.faber.zeroHighNCoeff_zero_before_c1 hd hc7 hc5 hc4 hc3 hc2
    (2 * T.delta) (mul_nonneg (by norm_num) T.hdelta.le) hearly
  rcases hz with ⟨h1, h2, h3, h4⟩
  constructor
  · have hc :
        (729 * GCD369CubeFaberN1
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4).1.coeff (2 * T.delta) =
        -32 * GCD369CubeNormalRow1
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u := by
      convert T.zeroHighN1Coeff using 1 <;> norm_num
    rw [hc] at h1
    exact (mul_eq_zero.mp h1).resolve_left (by norm_num)
  constructor
  · have hc :
        (2187 * GCD369CubeFaberN2
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4).1.coeff (2 * T.delta) =
        32 * GCD369CubeNormalRow2
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v := by
      convert T.zeroHighN2Coeff using 1 <;> norm_num
    rw [hc] at h2
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  constructor
  · have hcoeff :
        (243 * GCD369CubeFaberN3
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4).1.coeff (2 * T.delta) =
        (243 : k) *
          (GCD369CubeFaberN3
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4).1.coeff (2 * T.delta) := by
      exact GCD369CubeHahnRegular.coeff_nat_mul 243 _ _
    rw [hcoeff] at h3
    have h3' :
        (GCD369CubeFaberN3
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4).1.coeff (2 * T.delta) = 0 :=
      (mul_eq_zero.mp h3).resolve_left (by norm_num)
    have hc :
        (GCD369CubeFaberN3
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4).1.coeff (2 * T.delta) =
        128 * GCD369CubeNormalRow3
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v := by
      convert T.zeroHighN3Coeff using 1 <;> norm_num
    rw [hc] at h3'
    exact (mul_eq_zero.mp h3').resolve_left (by norm_num)
  · have hc :
        (6561 * GCD369CubeFaberN4
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4).1.coeff (2 * T.delta) =
        32 * GCD369CubeNormalRow4
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v := by
      convert T.zeroHighN4Coeff using 1 <;> norm_num
    rw [hc] at h4
    exact (mul_eq_zero.mp h4).resolve_left (by norm_num)

/-- The first transverse residue supplies the double-root chart, so the
strict active-`c1` middle window is inconsistent at coefficient level. -/
theorem TransverseScale.c1_singular_middle_inconsistent_coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C1 Rho1 Rho2 Rho3 Rho4 : k)
    (hC1 : C1 ≠ 0)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant 0)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hrho1 : D.faber.rho1 = GCD369CubeHahnRegular.constant Rho1)
    (hrho2 : D.faber.rho2 = GCD369CubeHahnRegular.constant Rho2)
    (hrho3 : D.faber.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : D.faber.rho4 = GCD369CubeHahnRegular.constant Rho4)
    (hdeltaP : T.delta < (8 * D.faber.scale.p) / 2)
    (hpDelta : 8 * D.faber.scale.p < 3 * T.delta) : False := by
  have hd0 : D.faber.d = 0 := by simpa using hd
  have hc70 : D.faber.c7 = 0 := by simpa using hc7
  have hc50 : D.faber.c5 = 0 := by simpa using hc5
  have hc40 : D.faber.c4 = 0 := by simpa using hc4
  have hc30 : D.faber.c3 = 0 := by simpa using hc3
  have hc20 : D.faber.c2 = 0 := by simpa using hc2
  have hearly : 2 * T.delta < 8 * D.faber.scale.p := by
    nlinarith [hdeltaP]
  obtain ⟨h1, h2, h3, h4⟩ :=
    T.factor.zeroLoadLeadingRows_before_c1_coeff hd0 hc70 hc50 hc40 hc30 hc20
      (by simpa only [TransverseScale.factor] using hearly)
  obtain ⟨r0, hX, hu, hv, hY, hZ⟩ :=
    GCD369CubeZeroLoadNormal_parametrization
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn)
      D.u D.v T.hleading h1 h2 h3 h4
  have hr0 : r0 ≠ 0 := by
    intro hrzero
    have hu0 : D.u = 0 := by rw [hu, hrzero]; norm_num
    have hv0 : D.v = 0 := by rw [hv, hrzero]; norm_num
    exact D.hprojective.elim (fun h => h hu0) (fun h => h hv0)
  have hUne : GCD369CubeHahnRegular.constantCoeff D.cubicU ≠ 0 := by
    rw [D.constantCoeff_cubicU, hu]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hr0)
  let r : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.movingDoubleRoot D.cubicU D.cubicV hUne
  have huc : GCD369CubeHahnRegular.constantCoeff D.cubicU =
      -3 * r0 ^ 2 := by
    rw [D.constantCoeff_cubicU, hu]
  have hvc : GCD369CubeHahnRegular.constantCoeff D.cubicV =
      2 * r0 ^ 3 := by
    rw [D.constantCoeff_cubicV, hv]
  have hr : GCD369CubeHahnRegular.constantCoeff r = r0 := by
    exact GCD369CubeHahnRegular.constantCoeff_movingDoubleRoot
      D.cubicU D.cubicV hUne r0 huc hvc hr0
  have hroot : 2 * D.cubicU * r + 3 * D.cubicV = 0 := by
    exact GCD369CubeHahnRegular.movingDoubleRoot_relation
      D.cubicU D.cubicV hUne
  exact T.factor.doubleRoot_c1Load_inconsistent_of_lt_coeff
    C1 Rho1 Rho2 Rho3 Rho4 hC1
    hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
    r r0 (GCD369CubeHahnRegular.constantCoeff T.Xn) hr0 hX hr hu hv
    (by rfl) hY hZ hroot
    (by simpa only [TransverseScale.factor] using hdeltaP)
    (by simpa only [TransverseScale.factor] using hpDelta)

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubePolynomialSource

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Generic source-facing active `c1` middle theorem in the explicit
`c3 = 0` gauge. -/
theorem infinity_c1_eq_zero_singular_middle
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hd0 : S.faberConstantParameters.d = 0)
    (hc70 : S.faberConstantParameters.c7 = 0)
    (hc50 : S.faberConstantParameters.c5 = 0)
    (hc40 : S.faberConstantParameters.c4 = 0)
    (hc30 : S.faberConstantParameters.c3 = 0)
    (hc20 : S.faberConstantParameters.c2 = 0)
    (hmiddle : 2 * T.delta <
      8 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p)
    (hpDelta :
      8 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p <
        3 * T.delta) :
    S.faberConstantParameters.c1 = 0 := by
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let D := S.infinityCommonCoefficientData hsdegree
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  obtain ⟨hd, hc7, hc5, hc4, hc3, hc2, hc1,
      hr1, hr2, hr3, hr4⟩ :=
    S.infinityFaberPoleData_constant_loads hpole
  have hdD : D.faber.d = GCD369CubeHahnRegular.constant 0 := by
    have h := hd
    rw [hd0] at h
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using h
  have hc7D : D.faber.c7 = GCD369CubeHahnRegular.constant 0 := by
    have h := hc7
    rw [hc70] at h
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using h
  have hc5D : D.faber.c5 = GCD369CubeHahnRegular.constant 0 := by
    have h := hc5
    rw [hc50] at h
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using h
  have hc4D : D.faber.c4 = GCD369CubeHahnRegular.constant 0 := by
    have h := hc4
    rw [hc40] at h
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using h
  have hc3D : D.faber.c3 = GCD369CubeHahnRegular.constant 0 := by
    have h := hc3
    rw [hc30] at h
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using h
  have hc2D : D.faber.c2 = GCD369CubeHahnRegular.constant 0 := by
    have h := hc2
    rw [hc20] at h
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using h
  have hc1D : D.faber.c1 = GCD369CubeHahnRegular.constant P.c1 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc1
  have hr1D : D.faber.rho1 = GCD369CubeHahnRegular.constant R.rho1 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree] using hr1
  have hr2D : D.faber.rho2 = GCD369CubeHahnRegular.constant R.rho2 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree] using hr2
  have hr3D : D.faber.rho3 = GCD369CubeHahnRegular.constant R.rho3 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree] using hr3
  have hr4D : D.faber.rho4 = GCD369CubeHahnRegular.constant R.rho4 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree] using hr4
  have hdeltaP : T.delta < (8 * D.faber.scale.p) / 2 := by
    dsimp only [D]
    nlinarith
  by_contra hPc1
  exact T.c1_singular_middle_inconsistent_coeff
    P.c1 R.rho1 R.rho2 R.rho3 R.rho4 hPc1
    hdD hc7D hc5D hc4D hc3D hc2D hc1D hr1D hr2D hr3D hr4D
    hdeltaP (by simpa only [D] using hpDelta)

/-- Target-normalized active-`c1` wrapper with canonical `c3 = 0`. -/
theorem targetNormalized_infinity_c1_eq_zero_singular_middle
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
    (hmiddle : let U := S.targetNormalizedSource
      let hsdegreeU : U.s.natDegree = 0 := by
        simpa [U, targetNormalizedSource] using hsdegree
      2 * T.delta <
        8 * (U.infinityCommonCoefficientData hsdegreeU).faber.scale.p)
    (hpDelta : let U := S.targetNormalizedSource
      let hsdegreeU : U.s.natDegree = 0 := by
        simpa [U, targetNormalizedSource] using hsdegree
      8 * (U.infinityCommonCoefficientData hsdegreeU).faber.scale.p <
        3 * T.delta) :
    S.targetNormalizedSource.faberConstantParameters.c1 = 0 := by
  let U := S.targetNormalizedSource
  have hsdegreeU : U.s.natDegree = 0 := by
    simpa [U, targetNormalizedSource] using hsdegree
  let Q := U.faberConstantParameters
  obtain ⟨hQd, _hQc7, _hQc6, _hQc5, _hQc4, hQc3, _hQc2,
      _hQc1, _hQc0⟩ := S.targetNormalizedCanonicalParameters hd0
  apply U.infinity_c1_eq_zero_singular_middle hsdegreeU T
  · simpa only [Q, U] using hQd
  · simpa only [Q, U] using hc70
  · simpa only [Q, U] using hc50
  · simpa only [Q, U] using hc40
  · simpa only [Q, U] using hQc3
  · simpa only [Q, U] using hc20
  · simpa only [U, hsdegreeU] using hmiddle
  · simpa only [U, hsdegreeU] using hpDelta

end GCD369CubePolynomialSource

#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseFactor.doubleRoot_row123Coeffs_zero_before_c1_coeff
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseFactor.doubleRoot_firstCommonScale_not_below_c1Load_half_coeff
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseFactor.doubleRoot_deviations_order_c1Load_half_lower_coeff
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseFactor.doubleRoot_c1Load_coeff_of_lt
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseFactor.doubleRoot_c1Load_inconsistent_of_lt_coeff
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.c1_singular_middle_inconsistent_coeff
#print axioms GCD369CubePolynomialSource.infinity_c1_eq_zero_singular_middle
#print axioms
  GCD369CubePolynomialSource.targetNormalized_infinity_c1_eq_zero_singular_middle
