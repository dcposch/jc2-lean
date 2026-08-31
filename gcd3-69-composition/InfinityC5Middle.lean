import InfinityC7Middle
import FiniteC5EarlyNormal
import FiniteDoubleC5LoadLift

/-! # The strict middle weight-four load at infinity

After `d = c7 = 0`, this file treats the window
`2 * delta < 4 * p < 3 * delta`.  The coefficient-only zero-load rows force
the moving-double-root deviations to the residual half-load scale, where the
active `c5` equations form an inconsistent quadratic system.
-/

noncomputable section

namespace GCD369CubeHahnCommonCoefficientData

/-- Before the weight-four load, the first three moving-root row
coefficients vanish below the intrinsic cubic residual cutoff. -/
theorem TransverseFactor.doubleRoot_row123Coeffs_zero_before_c5_coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (hd : D.faber.d = 0) (hc7 : D.faber.c7 = 0)
    (r : GCD369CubeHahnRegular k)
    (hroot : 2 * D.cubicU * r + 3 * D.cubicV = 0)
    (e : ℚ) (he : 0 ≤ e) (heDelta : e < T.delta)
    (hearly : 2 * T.delta + e < 4 * D.faber.scale.p) :
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
  have hz := D.faber.zeroHighNCoeff_zero_before_c5 hd hc7
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
`2p-delta`. -/
theorem TransverseFactor.doubleRoot_firstCommonScale_not_below_c5Load_half_coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (hd : D.faber.d = 0) (hc7 : D.faber.c7 = 0)
    (_hdeltaP : T.delta < 2 * D.faber.scale.p)
    (hpDelta : 4 * D.faber.scale.p < 3 * T.delta)
    (r : GCD369CubeHahnRegular k)
    (hA : GCD369CubeHahnRegular.constantCoeff T.Xn ≠ 0)
    (hr : GCD369CubeHahnRegular.constantCoeff r ≠ 0)
    (hroot : 2 * D.cubicU * r + 3 * D.cubicV = 0)
    (J : GCD369CubeHahnRegular.TripleScale
      (D.cubicU + 3 * r ^ 2) (T.Yn - r * T.Xn)
      (T.Zn + 2 * r ^ 2 * T.Xn)) :
    ¬ J.mu < 2 * D.faber.scale.p - T.delta := by
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
    · have hs := T.doubleRoot_row123Coeffs_zero_before_c5_coeff hd hc7
        r hroot q hq0 (by linarith) (by linarith)
      simpa only [R1, A, Dv, B, C] using hs.1
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg R1 (lt_of_not_ge hq0)
  have hR2 : (↑(2 * J.mu) : WithTop ℚ) ≤ R2.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro q hq
    have hq' := WithTop.coe_lt_coe.mp hq
    by_cases hq0 : 0 ≤ q
    · have hs := T.doubleRoot_row123Coeffs_zero_before_c5_coeff hd hc7
        r hroot q hq0 (by linarith) (by linarith)
      simpa only [R2, A, Dv, B, C] using hs.2.1
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg R2 (lt_of_not_ge hq0)
  have hs := T.doubleRoot_row123Coeffs_zero_before_c5_coeff hd hc7
    r hroot (2 * J.mu) (by linarith [J.hmu]) htwoMuDelta (by linarith)
  exact GCD369CubeHahnRegular.doubleBlowup_quadratic_inconsistent
    A r Dv B C J (by simpa only [A] using hA) hr
    (by simpa only [R1] using hR1) (by simpa only [R2] using hR2)
    (by simpa only [R1, A, Dv, B, C] using hs.1)
    (by simpa only [R2, A, Dv, B, C] using hs.2.1)
    (by simpa only [R3, A, Dv, B, C] using hs.2.2)

/-- The first-scale exclusion gives simultaneous residual half-load order
bounds for all three moving-root deviations. -/
theorem TransverseFactor.doubleRoot_deviations_order_c5Load_half_lower_coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (hd : D.faber.d = 0) (hc7 : D.faber.c7 = 0)
    (hdeltaP : T.delta < 2 * D.faber.scale.p)
    (hpDelta : 4 * D.faber.scale.p < 3 * T.delta)
    (r : GCD369CubeHahnRegular k) (r0 A0 : k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hu : GCD369CubeHahnRegular.constantCoeff D.cubicU = -3 * r0 ^ 2)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r0 * A0)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r0 ^ 2 * A0)
    (hroot : 2 * D.cubicU * r + 3 * D.cubicV = 0) :
    (↑(2 * D.faber.scale.p - T.delta) : WithTop ℚ) ≤
        (D.cubicU + 3 * r ^ 2).1.orderTop ∧
      (↑(2 * D.faber.scale.p - T.delta) : WithTop ℚ) ≤
        (T.Yn - r * T.Xn).1.orderTop ∧
      (↑(2 * D.faber.scale.p - T.delta) : WithTop ℚ) ≤
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
    have hnot := T.doubleRoot_firstCommonScale_not_below_c5Load_half_coeff
      hd hc7 hdeltaP hpDelta r (by rw [hX]; exact hA0)
      (by rw [hr]; exact hr0) hroot J
    have hmu : 2 * D.faber.scale.p - T.delta ≤ J.mu := le_of_not_gt hnot
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
    have hcoe : (↑(2 * D.faber.scale.p - T.delta) : WithTop ℚ) ≤
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

/-- At exponent `4p`, the four invariant equations are the shifted
quadratic double-root rows plus the pure weight-four `c5` load. -/
theorem TransverseFactor.doubleRoot_c5Load_coeff_of_lt
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hrho1 : D.faber.rho1 = GCD369CubeHahnRegular.constant Rho1)
    (hrho2 : D.faber.rho2 = GCD369CubeHahnRegular.constant Rho2)
    (hrho3 : D.faber.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : D.faber.rho4 = GCD369CubeHahnRegular.constant Rho4)
    (r : GCD369CubeHahnRegular k)
    (hroot : 2 * D.cubicU * r + 3 * D.cubicV = 0)
    (hu : D.u = -3 * GCD369CubeHahnRegular.constantCoeff r ^ 2)
    (hv : D.v = 2 * GCD369CubeHahnRegular.constantCoeff r ^ 3)
    (_hpLT : T.delta < 2 * D.faber.scale.p)
    (hpGT : 4 * D.faber.scale.p < 3 * T.delta) :
    let A := T.Xn
    let Dv := D.cubicU + 3 * r ^ 2
    let B := T.Yn - r * A
    let C := T.Zn + 2 * r ^ 2 * A
    let R1 := A ^ 2 * Dv - 2 * A * B * r - B ^ 2 - 2 * A * C
    let R2 := 2 * A ^ 2 * r * Dv - 3 * A * B * r ^ 2 -
      3 * A * C * r + 3 * A * B * Dv - 3 * B * C
    let R3 := -2 * A ^ 2 * r ^ 2 * Dv + 6 * B ^ 2 * r ^ 2 +
      2 * A ^ 2 * Dv ^ 2 - 2 * B ^ 2 * Dv - 4 * A * C * Dv + 3 * C ^ 2
    let R4 := 4374 * (-3 * r ^ 2 + Dv) *
      (A * B * r ^ 2 + 2 * B ^ 2 * r + A * C * r +
        3 * A * B * Dv - 3 * B * C)
    let lambda := 4 * D.faber.scale.p - 2 * T.delta
    let r0 := GCD369CubeHahnRegular.constantCoeff r
    ((-32 * (729 * R1)).1.coeff lambda + C5 * (241920 * r0 ^ 6) = 0) ∧
    ((32 * (-1458 * R2)).1.coeff lambda + C5 * (-622080 * r0 ^ 7) = 0) ∧
    ((128 * R3).1.coeff lambda = 0) ∧
    ((32 * R4).1.coeff lambda + C5 * (7257600 * r0 ^ 9) = 0) := by
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
  let R4 : GCD369CubeHahnRegular k := 4374 * (-3 * r ^ 2 + Dv) *
    (A * B * r ^ 2 + 2 * B ^ 2 * r + A * C * r +
      3 * A * B * Dv - 3 * B * C)
  let lambda : ℚ := 4 * D.faber.scale.p - 2 * T.delta
  let r0 : k := GCD369CubeHahnRegular.constantCoeff r
  let N1 : GCD369CubeHahnRegular k := GCD369CubeFaberN1
    D.faber.scale.regular0 D.faber.scale.regular1 D.faber.scale.regular2
    D.faber.scale.regular3 D.faber.scale.regular4
  let N2 : GCD369CubeHahnRegular k := GCD369CubeFaberN2
    D.faber.scale.regular0 D.faber.scale.regular1 D.faber.scale.regular2
    D.faber.scale.regular3 D.faber.scale.regular4
  let N3 : GCD369CubeHahnRegular k := GCD369CubeFaberN3
    D.faber.scale.regular0 D.faber.scale.regular1 D.faber.scale.regular2
    D.faber.scale.regular3 D.faber.scale.regular4
  let N4 : GCD369CubeHahnRegular k := GCD369CubeFaberN4
    D.faber.scale.regular0 D.faber.scale.regular1 D.faber.scale.regular2
    D.faber.scale.regular3 D.faber.scale.regular4
  let P1 : GCD369CubeHahnRegular k :=
    51840 * D.faber.scale.regular0 -
      8640 * D.faber.scale.regular2 * D.faber.scale.regular4 -
      4320 * D.faber.scale.regular3 ^ 2 +
      1680 * D.faber.scale.regular4 ^ 3
  let P2 : GCD369CubeHahnRegular k :=
    -25920 * D.faber.scale.regular1 * D.faber.scale.regular4 -
      25920 * D.faber.scale.regular2 * D.faber.scale.regular3 +
      15120 * D.faber.scale.regular3 * D.faber.scale.regular4 ^ 2
  let P3 : GCD369CubeHahnRegular k :=
    -34560 * D.faber.scale.regular1 * D.faber.scale.regular3 -
      17280 * D.faber.scale.regular2 ^ 2 +
      14400 * D.faber.scale.regular2 * D.faber.scale.regular4 ^ 2 +
      17280 * D.faber.scale.regular3 ^ 2 * D.faber.scale.regular4 -
      2520 * D.faber.scale.regular4 ^ 4
  let P4 : GCD369CubeHahnRegular k :=
    -233280 * D.faber.scale.regular1 * D.faber.scale.regular2 +
      58320 * D.faber.scale.regular1 * D.faber.scale.regular4 ^ 2 +
      155520 * D.faber.scale.regular2 * D.faber.scale.regular3 *
        D.faber.scale.regular4 +
      25920 * D.faber.scale.regular3 ^ 3 -
      45360 * D.faber.scale.regular3 * D.faber.scale.regular4 ^ 3
  let c5w : GCD369CubeHahnRegular k := D.faber.scale.weightedRegular 4
    (GCD369CubeHahnRegular.constant C5)
  have hlambda : 4 * D.faber.scale.p = lambda + (2 : ℚ) * T.delta := by
    dsimp only [lambda]; ring
  have hexp := T.doubleRoot_zeroHigh_expansions_coeff r hroot
  have hexp1 : 729 * N1 = (-32 * (729 * R1)) * H ^ 2 := by
    simpa only [N1, R1, A, Dv, B, C, H] using hexp.1
  have hexp2 : 2187 * N2 = (32 * (-1458 * R2)) * H ^ 2 := by
    simpa only [N2, R2, A, Dv, B, C, H] using hexp.2.1
  have hexp3 : N3 = (128 * R3) * H ^ 2 - (64 * A ^ 3) * H ^ 3 := by
    simpa only [N3, R3, A, Dv, B, C, H] using hexp.2.2.1
  have hexp4 : 6561 * N4 = (32 * R4) * H ^ 2 -
      (314928 * (r * A + B) * A ^ 2) * H ^ 3 := by
    simpa only [N4, R4, A, Dv, B, C, H] using hexp.2.2.2
  have hs1 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (-32 * (729 * R1)) T.delta lambda T.hdelta.le 2
  have hs2 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (32 * (-1458 * R2)) T.delta lambda T.hdelta.le 2
  have hs3 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (128 * R3) T.delta lambda T.hdelta.le 2
  have hs4 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (32 * R4) T.delta lambda T.hdelta.le 2
  change ((-32 * (729 * R1)) * H ^ 2).1.coeff
    (lambda + 2 * T.delta) = (-32 * (729 * R1)).1.coeff lambda at hs1
  change ((32 * (-1458 * R2)) * H ^ 2).1.coeff
    (lambda + 2 * T.delta) = (32 * (-1458 * R2)).1.coeff lambda at hs2
  change ((128 * R3) * H ^ 2).1.coeff
    (lambda + 2 * T.delta) = (128 * R3).1.coeff lambda at hs3
  change ((32 * R4) * H ^ 2).1.coeff
    (lambda + 2 * T.delta) = (32 * R4).1.coeff lambda at hs4
  have hc3s := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (64 * A ^ 3) T.delta (4 * D.faber.scale.p - 3 * T.delta) T.hdelta.le 3
  have hc4s := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (314928 * (r * A + B) * A ^ 2) T.delta
      (4 * D.faber.scale.p - 3 * T.delta) T.hdelta.le 3
  change ((64 * A ^ 3) * H ^ 3).1.coeff
    ((4 * D.faber.scale.p - 3 * T.delta) + 3 * T.delta) =
      (64 * A ^ 3).1.coeff (4 * D.faber.scale.p - 3 * T.delta) at hc3s
  change ((314928 * (r * A + B) * A ^ 2) * H ^ 3).1.coeff
    ((4 * D.faber.scale.p - 3 * T.delta) + 3 * T.delta) =
      (314928 * (r * A + B) * A ^ 2).1.coeff
        (4 * D.faber.scale.p - 3 * T.delta) at hc4s
  have hneg : 4 * D.faber.scale.p - 3 * T.delta < 0 := by linarith
  have hc3z : ((64 * A ^ 3) * H ^ 3).1.coeff (4 * D.faber.scale.p) = 0 := by
    rw [← show (4 * D.faber.scale.p - 3 * T.delta) + 3 * T.delta =
      4 * D.faber.scale.p by ring, hc3s]
    exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg _ hneg
  have hc4z : ((314928 * (r * A + B) * A ^ 2) * H ^ 3).1.coeff
      (4 * D.faber.scale.p) = 0 := by
    rw [← show (4 * D.faber.scale.p - 3 * T.delta) + 3 * T.delta =
      4 * D.faber.scale.p by ring, hc4s]
    exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg _ hneg
  have ha0 : GCD369CubeHahnRegular.constantCoeff D.faber.scale.regular0 =
      D.faber.scale.leading0 := rfl
  have ha1 : GCD369CubeHahnRegular.constantCoeff D.faber.scale.regular1 =
      D.faber.scale.leading1 := rfl
  have ha2 : GCD369CubeHahnRegular.constantCoeff D.faber.scale.regular2 =
      D.faber.scale.leading2 := rfl
  have ha3 : GCD369CubeHahnRegular.constantCoeff D.faber.scale.regular3 =
      D.faber.scale.leading3 := rfl
  have ha4 : GCD369CubeHahnRegular.constantCoeff D.faber.scale.regular4 =
      D.faber.scale.leading4 := rfl
  have hp1 : GCD369CubeHahnRegular.constantCoeff P1 = 241920 * r0 ^ 6 := by
    dsimp only [P1, r0]; simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    rw [ha0, ha2, ha3, ha4, D.ha0, D.ha2, D.ha3, D.ha4,
      hu, hv]; ring
  have hp2 : GCD369CubeHahnRegular.constantCoeff P2 = -622080 * r0 ^ 7 := by
    dsimp only [P2, r0]; simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
    rw [ha1, ha2, ha3, ha4, D.ha1, D.ha2, D.ha3, D.ha4,
      hu, hv]; ring
  have hp3 : GCD369CubeHahnRegular.constantCoeff P3 = 0 := by
    dsimp only [P3]; simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
    rw [ha1, ha2, ha3, ha4, D.ha1, D.ha2, D.ha3, D.ha4]; ring
  have hp4 : GCD369CubeHahnRegular.constantCoeff P4 = 7257600 * r0 ^ 9 := by
    dsimp only [P4, r0]; simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
    rw [ha1, ha2, ha3, ha4, D.ha1, D.ha2, D.ha3, D.ha4,
      hu, hv]; ring
  have hw1 := D.faber.scale.weightedRegular_four_constant_mul_coeff C5 P1
  have hw2 := D.faber.scale.weightedRegular_four_constant_mul_coeff C5 P2
  have hw3 := D.faber.scale.weightedRegular_four_constant_mul_coeff C5 P3
  have hw4 := D.faber.scale.weightedRegular_four_constant_mul_coeff C5 P4
  change (c5w * P1).1.coeff (4 * D.faber.scale.p) =
    C5 * GCD369CubeHahnRegular.constantCoeff P1 at hw1
  change (c5w * P2).1.coeff (4 * D.faber.scale.p) =
    C5 * GCD369CubeHahnRegular.constantCoeff P2 at hw2
  change (c5w * P3).1.coeff (4 * D.faber.scale.p) =
    C5 * GCD369CubeHahnRegular.constantCoeff P3 at hw3
  change (c5w * P4).1.coeff (4 * D.faber.scale.p) =
    C5 * GCD369CubeHahnRegular.constantCoeff P4 at hw4
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hz := (D.faber.c5NCoeff_zero C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
      hd hc7 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4).1
    rw [hc5] at hz
    have hf : GCD369CubeFaberC5N1 D.faber.scale.regular0
        D.faber.scale.regular1 D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 c5w = 729 * N1 + c5w * P1 := rfl
    rw [hf] at hz
    change (729 * N1).1.coeff (4 * D.faber.scale.p) +
      (c5w * P1).1.coeff (4 * D.faber.scale.p) = 0 at hz
    rw [hw1, hp1] at hz
    have hc := congrArg (fun z : GCD369CubeHahnRegular k =>
      z.1.coeff (4 * D.faber.scale.p)) hexp1
    rw [hlambda, hs1] at hc
    calc
      _ = (729 * N1).1.coeff (4 * D.faber.scale.p) +
          C5 * (241920 * r0 ^ 6) := by rw [← hc, hlambda]
      _ = 0 := hz
  · have hz := (D.faber.c5NCoeff_zero C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
      hd hc7 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4).2.1
    rw [hc5] at hz
    have hf : GCD369CubeFaberC5N2 D.faber.scale.regular0
        D.faber.scale.regular1 D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 c5w = 2187 * N2 + c5w * P2 := rfl
    rw [hf] at hz
    change (2187 * N2).1.coeff (4 * D.faber.scale.p) +
      (c5w * P2).1.coeff (4 * D.faber.scale.p) = 0 at hz
    rw [hw2, hp2] at hz
    have hc := congrArg (fun z : GCD369CubeHahnRegular k =>
      z.1.coeff (4 * D.faber.scale.p)) hexp2
    rw [hlambda, hs2] at hc
    calc
      _ = (2187 * N2).1.coeff (4 * D.faber.scale.p) +
          C5 * (-622080 * r0 ^ 7) := by rw [← hc, hlambda]
      _ = 0 := hz
  · have hz := (D.faber.c5NCoeff_zero C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
      hd hc7 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4).2.2.1
    rw [hc5] at hz
    have hf : GCD369CubeFaberC5N3 D.faber.scale.regular0
        D.faber.scale.regular1 D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 c5w = 243 * N3 + c5w * P3 := rfl
    rw [hf] at hz
    change (243 * N3).1.coeff (4 * D.faber.scale.p) +
      (c5w * P3).1.coeff (4 * D.faber.scale.p) = 0 at hz
    rw [hw3, hp3, mul_zero, add_zero] at hz
    have h243 := GCD369CubeHahnRegular.coeff_nat_mul 243 N3
      (4 * D.faber.scale.p)
    have hzN : N3.1.coeff (4 * D.faber.scale.p) = 0 :=
      (mul_eq_zero.mp (h243.symm.trans hz)).resolve_left (by norm_num)
    have hc := congrArg (fun z : GCD369CubeHahnRegular k =>
      z.1.coeff (4 * D.faber.scale.p)) hexp3
    change N3.1.coeff (4 * D.faber.scale.p) =
      ((128 * R3) * H ^ 2).1.coeff (4 * D.faber.scale.p) -
        ((64 * A ^ 3) * H ^ 3).1.coeff (4 * D.faber.scale.p) at hc
    rw [hc3z, sub_zero, hlambda, hs3] at hc
    rw [hlambda] at hzN
    exact hc.symm.trans hzN
  · have hz := (D.faber.c5NCoeff_zero C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
      hd hc7 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4).2.2.2
    rw [hc5] at hz
    have hf : GCD369CubeFaberC5N4 D.faber.scale.regular0
        D.faber.scale.regular1 D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 c5w = 6561 * N4 + c5w * P4 := rfl
    rw [hf] at hz
    change (6561 * N4).1.coeff (4 * D.faber.scale.p) +
      (c5w * P4).1.coeff (4 * D.faber.scale.p) = 0 at hz
    rw [hw4, hp4] at hz
    have hc := congrArg (fun z : GCD369CubeHahnRegular k =>
      z.1.coeff (4 * D.faber.scale.p)) hexp4
    change (6561 * N4).1.coeff (4 * D.faber.scale.p) =
      ((32 * R4) * H ^ 2).1.coeff (4 * D.faber.scale.p) -
        ((314928 * (r * A + B) * A ^ 2) * H ^ 3).1.coeff
          (4 * D.faber.scale.p) at hc
    rw [hc4z, sub_zero, hlambda, hs4] at hc
    calc
      _ = (6561 * N4).1.coeff (4 * D.faber.scale.p) +
          C5 * (7257600 * r0 ^ 9) := by rw [← hc, hlambda]
      _ = 0 := hz

/-- In the strict active-`c5` window, the coefficient equations and the
two-stage moving-root lift realize an inconsistent loaded quadratic system
when the weight-four parameter is nonzero. -/
theorem TransverseFactor.doubleRoot_c5Load_inconsistent_of_lt_coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 : k)
    (hC5 : C5 ≠ 0)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
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
    (hdeltaP : T.delta < 2 * D.faber.scale.p)
    (hpDelta : 4 * D.faber.scale.p < 3 * T.delta) : False := by
  have hd0 : D.faber.d = 0 := by simpa using hd
  have hc70 : D.faber.c7 = 0 := by simpa using hc7
  have huc : GCD369CubeHahnRegular.constantCoeff D.cubicU =
      -3 * r0 ^ 2 := by
    rw [D.constantCoeff_cubicU, hu]
  have hhalf := T.doubleRoot_deviations_order_c5Load_half_lower_coeff
    hd0 hc70 hdeltaP hpDelta r r0 A0 hr0 hA0 hr huc hX hY hZ hroot
  let mu : ℚ := 2 * D.faber.scale.p - T.delta
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
    2 * T.Xn ^ 2 * r * Dv - 3 * T.Xn * B * r ^ 2 -
      3 * T.Xn * C * r + 3 * T.Xn * B * Dv - 3 * B * C
  have hRow1 : (↑(2 * mu) : WithTop ℚ) ≤ Row1.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro e he
    have he' : e < 2 * mu := WithTop.coe_lt_coe.mp he
    by_cases he0 : 0 ≤ e
    · have hrows := T.doubleRoot_row123Coeffs_zero_before_c5_coeff hd0 hc70
        r hroot e he0 (by dsimp only [mu] at he'; linarith)
        (by dsimp only [mu] at he'; linarith)
      simpa only [Row1, Dv, B, C] using hrows.1
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg Row1
        (lt_of_not_ge he0)
  have hRow2 : (↑(2 * mu) : WithTop ℚ) ≤ Row2.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro e he
    have he' : e < 2 * mu := WithTop.coe_lt_coe.mp he
    by_cases he0 : 0 ≤ e
    · have hrows := T.doubleRoot_row123Coeffs_zero_before_c5_coeff hd0 hc70
        r hroot e he0 (by dsimp only [mu] at he'; linarith)
        (by dsimp only [mu] at he'; linarith)
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
  let dn : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift Dn mu hlift.1
  let qn : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift Qn mu hlift.2
  have hdnfact : M * dn = Dn := by
    simpa only [M, dn] using GCD369CubeHahnRegular.monomial_mul_shift
      Dn mu hmu.le hlift.1
  have hqnfact : M * qn = Qn := by
    simpa only [M, qn] using GCD369CubeHahnRegular.monomial_mul_shift
      Qn mu hmu.le hlift.2
  let Dq : GCD369CubeHahnRegular k := M ^ 2 * dn
  let Bq : GCD369CubeHahnRegular k := M * Bn
  let Cq : GCD369CubeHahnRegular k := M ^ 2 * qn - M * r * Bn
  have hDq : Dv = Dq := by
    calc
      Dv = M * Dn := hDfact.symm
      _ = M * (M * dn) := congrArg (fun z => M * z) hdnfact.symm
      _ = Dq := by dsimp only [Dq]; ring
  have hBq : B = Bq := by simpa only [Bq] using hBfact.symm
  have hCn : Cn = M * qn - r * Bn := by
    dsimp only [Qn] at hqnfact
    linear_combination -hqnfact
  have hCq : C = Cq := by
    calc
      C = M * Cn := hCfact.symm
      _ = M * (M * qn - r * Bn) := congrArg (fun z => M * z) hCn
      _ = Cq := by dsimp only [Cq]; ring
  let Row3 : GCD369CubeHahnRegular k :=
    -2 * T.Xn ^ 2 * r ^ 2 * Dv + 6 * B ^ 2 * r ^ 2 +
      2 * T.Xn ^ 2 * Dv ^ 2 - 2 * B ^ 2 * Dv -
        4 * T.Xn * C * Dv + 3 * C ^ 2
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
  have hload := T.doubleRoot_c5Load_coeff_of_lt
    C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
    r hroot hu' hv' hdeltaP hpDelta
  dsimp only at hload
  have hlambda : 4 * D.faber.scale.p - 2 * T.delta = 2 * mu := by
    dsimp only [mu]
    ring
  rw [hlambda, hr] at hload
  have hload1 : (-32 * (729 * Row1)).1.coeff (2 * mu) +
      C5 * (241920 * r0 ^ 6) = 0 := by
    simpa only [Row1, Dv, B, C] using hload.1
  have hload2 : (32 * (-1458 * Row2)).1.coeff (2 * mu) +
      C5 * (-622080 * r0 ^ 7) = 0 := by
    simpa only [Row2, Dv, B, C] using hload.2.1
  have hload3 : (128 * Row3).1.coeff (2 * mu) = 0 := by
    simpa only [Row3, Dv, B, C] using hload.2.2.1
  have hload4 : (32 * Row4).1.coeff (2 * mu) +
      C5 * (7257600 * r0 ^ 9) = 0 := by
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
      C5 * (241920 * r0 ^ 6) = 0 := by
    simpa only [QR1] using hload1
  have hload2q : (32 * (-1458 * QR2)).1.coeff (2 * mu) +
      C5 * (-622080 * r0 ^ 7) = 0 := by
    simpa only [QR2] using hload2
  have hload3q : (128 * QR3).1.coeff (2 * mu) = 0 := by
    simpa only [QR3] using hload3
  have hload4q : (32 * QR4).1.coeff (2 * mu) +
      C5 * (7257600 * r0 ^ 9) = 0 := by
    simpa only [QR4] using hload4
  have hquad := GCD369CubeHahnRegular.doubleBlowup_quadratic_coefficients
    mu hmu T.Xn r dn Bn qn
  have hq1 : QR1.1.coeff (2 * mu) =
      A0 ^ 2 * GCD369CubeHahnRegular.constantCoeff dn -
        2 * A0 * GCD369CubeHahnRegular.constantCoeff qn -
          GCD369CubeHahnRegular.constantCoeff Bn ^ 2 := by
    simpa only [QR1, Dq, Bq, Cq, M, hX, hr] using hquad.1
  have hq2 : QR2.1.coeff (2 * mu) =
      2 * A0 ^ 2 * r0 * GCD369CubeHahnRegular.constantCoeff dn -
        3 * A0 * r0 * GCD369CubeHahnRegular.constantCoeff qn +
          3 * r0 * GCD369CubeHahnRegular.constantCoeff Bn ^ 2 := by
    simpa only [QR2, Dq, Bq, Cq, M, hX, hr] using hquad.2.1
  have hq3 : QR3.1.coeff (2 * mu) =
      -2 * A0 ^ 2 * r0 ^ 2 * GCD369CubeHahnRegular.constantCoeff dn +
        9 * r0 ^ 2 * GCD369CubeHahnRegular.constantCoeff Bn ^ 2 := by
    simpa only [QR3, Dq, Bq, Cq, M, hX, hr] using hquad.2.2
  have hq4 : QR4.1.coeff (2 * mu) =
      -13122 * A0 * r0 ^ 3 * GCD369CubeHahnRegular.constantCoeff qn -
        65610 * r0 ^ 3 * GCD369CubeHahnRegular.constantCoeff Bn ^ 2 := by
    simpa only [QR4, Dq, Bq, Cq, M, hX, hr] using
      (GCD369CubeHahnRegular.doubleBlowup_quadratic_row4_coefficient
        mu hmu T.Xn r dn Bn qn)
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
  apply GCD369CubeDoubleBlowup_c5Load_quadratic_beforeCubic_inconsistent
    A0 (GCD369CubeHahnRegular.constantCoeff Bn)
      (GCD369CubeHahnRegular.constantCoeff qn) r0
      (GCD369CubeHahnRegular.constantCoeff dn) C5 hr0 hC5
  · linear_combination hload1q
  · linear_combination hload2q
  · exact (mul_eq_zero.mp hload3q).resolve_left (by norm_num)
  · linear_combination hload4q

/-- Below the weight-four load, with the two earlier parameters zero, the
first transverse residue satisfies the four universal normal rows. -/
theorem TransverseScale.zeroLoadLeadingRows_before_c5_coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (hd : D.faber.d = 0) (hc7 : D.faber.c7 = 0)
    (hearly : 2 * T.delta < 4 * D.faber.scale.p) :
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
  have hz := D.faber.zeroHighNCoeff_zero_before_c5 hd hc7
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

/-- The first transverse residue supplies a nonzero double-root chart, so
the strict active-`c5` middle window is inconsistent at the coefficient
packet level. -/
theorem TransverseScale.c5_singular_middle_inconsistent_coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 : k)
    (hC5 : C5 ≠ 0)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hrho1 : D.faber.rho1 = GCD369CubeHahnRegular.constant Rho1)
    (hrho2 : D.faber.rho2 = GCD369CubeHahnRegular.constant Rho2)
    (hrho3 : D.faber.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : D.faber.rho4 = GCD369CubeHahnRegular.constant Rho4)
    (hdeltaP : T.delta < 2 * D.faber.scale.p)
    (hpDelta : 4 * D.faber.scale.p < 3 * T.delta) : False := by
  have hd0 : D.faber.d = 0 := by simpa using hd
  have hc70 : D.faber.c7 = 0 := by simpa using hc7
  have hearly : 2 * T.delta < 4 * D.faber.scale.p := by linarith
  obtain ⟨h1, h2, h3, h4⟩ :=
    T.zeroLoadLeadingRows_before_c5_coeff hd0 hc70 hearly
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
  exact T.factor.doubleRoot_c5Load_inconsistent_of_lt_coeff
    C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 hC5
    hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
    r r0 (GCD369CubeHahnRegular.constantCoeff T.Xn) hr0 hX hr hu hv
    (by rfl) hY hZ hroot
    (by simpa only [TransverseScale.factor] using hdeltaP)
    (by simpa only [TransverseScale.factor] using hpDelta)

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubePolynomialSource

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- After `d = c7 = 0`, a nonzero `c5` coefficient is impossible in the
strict singular middle window `2 delta < 4p < 3 delta`. -/
theorem infinity_c5_eq_zero_singular_middle
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hd0 : S.faberConstantParameters.d = 0)
    (hc70 : S.faberConstantParameters.c7 = 0)
    (hmiddle : 2 * T.delta <
      4 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p)
    (hpDelta :
      4 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p <
        3 * T.delta) :
    S.faberConstantParameters.c5 = 0 := by
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
  have hc5D : D.faber.c5 = GCD369CubeHahnRegular.constant P.c5 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc5
  have hc4D : D.faber.c4 = GCD369CubeHahnRegular.constant P.c4 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc4
  have hc3D : D.faber.c3 = GCD369CubeHahnRegular.constant P.c3 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc3
  have hc2D : D.faber.c2 = GCD369CubeHahnRegular.constant P.c2 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc2
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
  have hdeltaP : T.delta < 2 * D.faber.scale.p := by
    dsimp only [D]
    linarith
  by_contra hPc5
  exact T.c5_singular_middle_inconsistent_coeff
    P.c5 P.c4 P.c3 P.c2 P.c1 R.rho1 R.rho2 R.rho3 R.rho4 hPc5
    hdD hc7D hc5D hc4D hc3D hc2D hc1D hr1D hr2D hr3D hr4D
    hdeltaP (by simpa only [D] using hpDelta)

end GCD369CubePolynomialSource

#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseFactor.doubleRoot_row123Coeffs_zero_before_c5_coeff
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseFactor.doubleRoot_firstCommonScale_not_below_c5Load_half_coeff
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseFactor.doubleRoot_deviations_order_c5Load_half_lower_coeff
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseFactor.doubleRoot_c5Load_coeff_of_lt
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseFactor.doubleRoot_c5Load_inconsistent_of_lt_coeff
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.zeroLoadLeadingRows_before_c5_coeff
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.c5_singular_middle_inconsistent_coeff
#print axioms GCD369CubePolynomialSource.infinity_c5_eq_zero_singular_middle
