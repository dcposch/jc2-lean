import InfinityC7Before
import InfinityLoadLanding
import FiniteC2Extraction
import TargetNormalization
import FiniteTargetNormalizedParameters

/-! # The strict-before weight-seven load at infinity

At the prescribed scale `7p/2`, a weight-seven `c2` load is quadratic in
the Hahn monomial.  Strict arrival before the first transverse normal forces
the normal residues to vanish, and the arbitrary-`c2` common-root
certificate then kills the load.
-/

noncomputable section
open Polynomial

namespace GCD369CubeHahnCommonCoefficientData

theorem TransverseFactor.c2BeforeN1Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C2 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC2N1
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C2)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -2592 * (-16 * C2 * D.v +
        9 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
        18 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) -
        9 * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    20736 * D.faber.scale.regular3
  change
    (729 * GCD369CubeFaberN1
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C2 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN1Coeff]
  have hload :
      ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
        GCD369CubeHahnRegular.constant C2 * P).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) =
        C2 * GCD369CubeHahnRegular.constantCoeff P := by
    exact GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C2 P
  rw [hload]
  dsimp only [P]
  simp only [map_mul, map_ofNat]
  change _ + C2 * (20736 * D.faber.scale.leading3) = _
  rw [D.ha3]
  dsimp only [GCD369CubeNormalRow1]
  ring

theorem TransverseFactor.c2BeforeN2Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C2 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC2N2
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C2)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -2592 * (8 * C2 * D.u ^ 2 +
        27 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
        54 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) -
        54 * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    62208 * D.faber.scale.regular2 -
      20736 * D.faber.scale.regular4 ^ 2
  change
    (2187 * GCD369CubeFaberN2
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C2 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN2Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C2 P]
  dsimp only [P]
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  change _ + C2 *
    (62208 * D.faber.scale.leading2 -
      20736 * D.faber.scale.leading4 ^ 2) = _
  rw [D.ha2, D.ha4]
  dsimp only [GCD369CubeNormalRow2]
  ring

theorem TransverseFactor.c2BeforeN3Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C2 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC2N3
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C2)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      31104 * GCD369CubeNormalRow3
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    82944 * D.faber.scale.regular1 -
      41472 * D.faber.scale.regular3 *
        D.faber.scale.regular4
  have hzero :
      (243 * GCD369CubeFaberN3
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) =
        31104 * GCD369CubeNormalRow3
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v := by
    calc
      _ = (243 : k) *
          (GCD369CubeFaberN3
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4).1.coeff
              (((2 : ℕ) : ℚ) * T.delta) :=
        GCD369CubeHahnRegular.coeff_nat_mul 243 _ _
      _ = _ := by rw [T.zeroHighN3Coeff]; ring
  change
    (243 * GCD369CubeFaberN3
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C2 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [hzero,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C2 P]
  dsimp only [P]
  simp only [map_sub, map_mul, map_ofNat]
  change _ + C2 *
    (82944 * D.faber.scale.leading1 -
      41472 * D.faber.scale.leading3 *
        D.faber.scale.leading4) = _
  rw [D.ha1, D.ha3, D.ha4]
  ring

theorem TransverseFactor.c2BeforeN4Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C2 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC2N4
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C2)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -2592 * (16 * C2 * D.u ^ 3 - 72 * C2 * D.v ^ 2 -
        243 * D.u * D.v *
          (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
        162 * D.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) +
        324 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) +
        162 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 +
        162 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    559872 * D.faber.scale.regular0 -
      186624 * D.faber.scale.regular2 *
        D.faber.scale.regular4 -
      93312 * D.faber.scale.regular3 ^ 2 +
      41472 * D.faber.scale.regular4 ^ 3
  change
    (6561 * GCD369CubeFaberN4
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C2 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN4Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C2 P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change _ + C2 *
    (559872 * D.faber.scale.leading0 -
      186624 * D.faber.scale.leading2 *
        D.faber.scale.leading4 -
      93312 * D.faber.scale.leading3 ^ 2 +
      41472 * D.faber.scale.leading4 ^ 3) = _
  rw [D.ha0, D.ha2, D.ha3, D.ha4]
  dsimp only [GCD369CubeNormalRow4]
  ring

/-- Vanishing of the four literal quadratic Hahn coefficients is exactly
the source-facing arbitrary-`c2` Faber row packet. -/
theorem TransverseFactor.c2BeforeLeadingFaberRowsAt
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C2 : k)
    (h1 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC2N1
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C2)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h2 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC2N2
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C2)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h3 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC2N3
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C2)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h4 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC2N4
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C2)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0) :
    GCD369CubeC2LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C2 := by
  dsimp [GCD369CubeC2LeadingFaberRowsAt]
  have hc := GCD369CubeFaberC2NormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C2
  dsimp only at hc
  rcases hc with ⟨hc1, hc2, hc3, hc4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc1, ← T.c2BeforeN1Coeff C2]
    exact h1
  · rw [hc2, ← T.c2BeforeN2Coeff C2]
    exact h2
  · rw [hc3, ← T.c2BeforeN3Coeff C2]
    exact h3
  · rw [hc4, ← T.c2BeforeN4Coeff C2]
    exact h4
theorem c2BeforeLeadingFaberRowsAt_of_bounds
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k)
    (C2 C1 R1 R2 R3 R4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (hnormal2 : (↑((7 * D.faber.scale.p) / 2) : WithTop ℚ) ≤
      D.normal2.1.orderTop)
    (hnormal1 : (↑((7 * D.faber.scale.p) / 2) : WithTop ℚ) ≤
      D.normal1.1.orderTop)
    (hnormal0 : (↑((7 * D.faber.scale.p) / 2) : WithTop ℚ) ≤
      D.normal0.1.orderTop) :
    let T := D.transverseFactorOfBounds ((7 * D.faber.scale.p) / 2)
      (div_pos (mul_pos (by norm_num) D.faber.scale.hp) (by norm_num))
      hnormal2 hnormal1 hnormal0
    GCD369CubeC2LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C2 := by
  dsimp only
  let T := D.transverseFactorOfBounds ((7 * D.faber.scale.p) / 2)
    (div_pos (mul_pos (by norm_num) D.faber.scale.hp) (by norm_num))
    hnormal2 hnormal1 hnormal0
  apply T.c2BeforeLeadingFaberRowsAt C2
  · have hz := (D.faber.c2NCoeff_zero C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc1 hr1 hr2 hr3 hr4).1
    rw [hc2,
      D.faber.scale.weightedRegular_constant_eq_monomial_sq 7 (by norm_num) C2] at hz
    have hTdelta : T.delta = (7 * D.faber.scale.p) / 2 := rfl
    simp only [hTdelta]
    convert hz using 1
    all_goals norm_num
    all_goals ring_nf
  · have hz := (D.faber.c2NCoeff_zero C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc1 hr1 hr2 hr3 hr4).2.1
    rw [hc2,
      D.faber.scale.weightedRegular_constant_eq_monomial_sq 7 (by norm_num) C2] at hz
    have hTdelta : T.delta = (7 * D.faber.scale.p) / 2 := rfl
    simp only [hTdelta]
    convert hz using 1
    all_goals norm_num
    all_goals ring_nf
  · have hz := (D.faber.c2NCoeff_zero C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc1 hr1 hr2 hr3 hr4).2.2.1
    rw [hc2,
      D.faber.scale.weightedRegular_constant_eq_monomial_sq 7 (by norm_num) C2] at hz
    have hTdelta : T.delta = (7 * D.faber.scale.p) / 2 := rfl
    simp only [hTdelta]
    convert hz using 1
    all_goals norm_num
    all_goals ring_nf
  · have hz := (D.faber.c2NCoeff_zero C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc1 hr1 hr2 hr3 hr4).2.2.2
    rw [hc2,
      D.faber.scale.weightedRegular_constant_eq_monomial_sq 7 (by norm_num) C2] at hz
    have hTdelta : T.delta = (7 * D.faber.scale.p) / 2 := rfl
    simp only [hTdelta]
    convert hz using 1
    all_goals norm_num
    all_goals ring_nf
set_option maxHeartbeats 4000000 in
theorem TransverseScale.c2_eq_zero_strict_before
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C2 C1 R1 R2 R3 R4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (hbefore : 7 * D.faber.scale.p < 2 * T.delta) :
    C2 = 0 := by
  let e : ℚ := ((7 : ℚ) * D.faber.scale.p) / 2
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
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact (WithTop.coe_lt_coe.mpr hedelt).trans_le hn2
  have hY : GCD369CubeHahnRegular.constantCoeff U.Yn = 0 := by
    dsimp only [U, transverseFactorOfBounds]
    rw [constantCoeff_shift]
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact (WithTop.coe_lt_coe.mpr hedelt).trans_le hn1
  have hZ : GCD369CubeHahnRegular.constantCoeff U.Zn = 0 := by
    dsimp only [U, transverseFactorOfBounds]
    rw [constantCoeff_shift]
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact (WithTop.coe_lt_coe.mpr hedelt).trans_le hn0
  have hrows : GCD369CubeC2LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff U.Xn)
      (GCD369CubeHahnRegular.constantCoeff U.Yn)
      (GCD369CubeHahnRegular.constantCoeff U.Zn) D.u D.v C2 := by
    simpa only [U, e] using D.c2BeforeLeadingFaberRowsAt_of_bounds
      C2 C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4
      hb2 hb1 hb0
  by_contra hC2
  have hnocommon := GCD369CubeC2LeadingFaberRowsAt_noCommonRoot
    (GCD369CubeHahnRegular.constantCoeff U.Xn)
    (GCD369CubeHahnRegular.constantCoeff U.Yn)
    (GCD369CubeHahnRegular.constantCoeff U.Zn)
    D.u D.v C2 hC2 D.hprojective hrows
  obtain ⟨r, hr⟩ := GCD369CubeExistsDepressedCubicRoot D.u D.v
  exact hnocommon r hr (by rw [hX, hY, hZ]; ring)

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubePolynomialSource

/-- Generic source-facing strict `c2` routing in the explicit `c3 = 0`
gauge, after all earlier genuine loads have vanished. -/
theorem infinity_c2_eq_zero_strict_before
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hd0 : S.faberConstantParameters.d = 0)
    (hc70 : S.faberConstantParameters.c7 = 0)
    (hc50 : S.faberConstantParameters.c5 = 0)
    (hc40 : S.faberConstantParameters.c4 = 0)
    (hc30 : S.faberConstantParameters.c3 = 0)
    (hbefore :
      7 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p <
        2 * T.delta) :
    S.faberConstantParameters.c2 = 0 := by
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  obtain ⟨hd, hc7, hc5, hc4, hc3, hc2, hc1,
      hr1, hr2, hr3, hr4⟩ :=
    S.infinityFaberPoleData_constant_loads hpole
  apply T.c2_eq_zero_strict_before
    P.c2 P.c1 R.rho1 R.rho2 R.rho3 R.rho4
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
    exact hc2
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hc1
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hr1
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hr2
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hr3
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hr4
  · exact hbefore

/-- Clean target-normalized wrapper: `c3 = 0` is supplied canonically, so
the only explicit vanishing hypotheses are the genuine earlier loads. -/
theorem targetNormalized_infinity_c2_eq_zero_strict_before
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
    (hbefore : let U := S.targetNormalizedSource
      let hsdegreeU : U.s.natDegree = 0 := by
        simpa [U, targetNormalizedSource] using hsdegree
      7 * (U.infinityCommonCoefficientData hsdegreeU).faber.scale.p <
        2 * T.delta) :
    S.targetNormalizedSource.faberConstantParameters.c2 = 0 := by
  let U := S.targetNormalizedSource
  have hsdegreeU : U.s.natDegree = 0 := by
    simpa [U, targetNormalizedSource] using hsdegree
  let P := S.faberConstantParameters
  let Q := U.faberConstantParameters
  obtain ⟨hQd, _hQc7, _hQc6, _hQc5, _hQc4, hQc3, _hQc2,
      _hQc1, _hQc0⟩ := S.targetNormalizedCanonicalParameters hd0
  apply U.infinity_c2_eq_zero_strict_before hsdegreeU T
  · simpa only [Q, U] using hQd
  · simpa only [Q, U] using hc70
  · simpa only [Q, U] using hc50
  · simpa only [Q, U] using hc40
  · simpa only [Q, U] using hQc3
  · simpa only [U, hsdegreeU] using hbefore

end GCD369CubePolynomialSource

#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseFactor.c2BeforeLeadingFaberRowsAt
#print axioms
  GCD369CubeHahnCommonCoefficientData.c2BeforeLeadingFaberRowsAt_of_bounds
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.c2_eq_zero_strict_before
#print axioms GCD369CubePolynomialSource.infinity_c2_eq_zero_strict_before
#print axioms
  GCD369CubePolynomialSource.targetNormalized_infinity_c2_eq_zero_strict_before
