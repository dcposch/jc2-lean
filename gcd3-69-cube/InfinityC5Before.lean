import InfinityC7Before
import InfinityLoadLanding
import FiniteC5Extraction

/-! # The strict-before weight-four load at infinity

At the prescribed scale `2p`, a weight-four `c5` load is quadratic in
the Hahn monomial.  If `4p < 2δ`, this scale lies strictly below the first
transverse normal order, so all three normal residues vanish and the finite
`c5` no-common-root certificate forces the load to be zero.
-/

noncomputable section
open Polynomial

noncomputable section
open Polynomial

namespace GCD369CubeHahnCommonCoefficientData

theorem TransverseFactor.c5BeforeN1Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C5 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC5N1
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C5)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -96 * (40 * C5 * D.u ^ 3 - 360 * C5 * D.v ^ 2 +
        243 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
          486 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
            (GCD369CubeHahnRegular.constantCoeff T.Zn) -
          243 * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    51840 * D.faber.scale.regular0 -
      8640 * D.faber.scale.regular2 *
        D.faber.scale.regular4 -
      4320 * D.faber.scale.regular3 ^ 2 +
      1680 * D.faber.scale.regular4 ^ 3
  change
    (729 * GCD369CubeFaberN1
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C5 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN1Coeff]
  have hload :
      ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
        GCD369CubeHahnRegular.constant C5 * P).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) =
        C5 * GCD369CubeHahnRegular.constantCoeff P := by
    exact GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C5 P
  rw [hload]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change _ + C5 *
    (51840 * D.faber.scale.leading0 -
      8640 * D.faber.scale.leading2 *
          D.faber.scale.leading4 -
      4320 * D.faber.scale.leading3 ^ 2 +
      1680 * D.faber.scale.leading4 ^ 3) = _
  rw [D.ha0, D.ha2, D.ha3, D.ha4]
  dsimp only [GCD369CubeNormalRow1]
  ring

theorem TransverseFactor.c5BeforeN2Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C5 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC5N2
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C5)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -864 * (40 * C5 * D.u ^ 2 * D.v +
        81 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
          162 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
            (GCD369CubeHahnRegular.constantCoeff T.Yn) -
          162 * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
            (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    -25920 * D.faber.scale.regular1 *
        D.faber.scale.regular4 -
      25920 * D.faber.scale.regular2 *
        D.faber.scale.regular3 +
      15120 * D.faber.scale.regular3 *
        D.faber.scale.regular4 ^ 2
  change
    (2187 * GCD369CubeFaberN2
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C5 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN2Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C5 P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
  change _ + C5 *
    (-25920 * D.faber.scale.leading1 *
          D.faber.scale.leading4 -
      25920 * D.faber.scale.leading2 *
          D.faber.scale.leading3 +
      15120 * D.faber.scale.leading3 *
          D.faber.scale.leading4 ^ 2) = _
  rw [D.ha1, D.ha2, D.ha3, D.ha4]
  dsimp only [GCD369CubeNormalRow2]
  ring

theorem TransverseFactor.c5BeforeN3Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C5 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC5N3
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C5)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      31104 * GCD369CubeNormalRow3
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    -34560 * D.faber.scale.regular1 *
        D.faber.scale.regular3 -
      17280 * D.faber.scale.regular2 ^ 2 +
      14400 * D.faber.scale.regular2 *
        D.faber.scale.regular4 ^ 2 +
      17280 * D.faber.scale.regular3 ^ 2 *
        D.faber.scale.regular4 -
      2520 * D.faber.scale.regular4 ^ 4
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
      GCD369CubeHahnRegular.constant C5 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [hzero,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C5 P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
  change _ + C5 *
    (-34560 * D.faber.scale.leading1 *
          D.faber.scale.leading3 -
      17280 * D.faber.scale.leading2 ^ 2 +
      14400 * D.faber.scale.leading2 *
          D.faber.scale.leading4 ^ 2 +
      17280 * D.faber.scale.leading3 ^ 2 *
          D.faber.scale.leading4 -
      2520 * D.faber.scale.leading4 ^ 4) = _
  rw [D.ha1, D.ha2, D.ha3, D.ha4]
  ring

theorem TransverseFactor.c5BeforeN4Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C5 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC5N4
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C5)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -2592 * (40 * C5 * D.u ^ 3 * D.v - 80 * C5 * D.v ^ 3 -
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
    -233280 * D.faber.scale.regular1 *
        D.faber.scale.regular2 +
      58320 * D.faber.scale.regular1 *
        D.faber.scale.regular4 ^ 2 +
      155520 * D.faber.scale.regular2 *
        D.faber.scale.regular3 * D.faber.scale.regular4 +
      25920 * D.faber.scale.regular3 ^ 3 -
      45360 * D.faber.scale.regular3 *
        D.faber.scale.regular4 ^ 3
  change
    (6561 * GCD369CubeFaberN4
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C5 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN4Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C5 P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
  change _ + C5 *
    (-233280 * D.faber.scale.leading1 *
          D.faber.scale.leading2 +
      58320 * D.faber.scale.leading1 *
          D.faber.scale.leading4 ^ 2 +
      155520 * D.faber.scale.leading2 *
          D.faber.scale.leading3 *
            D.faber.scale.leading4 +
      25920 * D.faber.scale.leading3 ^ 3 -
      45360 * D.faber.scale.leading3 *
          D.faber.scale.leading4 ^ 3) = _
  rw [D.ha1, D.ha2, D.ha3, D.ha4]
  dsimp only [GCD369CubeNormalRow4]
  ring

/-- Vanishing of the four literal quadratic Hahn coefficients is exactly
the source-facing arbitrary-`c5` Faber row packet. -/
theorem TransverseFactor.c5BeforeLeadingFaberRowsAt
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C5 : k)
    (h1 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC5N1
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C5)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h2 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC5N2
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C5)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h3 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC5N3
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C5)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h4 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC5N4
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C5)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0) :
    GCD369CubeC5LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C5 := by
  dsimp [GCD369CubeC5LeadingFaberRowsAt]
  have hc := GCD369CubeFaberC5NormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C5
  dsimp only at hc
  rcases hc with ⟨hc1, hc2, hc3, hc4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc1, ← T.c5BeforeN1Coeff C5]
    exact h1
  · rw [hc2, ← T.c5BeforeN2Coeff C5]
    exact h2
  · rw [hc3, ← T.c5BeforeN3Coeff C5]
    exact h3
  · rw [hc4, ← T.c5BeforeN4Coeff C5]
    exact h4


end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubeHahnCommonCoefficientData

set_option maxHeartbeats 4000000 in
/-- Literal source parameters produce the pure `c5` row packet after
factoring the normal coordinates at the prescribed scale `2p`. -/
theorem c5BeforeLeadingFaberRowsAt_of_bounds
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k)
    (C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (hscale : 0 < ((4 : ℚ) * D.faber.scale.p) / 2)
    (hnormal2 :
      (↑(((4 : ℚ) * D.faber.scale.p) / 2) : WithTop ℚ) ≤
        D.normal2.1.orderTop)
    (hnormal1 :
      (↑(((4 : ℚ) * D.faber.scale.p) / 2) : WithTop ℚ) ≤
        D.normal1.1.orderTop)
    (hnormal0 :
      (↑(((4 : ℚ) * D.faber.scale.p) / 2) : WithTop ℚ) ≤
        D.normal0.1.orderTop) :
    let U := D.transverseFactorOfBounds
      (((4 : ℚ) * D.faber.scale.p) / 2)
      hscale hnormal2 hnormal1 hnormal0
    GCD369CubeC5LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff U.Xn)
      (GCD369CubeHahnRegular.constantCoeff U.Yn)
      (GCD369CubeHahnRegular.constantCoeff U.Zn) D.u D.v C5 := by
  dsimp only
  let U := D.transverseFactorOfBounds
    (((4 : ℚ) * D.faber.scale.p) / 2)
    hscale hnormal2 hnormal1 hnormal0
  have hz := D.faber.c5NCoeff_zero C4 C3 C2 C1 R1 R2 R3 R4
    hd hc7 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4
  rw [hc5,
    D.faber.scale.weightedRegular_constant_eq_monomial_sq
      4 (by norm_num) C5] at hz
  rcases hz with ⟨hz1, hz2, hz3, hz4⟩
  apply U.c5BeforeLeadingFaberRowsAt C5
  · have hUdelta :
        U.delta = (((4 : ℚ) * D.faber.scale.p) / 2) := rfl
    simp only [hUdelta]
    convert hz1 using 1
    congr 1
    ring
  · have hUdelta :
        U.delta = (((4 : ℚ) * D.faber.scale.p) / 2) := rfl
    simp only [hUdelta]
    convert hz2 using 1
    congr 1
    ring
  · have hUdelta :
        U.delta = (((4 : ℚ) * D.faber.scale.p) / 2) := rfl
    simp only [hUdelta]
    convert hz3 using 1
    congr 1
    ring
  · have hUdelta :
        U.delta = (((4 : ℚ) * D.faber.scale.p) / 2) := rfl
    simp only [hUdelta]
    convert hz4 using 1
    congr 1
    ring

set_option maxHeartbeats 4000000 in
/-- A nonzero constant `c5` load cannot arrive strictly before the first
transverse normal scale.  The hypothesis is equivalent to `2p < δ`. -/
theorem TransverseScale.c5_eq_zero_strict_before
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (hbefore : 4 * D.faber.scale.p < 2 * T.delta) :
    C5 = 0 := by
  let e : ℚ := ((4 : ℚ) * D.faber.scale.p) / 2
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
  have hrows : GCD369CubeC5LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff U.Xn)
      (GCD369CubeHahnRegular.constantCoeff U.Yn)
      (GCD369CubeHahnRegular.constantCoeff U.Zn) D.u D.v C5 := by
    simpa only [U, e] using D.c5BeforeLeadingFaberRowsAt_of_bounds
      C5 C4 C3 C2 C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4
      he hb2 hb1 hb0
  by_contra hC5
  have hnocommon := GCD369CubeC5LeadingFaberRowsAt_noCommonRoot
    (GCD369CubeHahnRegular.constantCoeff U.Xn)
    (GCD369CubeHahnRegular.constantCoeff U.Yn)
    (GCD369CubeHahnRegular.constantCoeff U.Zn)
    D.u D.v C5 hC5 D.hprojective hrows
  obtain ⟨r, hr⟩ := GCD369CubeExistsDepressedCubicRoot D.u D.v
  exact hnocommon r hr (by rw [hX, hY, hZ]; ring)

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubePolynomialSource

/-- Source-facing strict `c5` routing for the constant-core infinity packet,
after the weight-one and weight-two source coefficients have vanished. -/
theorem infinity_c5_eq_zero_strict_before
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hd0 : S.faberConstantParameters.d = 0)
    (hc70 : S.faberConstantParameters.c7 = 0)
    (hbefore :
      4 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p <
        2 * T.delta) :
    S.faberConstantParameters.c5 = 0 := by
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  obtain ⟨hd, hc7, hc5, hc4, hc3, hc2, hc1,
      hr1, hr2, hr3, hr4⟩ :=
    S.infinityFaberPoleData_constant_loads hpole
  apply T.c5_eq_zero_strict_before
    P.c5 P.c4 P.c3 P.c2 P.c1
      R.rho1 R.rho2 R.rho3 R.rho4
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    simpa only [P, hd0] using hd
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    simpa only [P, hc70] using hc7
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hc5
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hc4
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hc3
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

end GCD369CubePolynomialSource

#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseFactor.c5BeforeLeadingFaberRowsAt
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.c5_eq_zero_strict_before
#print axioms GCD369CubePolynomialSource.infinity_c5_eq_zero_strict_before
