import InfinityC5Tie
import InfinityC5Middle
import InfinityC7Balanced
import InfinityC7Late
import FiniteDoubleC5LoadSourceCoeff

/-! # The balanced and late singular c5 cells at infinity

After `d = c7 = 0`, this file closes the terminal algebra at
`4 p = 3 delta` and ports the intrinsic-cubic order argument to the late
cell `3 delta < 4 p`.
-/

noncomputable section

/-- The fifth terminal row eliminates the survivor of the four balanced
`c5` rows. -/
theorem GCD369Cube_c5Load_balanced_terminal_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A r d b q T : K) (hA : A ≠ 0) (hr : r ≠ 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * q - b ^ 2)) +
        241920 * r ^ 6 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * r * q +
        3 * r * b ^ 2)) - 622080 * r ^ 7 * T = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * q - 65610 * r ^ 3 * b ^ 2) -
        314928 * r * A ^ 3 + 7257600 * r ^ 9 * T = 0)
    (h5 :
      559872 * r ^ 4 * (-A ^ 2 * d + 21 * b ^ 2 + 6 * A * q) -
        2519424 * r ^ 2 * A ^ 3 - 73156608 * r ^ 10 * T = 0) :
    False := by
  have hzero : A ^ 3 * r ^ 2 = 0 := by
    linear_combination
      (-5 / 23934528 : K) *
        ((216 / 5 : K) * r ^ 4 * h1 -
          (84 / 5 : K) * r ^ 3 * h2 +
          (36 / 5 : K) * r * h4 + h5)
  exact (mul_ne_zero (pow_ne_zero 3 hA) (pow_ne_zero 2 hr)) hzero

namespace GCD369CubeHahnCommonCoefficientData

/-- The pure `c5` terminal polynomial restricted to the common cubic
sheet. -/
theorem terminalC5Coeff_cubicSheet
    {R : Type*} [CommRing R]
    (u v : R) :
    terminalC5Coeff (v ^ 2) (2 * u * v) (u ^ 2) (2 * v) (2 * u) =
      55296 * (u ^ 5 - 30 * u ^ 2 * v ^ 2) := by
  simp only [terminalC5Coeff]
  ring

/-- On the singular double-root sheet, the pure weight-four terminal
residue is `-73156608 r^10`. -/
theorem terminalC5Coeff_doubleRoot
    {R : Type*} [CommRing R]
    (r : R) :
    terminalC5Coeff
        ((2 * r ^ 3) ^ 2)
        (2 * (-3 * r ^ 2) * (2 * r ^ 3))
        ((-3 * r ^ 2) ^ 2) (2 * (2 * r ^ 3)) (2 * (-3 * r ^ 2)) =
      -73156608 * r ^ 10 := by
  rw [terminalC5Coeff_cubicSheet]
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- At `4 p = 3 delta`, the pure `c5` specialization contributes the
quadratic fifth row, intrinsic cubic, and singular c5 residue at one Hahn
coefficient. -/
theorem TransverseScale.c5SpecializedTerminalCoeff_at_balanced
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C5 : k)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (r A d b q : k)
    (hu : D.u = -3 * r ^ 2) (hv : D.v = 2 * r ^ 3)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r * A)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r ^ 2 * A)
    (htie : 4 * D.faber.scale.p = 3 * T.delta)
    (hord1 : (↑T.delta : WithTop ℚ) ≤
      (GCD369CubeNormalRow1 T.Xn T.Yn T.Zn D.cubicU).1.orderTop)
    (hord2 : (↑T.delta : WithTop ℚ) ≤
      (GCD369CubeNormalRow2 T.Xn T.Yn T.Zn
        D.cubicU D.cubicV).1.orderTop)
    (hcoeff1 :
      (GCD369CubeNormalRow1 T.Xn T.Yn T.Zn D.cubicU).1.coeff T.delta =
        729 * (A ^ 2 * d - 2 * A * q - b ^ 2))
    (hcoeff2 :
      (GCD369CubeNormalRow2 T.Xn T.Yn T.Zn
        D.cubicU D.cubicV).1.coeff T.delta =
        -1458 * (2 * A ^ 2 * r * d - 3 * A * r * q +
          3 * r * b ^ 2)) :
    (GCD369CubeFaberFullN5
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4 0 0
      (D.faber.scale.weightedRegular 4 D.faber.c5)
      0 0 0 0).1.coeff (4 * D.faber.scale.p) =
      559872 * r ^ 4 * (-A ^ 2 * d + 21 * b ^ 2 + 6 * A * q) -
        2519424 * r ^ 2 * A ^ 3 - 73156608 * r ^ 10 * C5 := by
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let R5 : GCD369CubeHahnRegular k :=
    GCD369CubeNormalRow5 T.Xn T.Yn T.Zn D.cubicU D.cubicV
  let C : GCD369CubeHahnRegular k :=
    GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU
  let P : GCD369CubeHahnRegular k := terminalC5Coeff
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4
  have hR5 : R5.1.coeff T.delta =
      r ^ 4 * (-A ^ 2 * d + 21 * b ^ 2 + 6 * A * q) := by
    simpa only [R5] using normalRow5Coeff_doubleRoot_of_row12
      T.Xn T.Yn T.Zn D.cubicU D.cubicV T.delta T.hdelta
      A r d b q
      (by rw [D.constantCoeff_cubicU, hu])
      (by rw [D.constantCoeff_cubicV, hv])
      hord1 hord2 hcoeff1 hcoeff2
  have hC : GCD369CubeHahnRegular.constantCoeff C =
      -3 * r ^ 2 * A ^ 3 := by
    dsimp only [C]
    rw [GCD369CubeNormalRow5Cubic_map,
      D.constantCoeff_cubicU, hX, hY, hZ, hu]
    exact GCD369CubeNormalRow5Cubic_doubleRoot r A
  have hP : GCD369CubeHahnRegular.constantCoeff P =
      -73156608 * r ^ 10 := by
    dsimp only [P]
    simp only [terminalC5Coeff, map_add, map_sub, map_mul, map_pow,
      map_ofNat, map_neg]
    change terminalC5Coeff
      D.faber.scale.leading0 D.faber.scale.leading1
      D.faber.scale.leading2 D.faber.scale.leading3
      D.faber.scale.leading4 = -73156608 * r ^ 10
    rw [D.ha0, D.ha1, D.ha2, D.ha3, D.ha4, hu, hv]
    exact terminalC5Coeff_doubleRoot r
  have hload : D.faber.scale.weightedRegular 4 D.faber.c5 =
      H ^ 3 * GCD369CubeHahnRegular.constant C5 := by
    rw [hc5, D.faber.scale.weightedRegular_constant_eq_monomial_sq
      4 (by norm_num) C5]
    apply Subtype.ext
    change
      (HahnSeries.single (((4 : ℕ) : ℚ) * D.faber.scale.p / 2)
          (1 : k)) ^ 2 * HahnSeries.C C5 =
        (HahnSeries.single T.delta (1 : k)) ^ 3 * HahnSeries.C C5
    simp only [HahnSeries.single_pow, nsmul_eq_mul, one_pow]
    apply congrArg
      (fun z : ℚ => HahnSeries.single z (1 : k) * HahnSeries.C C5)
    calc
      2 * (4 * D.faber.scale.p / 2) = 4 * D.faber.scale.p := by ring
      _ = 3 * T.delta := htie
  have hchart0 : D.faber.scale.regular0 =
      D.cubicV ^ 2 + H * T.Zn := by
    rw [T.regular0_eq]
    dsimp only [H]
    rw [monomial_eq_regularMonomial]
    ring
  have hchart1 : D.faber.scale.regular1 =
      2 * D.cubicU * D.cubicV + H * T.Yn := by
    rw [T.regular1_eq]
    dsimp only [H]
    rw [monomial_eq_regularMonomial]
    ring
  have hchart2 : D.faber.scale.regular2 =
      D.cubicU ^ 2 + H * T.Xn := by
    rw [T.regular2_eq]
    dsimp only [H]
    rw [monomial_eq_regularMonomial]
    ring
  have hzero := GCD369CubeFaberFullN5_zeroHigh_expansion
    T.Xn T.Yn T.Zn D.cubicU D.cubicV H
  have hfactor :
      GCD369CubeFaberFullN5
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 0 0
        (D.faber.scale.weightedRegular 4 D.faber.c5)
        0 0 0 0 =
      (559872 * R5) * H ^ 2 +
        H ^ 3 * (839808 * C + GCD369CubeHahnRegular.constant C5 * P) := by
    rw [fullN5_c5_specialize, hload]
    rw [hchart0, hchart1, hchart2,
      D.regular3_eq_two_cubicV, D.regular4_eq_two_cubicU]
    rw [hzero]
    dsimp only [R5, C, P]
    rw [← hchart0, ← hchart1, ← hchart2,
      ← D.regular3_eq_two_cubicV, ← D.regular4_eq_two_cubicU]
    ring
  have hc := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (3 * T.delta)) hfactor
  have hquad := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (559872 * R5) T.delta T.delta T.hdelta.le 2
  change ((559872 * R5) * H ^ 2).1.coeff
      (T.delta + (2 : ℚ) * T.delta) =
        (559872 * R5).1.coeff T.delta at hquad
  have htop := GCD369CubeHahnRegular.coeff_monomial_pow_mul_at
    T.delta T.hdelta 3
      (839808 * C + GCD369CubeHahnRegular.constant C5 * P)
  change (H ^ 3 *
      (839808 * C + GCD369CubeHahnRegular.constant C5 * P)).1.coeff
        (3 * T.delta) =
      GCD369CubeHahnRegular.constantCoeff
        (839808 * C + GCD369CubeHahnRegular.constant C5 * P) at htop
  change
    (GCD369CubeFaberFullN5
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4 0 0
      (D.faber.scale.weightedRegular 4 D.faber.c5)
      0 0 0 0).1.coeff (3 * T.delta) =
        ((559872 * R5) * H ^ 2).1.coeff (3 * T.delta) +
        (H ^ 3 *
          (839808 * C + GCD369CubeHahnRegular.constant C5 * P)).1.coeff
            (3 * T.delta) at hc
  rw [show 3 * T.delta = T.delta + (2 : ℚ) * T.delta by ring,
    hquad] at hc
  rw [← show 3 * T.delta = T.delta + (2 : ℚ) * T.delta by ring,
    htop] at hc
  rw [htie]
  rw [hc]
  have hnat : (559872 * R5).1.coeff T.delta =
      (559872 : k) * R5.1.coeff T.delta :=
    GCD369CubeHahnRegular.coeff_nat_mul 559872 R5 T.delta
  rw [hnat, hR5]
  simp only [map_add, map_mul, map_ofNat,
    GCD369CubeHahnRegular.constantCoeff_constant, hC, hP]
  ring

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubeHahnCommonCoefficientData

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Rows one, two, and four at the balanced c5 resonance. -/
theorem TransverseScale.c5LoadedNormalRowsAt_balanced
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
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
    (r A0 : k)
    (hu : D.u = -3 * r ^ 2) (hv : D.v = 2 * r ^ 3)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r * A0)
    (htie : 4 * D.faber.scale.p = 3 * T.delta) :
    ((-32 * GCD369CubeNormalRow1
        T.Xn T.Yn T.Zn D.cubicU).1.coeff T.delta +
          241920 * r ^ 6 * C5 = 0) ∧
    ((32 * GCD369CubeNormalRow2
        T.Xn T.Yn T.Zn D.cubicU D.cubicV).1.coeff T.delta -
          622080 * r ^ 7 * C5 = 0) ∧
    ((32 * GCD369CubeNormalRow4
        T.Xn T.Yn T.Zn D.cubicU D.cubicV).1.coeff T.delta -
          314928 * r * A0 ^ 3 + 7257600 * r ^ 9 * C5 = 0) := by
  let F := D.faber
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let N1 : GCD369CubeHahnRegular k := GCD369CubeFaberN1
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
  let N2 : GCD369CubeHahnRegular k := GCD369CubeFaberN2
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
  let N4 : GCD369CubeHahnRegular k := GCD369CubeFaberN4
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
  let Row1 : GCD369CubeHahnRegular k :=
    GCD369CubeNormalRow1 T.Xn T.Yn T.Zn D.cubicU
  let Row2 : GCD369CubeHahnRegular k :=
    GCD369CubeNormalRow2 T.Xn T.Yn T.Zn D.cubicU D.cubicV
  let Row4 : GCD369CubeHahnRegular k :=
    GCD369CubeNormalRow4 T.Xn T.Yn T.Zn D.cubicU D.cubicV
  let P1 : GCD369CubeHahnRegular k :=
    51840 * F.scale.regular0 -
      8640 * F.scale.regular2 * F.scale.regular4 -
      4320 * F.scale.regular3 ^ 2 + 1680 * F.scale.regular4 ^ 3
  let P2 : GCD369CubeHahnRegular k :=
    -25920 * F.scale.regular1 * F.scale.regular4 -
      25920 * F.scale.regular2 * F.scale.regular3 +
      15120 * F.scale.regular3 * F.scale.regular4 ^ 2
  let P4 : GCD369CubeHahnRegular k :=
    -233280 * F.scale.regular1 * F.scale.regular2 +
      58320 * F.scale.regular1 * F.scale.regular4 ^ 2 +
      155520 * F.scale.regular2 * F.scale.regular3 * F.scale.regular4 +
      25920 * F.scale.regular3 ^ 3 -
      45360 * F.scale.regular3 * F.scale.regular4 ^ 3
  let c5w : GCD369CubeHahnRegular k :=
    F.scale.weightedRegular 4 (GCD369CubeHahnRegular.constant C5)
  have hload1 : GCD369CubeHahnRegular.constantCoeff P1 =
      241920 * r ^ 6 := by
    dsimp only [P1, F]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    change 51840 * F.scale.leading0 -
      8640 * F.scale.leading2 * F.scale.leading4 -
      4320 * F.scale.leading3 ^ 2 + 1680 * F.scale.leading4 ^ 3 = _
    rw [D.ha0, D.ha2, D.ha3, D.ha4, hu, hv]
    ring
  have hload2 : GCD369CubeHahnRegular.constantCoeff P2 =
      -622080 * r ^ 7 := by
    dsimp only [P2, F]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg]
    change -25920 * F.scale.leading1 * F.scale.leading4 -
      25920 * F.scale.leading2 * F.scale.leading3 +
      15120 * F.scale.leading3 * F.scale.leading4 ^ 2 = _
    rw [D.ha1, D.ha2, D.ha3, D.ha4, hu, hv]
    ring
  have hload4 : GCD369CubeHahnRegular.constantCoeff P4 =
      7257600 * r ^ 9 := by
    dsimp only [P4, F]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg]
    change -233280 * F.scale.leading1 * F.scale.leading2 +
      58320 * F.scale.leading1 * F.scale.leading4 ^ 2 +
      155520 * F.scale.leading2 * F.scale.leading3 * F.scale.leading4 +
      25920 * F.scale.leading3 ^ 3 -
      45360 * F.scale.leading3 * F.scale.leading4 ^ 3 = _
    rw [D.ha1, D.ha2, D.ha3, D.ha4, hu, hv]
    ring
  have hweight1 : (c5w * P1).1.coeff (4 * F.scale.p) =
      C5 * GCD369CubeHahnRegular.constantCoeff P1 := by
    simpa only [c5w] using
      F.scale.weightedRegular_four_constant_mul_coeff C5 P1
  have hweight2 : (c5w * P2).1.coeff (4 * F.scale.p) =
      C5 * GCD369CubeHahnRegular.constantCoeff P2 := by
    simpa only [c5w] using
      F.scale.weightedRegular_four_constant_mul_coeff C5 P2
  have hweight4 : (c5w * P4).1.coeff (4 * F.scale.p) =
      C5 * GCD369CubeHahnRegular.constantCoeff P4 := by
    simpa only [c5w] using
      F.scale.weightedRegular_four_constant_mul_coeff C5 P4
  have hz := F.c5NCoeff_zero C4 C3 C2 C1
    Rho1 Rho2 Rho3 Rho4 hd hc7 hc4 hc3 hc2 hc1
    hrho1 hrho2 hrho3 hrho4
  have hz1 := hz.1
  have hz2 := hz.2.1
  have hz4 := hz.2.2.2
  rw [hc5] at hz1 hz2 hz4
  change (729 * N1).1.coeff (4 * F.scale.p) +
      (c5w * P1).1.coeff (4 * F.scale.p) = 0 at hz1
  change (2187 * N2).1.coeff (4 * F.scale.p) +
      (c5w * P2).1.coeff (4 * F.scale.p) = 0 at hz2
  change (6561 * N4).1.coeff (4 * F.scale.p) +
      (c5w * P4).1.coeff (4 * F.scale.p) = 0 at hz4
  rw [hweight1, hload1] at hz1
  rw [hweight2, hload2] at hz2
  rw [hweight4, hload4] at hz4
  have hexp1 := T.zeroHighN1Expansion
  have hexp2 := T.zeroHighN2Expansion
  have hexp4 := T.zeroHighN4Expansion
  rw [monomial_eq_regularMonomial] at hexp1 hexp2 hexp4
  have hc1' := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (4 * F.scale.p)) hexp1
  have hc2' := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (4 * F.scale.p)) hexp2
  have hc4' := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (4 * F.scale.p)) hexp4
  have hshift1 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (-32 * Row1) T.delta T.delta T.hdelta.le 2
  have hshift2 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (32 * Row2) T.delta T.delta T.hdelta.le 2
  have hshift4 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (32 * Row4) T.delta T.delta T.hdelta.le 2
  change ((-32 * Row1) * H ^ 2).1.coeff
      (T.delta + (2 : ℚ) * T.delta) = (-32 * Row1).1.coeff T.delta
    at hshift1
  change ((32 * Row2) * H ^ 2).1.coeff
      (T.delta + (2 : ℚ) * T.delta) = (32 * Row2).1.coeff T.delta
    at hshift2
  change ((32 * Row4) * H ^ 2).1.coeff
      (T.delta + (2 : ℚ) * T.delta) = (32 * Row4).1.coeff T.delta
    at hshift4
  have hcubic := GCD369CubeHahnRegular.coeff_mul_monomial_pow_at
    T.delta T.hdelta 3 (314928 * T.Yn * T.Xn ^ 2)
  change ((314928 * T.Yn * T.Xn ^ 2) * H ^ 3).1.coeff
      (3 * T.delta) = GCD369CubeHahnRegular.constantCoeff
        (314928 * T.Yn * T.Xn ^ 2) at hcubic
  have hcubicval :
      ((314928 * T.Yn * T.Xn ^ 2) * H ^ 3).1.coeff
          (4 * F.scale.p) = 314928 * r * A0 ^ 3 := by
    rw [htie, hcubic]
    simp only [map_mul, map_pow, map_ofNat, hY, hX]
    ring
  change (729 * N1).1.coeff (4 * F.scale.p) =
      ((-32 * Row1) * H ^ 2).1.coeff (4 * F.scale.p) at hc1'
  change (2187 * N2).1.coeff (4 * F.scale.p) =
      ((32 * Row2) * H ^ 2).1.coeff (4 * F.scale.p) at hc2'
  change (6561 * N4).1.coeff (4 * F.scale.p) =
      ((32 * Row4) * H ^ 2).1.coeff (4 * F.scale.p) -
        ((314928 * T.Yn * T.Xn ^ 2) * H ^ 3).1.coeff
          (4 * F.scale.p) at hc4'
  rw [htie, show 3 * T.delta = T.delta + (2 : ℚ) * T.delta by ring,
    hshift1] at hc1'
  rw [htie, show 3 * T.delta = T.delta + (2 : ℚ) * T.delta by ring,
    hshift2] at hc2'
  rw [htie, show 3 * T.delta = T.delta + (2 : ℚ) * T.delta by ring,
    hshift4] at hc4'
  have hcubicval' :
      ((314928 * T.Yn * T.Xn ^ 2) * H ^ 3).1.coeff
          (T.delta + 2 * T.delta) = 314928 * r * A0 ^ 3 := by
    rw [← show 3 * T.delta = T.delta + 2 * T.delta by ring,
      ← htie]
    exact hcubicval
  rw [hcubicval'] at hc4'
  rw [htie, show 3 * T.delta = T.delta + 2 * T.delta by ring]
    at hz1 hz2 hz4
  rw [hc1'] at hz1
  rw [hc2'] at hz2
  rw [hc4'] at hz4
  constructor
  · linear_combination hz1
  constructor
  · linear_combination hz2
  · linear_combination hz4

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubeHahnFaberPoleData

/-- With `d = c7 = 0`, loads after `c5` are invisible through the
weight-four coefficient. -/
theorem fullN5_sub_c5Specialized_mem_higherOrderIdeal_local
    {k : Type*} [Field k] [CharZero k]
    (F : GCD369CubeHahnFaberPoleData k)
    (C4 C3 C2 C1 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1) :
    GCD369CubeFaberFullN5
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4
      (F.scale.weightedRegular 1 F.d)
      (F.scale.weightedRegular 2 F.c7)
      (F.scale.weightedRegular 4 F.c5)
      (F.scale.weightedRegular 5 F.c4)
      (F.scale.weightedRegular 6 F.c3)
      (F.scale.weightedRegular 7 F.c2)
      (F.scale.weightedRegular 8 F.c1) -
    GCD369CubeFaberFullN5
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4 0 0
      (F.scale.weightedRegular 4 F.c5) 0 0 0 0 ∈
        GCD369CubeHahnRegular.higherOrderIdeal
          (4 * F.scale.p) (mul_nonneg (by norm_num) F.scale.hp.le) := by
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal
      (4 * F.scale.p) (mul_nonneg (by norm_num) F.scale.hp.le)
  let Q := Ideal.Quotient.mk I
  have hweight (w : ℕ) (hw : 4 < w) :
      4 * F.scale.p < (w : ℚ) * F.scale.p := by
    exact mul_lt_mul_of_pos_right
      (show (4 : ℚ) < (w : ℚ) by exact_mod_cast hw) F.scale.hp
  have hdq : Q (F.scale.weightedRegular 1 F.d) = 0 := by
    rw [hd]
    have hz : F.scale.weightedRegular 1
        (GCD369CubeHahnRegular.constant (0 : k)) = 0 := by
      apply Subtype.ext
      change F.scale.t ^ 1 * HahnSeries.C (0 : k) = 0
      simp
    rw [hz, map_zero]
  have hc7q : Q (F.scale.weightedRegular 2 F.c7) = 0 := by
    rw [hc7]
    have hz : F.scale.weightedRegular 2
        (GCD369CubeHahnRegular.constant (0 : k)) = 0 := by
      apply Subtype.ext
      change F.scale.t ^ 2 * HahnSeries.C (0 : k) = 0
      simp
    rw [hz, map_zero]
  have hc4q : Q (F.scale.weightedRegular 5 F.c4) = 0 := by
    rw [hc4, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 5 C4 (mul_nonneg (by norm_num) F.scale.hp.le)
        (hweight 5 (by norm_num))
  have hc3q : Q (F.scale.weightedRegular 6 F.c3) = 0 := by
    rw [hc3, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 6 C3 (mul_nonneg (by norm_num) F.scale.hp.le)
        (hweight 6 (by norm_num))
  have hc2q : Q (F.scale.weightedRegular 7 F.c2) = 0 := by
    rw [hc2, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 7 C2 (mul_nonneg (by norm_num) F.scale.hp.le)
        (hweight 7 (by norm_num))
  have hc1q : Q (F.scale.weightedRegular 8 F.c1) = 0 := by
    rw [hc1, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 8 C1 (mul_nonneg (by norm_num) F.scale.hp.le)
        (hweight 8 (by norm_num))
  let full : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
    (F.scale.weightedRegular 1 F.d)
    (F.scale.weightedRegular 2 F.c7)
    (F.scale.weightedRegular 4 F.c5)
    (F.scale.weightedRegular 5 F.c4)
    (F.scale.weightedRegular 6 F.c3)
    (F.scale.weightedRegular 7 F.c2)
    (F.scale.weightedRegular 8 F.c1)
  let c5row : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4 0 0
    (F.scale.weightedRegular 4 F.c5) 0 0 0 0
  have hq : Q full = Q c5row := by
    dsimp only [full, c5row]
    rw [GCD369CubeFaberFullN5_map, GCD369CubeFaberFullN5_map,
      hdq, hc7q, hc4q, hc3q, hc2q, hc1q]
    simp
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [map_sub, hq, sub_self]

/-- Coefficient version of the c5 specialization comparison. -/
theorem fullN5Coeff_eq_c5Specialized
    {k : Type*} [Field k] [CharZero k]
    (F : GCD369CubeHahnFaberPoleData k)
    (C4 C3 C2 C1 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1) :
    (GCD369CubeFaberFullN5
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4
      (F.scale.weightedRegular 1 F.d)
      (F.scale.weightedRegular 2 F.c7)
      (F.scale.weightedRegular 4 F.c5)
      (F.scale.weightedRegular 5 F.c4)
      (F.scale.weightedRegular 6 F.c3)
      (F.scale.weightedRegular 7 F.c2)
      (F.scale.weightedRegular 8 F.c1)).1.coeff (4 * F.scale.p) =
    (GCD369CubeFaberFullN5
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4 0 0
      (F.scale.weightedRegular 4 F.c5) 0 0 0 0).1.coeff
        (4 * F.scale.p) := by
  let full : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
    (F.scale.weightedRegular 1 F.d)
    (F.scale.weightedRegular 2 F.c7)
    (F.scale.weightedRegular 4 F.c5)
    (F.scale.weightedRegular 5 F.c4)
    (F.scale.weightedRegular 6 F.c3)
    (F.scale.weightedRegular 7 F.c2)
    (F.scale.weightedRegular 8 F.c1)
  let c5row : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4 0 0
    (F.scale.weightedRegular 4 F.c5) 0 0 0 0
  have hdiff := F.fullN5_sub_c5Specialized_mem_higherOrderIdeal
    C4 C3 C2 C1 hd hc7 hc4 hc3 hc2 hc1
  have hcoeff : (full - c5row).1.coeff (4 * F.scale.p) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop hdiff
  change full.1.coeff (4 * F.scale.p) =
    c5row.1.coeff (4 * F.scale.p)
  change full.1.coeff (4 * F.scale.p) -
      c5row.1.coeff (4 * F.scale.p) = 0 at hcoeff
  exact sub_eq_zero.mp hcoeff

end GCD369CubeHahnFaberPoleData

namespace GCD369CubeHahnCommonCoefficientData

/-- The complete balanced c5 fifth coefficient. -/
theorem TransverseScale.fullN5Coeff_at_c5_balanced
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C5 C4 C3 C2 C1 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (r A d b q : k)
    (hu : D.u = -3 * r ^ 2) (hv : D.v = 2 * r ^ 3)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r * A)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r ^ 2 * A)
    (htie : 4 * D.faber.scale.p = 3 * T.delta)
    (hord1 : (↑T.delta : WithTop ℚ) ≤
      (GCD369CubeNormalRow1 T.Xn T.Yn T.Zn D.cubicU).1.orderTop)
    (hord2 : (↑T.delta : WithTop ℚ) ≤
      (GCD369CubeNormalRow2 T.Xn T.Yn T.Zn
        D.cubicU D.cubicV).1.orderTop)
    (hcoeff1 :
      (GCD369CubeNormalRow1 T.Xn T.Yn T.Zn D.cubicU).1.coeff T.delta =
        729 * (A ^ 2 * d - 2 * A * q - b ^ 2))
    (hcoeff2 :
      (GCD369CubeNormalRow2 T.Xn T.Yn T.Zn
        D.cubicU D.cubicV).1.coeff T.delta =
        -1458 * (2 * A ^ 2 * r * d - 3 * A * r * q +
          3 * r * b ^ 2)) :
    (GCD369CubeFaberFullN5
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (D.faber.scale.weightedRegular 1 D.faber.d)
      (D.faber.scale.weightedRegular 2 D.faber.c7)
      (D.faber.scale.weightedRegular 4 D.faber.c5)
      (D.faber.scale.weightedRegular 5 D.faber.c4)
      (D.faber.scale.weightedRegular 6 D.faber.c3)
      (D.faber.scale.weightedRegular 7 D.faber.c2)
      (D.faber.scale.weightedRegular 8 D.faber.c1)).1.coeff
        (4 * D.faber.scale.p) =
      559872 * r ^ 4 * (-A ^ 2 * d + 21 * b ^ 2 + 6 * A * q) -
        2519424 * r ^ 2 * A ^ 3 - 73156608 * r ^ 10 * C5 := by
  calc
    _ = (GCD369CubeFaberFullN5
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 0 0
        (D.faber.scale.weightedRegular 4 D.faber.c5)
        0 0 0 0).1.coeff (4 * D.faber.scale.p) :=
      D.faber.fullN5Coeff_eq_c5Specialized
        C4 C3 C2 C1 hd hc7 hc4 hc3 hc2 hc1
    _ = _ := T.c5SpecializedTerminalCoeff_at_balanced
      C5 hc5 r A d b q hu hv hX hY hZ htie
      hord1 hord2 hcoeff1 hcoeff2

/-- Vanishing of the global weight-four coefficient supplies the fifth
balanced c5 equation. -/
theorem TransverseScale.c5LoadedTerminalEquation_at_balanced
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C5 C4 C3 C2 C1 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (r A d b q : k)
    (hu : D.u = -3 * r ^ 2) (hv : D.v = 2 * r ^ 3)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r * A)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r ^ 2 * A)
    (htie : 4 * D.faber.scale.p = 3 * T.delta)
    (hord1 : (↑T.delta : WithTop ℚ) ≤
      (GCD369CubeNormalRow1 T.Xn T.Yn T.Zn D.cubicU).1.orderTop)
    (hord2 : (↑T.delta : WithTop ℚ) ≤
      (GCD369CubeNormalRow2 T.Xn T.Yn T.Zn
        D.cubicU D.cubicV).1.orderTop)
    (hcoeff1 :
      (GCD369CubeNormalRow1 T.Xn T.Yn T.Zn D.cubicU).1.coeff T.delta =
        729 * (A ^ 2 * d - 2 * A * q - b ^ 2))
    (hcoeff2 :
      (GCD369CubeNormalRow2 T.Xn T.Yn T.Zn
        D.cubicU D.cubicV).1.coeff T.delta =
        -1458 * (2 * A ^ 2 * r * d - 3 * A * r * q +
          3 * r * b ^ 2))
    (hzero :
      (GCD369CubeFaberFullN5
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4
        (D.faber.scale.weightedRegular 1 D.faber.d)
        (D.faber.scale.weightedRegular 2 D.faber.c7)
        (D.faber.scale.weightedRegular 4 D.faber.c5)
        (D.faber.scale.weightedRegular 5 D.faber.c4)
        (D.faber.scale.weightedRegular 6 D.faber.c3)
        (D.faber.scale.weightedRegular 7 D.faber.c2)
        (D.faber.scale.weightedRegular 8 D.faber.c1)).1.coeff
          (4 * D.faber.scale.p) = 0) :
    559872 * r ^ 4 * (-A ^ 2 * d + 21 * b ^ 2 + 6 * A * q) -
      2519424 * r ^ 2 * A ^ 3 - 73156608 * r ^ 10 * C5 = 0 := by
  rw [T.fullN5Coeff_at_c5_balanced
    C5 C4 C3 C2 C1 hd hc7 hc5 hc4 hc3 hc2 hc1
    r A d b q hu hv hX hY hZ htie
    hord1 hord2 hcoeff1 hcoeff2] at hzero
  exact hzero

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubePolynomialSource

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Degree integrality turns the balanced c5 terminal coefficient into the
fifth algebraic row. -/
theorem infinity_c5LoadedTerminalEquation_at_balanced
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (hdisc :
      4 * (S.infinityCommonCoefficientData hsdegree).u ^ 3 +
        27 * (S.infinityCommonCoefficientData hsdegree).v ^ 2 = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (C5 C4 C3 C2 C1 : k)
    (hd : (S.infinityCommonCoefficientData hsdegree).faber.d =
      GCD369CubeHahnRegular.constant 0)
    (hc7 : (S.infinityCommonCoefficientData hsdegree).faber.c7 =
      GCD369CubeHahnRegular.constant 0)
    (hc5 : (S.infinityCommonCoefficientData hsdegree).faber.c5 =
      GCD369CubeHahnRegular.constant C5)
    (hc4 : (S.infinityCommonCoefficientData hsdegree).faber.c4 =
      GCD369CubeHahnRegular.constant C4)
    (hc3 : (S.infinityCommonCoefficientData hsdegree).faber.c3 =
      GCD369CubeHahnRegular.constant C3)
    (hc2 : (S.infinityCommonCoefficientData hsdegree).faber.c2 =
      GCD369CubeHahnRegular.constant C2)
    (hc1 : (S.infinityCommonCoefficientData hsdegree).faber.c1 =
      GCD369CubeHahnRegular.constant C1)
    (r A d b q : k)
    (hu : (S.infinityCommonCoefficientData hsdegree).u = -3 * r ^ 2)
    (hv : (S.infinityCommonCoefficientData hsdegree).v = 2 * r ^ 3)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r * A)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r ^ 2 * A)
    (htie : 4 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p =
      3 * T.delta)
    (hord1 : (↑T.delta : WithTop ℚ) ≤
      (GCD369CubeNormalRow1 T.Xn T.Yn T.Zn
        (S.infinityCommonCoefficientData hsdegree).cubicU).1.orderTop)
    (hord2 : (↑T.delta : WithTop ℚ) ≤
      (GCD369CubeNormalRow2 T.Xn T.Yn T.Zn
        (S.infinityCommonCoefficientData hsdegree).cubicU
        (S.infinityCommonCoefficientData hsdegree).cubicV).1.orderTop)
    (hcoeff1 :
      (GCD369CubeNormalRow1 T.Xn T.Yn T.Zn
        (S.infinityCommonCoefficientData hsdegree).cubicU).1.coeff T.delta =
          729 * (A ^ 2 * d - 2 * A * q - b ^ 2))
    (hcoeff2 :
      (GCD369CubeNormalRow2 T.Xn T.Yn T.Zn
        (S.infinityCommonCoefficientData hsdegree).cubicU
        (S.infinityCommonCoefficientData hsdegree).cubicV).1.coeff T.delta =
          -1458 * (2 * A ^ 2 * r * d - 3 * A * r * q +
            3 * r * b ^ 2)) :
    559872 * r ^ 4 * (-A ^ 2 * d + 21 * b ^ 2 + 6 * A * q) -
      2519424 * r ^ 2 * A ^ 3 - 73156608 * r ^ 10 * C5 = 0 := by
  let D := S.infinityCommonCoefficientData hsdegree
  have hzero := S.infinity_fullN5Coeff_weight_p_eq_zero_of_singular
    hsdegree 4 (by norm_num) hdisc
  exact T.c5LoadedTerminalEquation_at_balanced
    C5 C4 C3 C2 C1 hd hc7 hc5 hc4 hc3 hc2 hc1
    r A d b q hu hv hX hY hZ htie
    hord1 hord2 hcoeff1 hcoeff2
      (by simpa only [D, Nat.cast_ofNat] using hzero)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- After `d = c7 = 0`, the singular resonance `4 p = 3 delta` is
impossible for a constant-core infinity source. -/
theorem infinity_c5_singular_balanced_inconsistent
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hd0 : S.faberConstantParameters.d = 0)
    (hc70 : S.faberConstantParameters.c7 = 0)
    (htie :
      4 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p =
        3 * T.delta) :
    False := by
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let D := S.infinityCommonCoefficientData hsdegree
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  obtain ⟨hd, hc7, hc5, hc4, hc3, hc2, hc1,
      hr1, hr2, hr3, hr4⟩ :=
    S.infinityFaberPoleData_constant_loads hpole
  have hdD : D.faber.d = GCD369CubeHahnRegular.constant 0 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree,
      hd0] using hd
  have hc7D : D.faber.c7 = GCD369CubeHahnRegular.constant 0 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree,
      hc70] using hc7
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
  have hdDz : D.faber.d = 0 := by simpa using hdD
  have hc7Dz : D.faber.c7 = 0 := by simpa using hc7D
  have hearly : 2 * T.delta < 4 * D.faber.scale.p := by
    rw [htie]
    linarith [T.hdelta]
  obtain ⟨hz1, hz2, hz3, hz4⟩ :=
    T.zeroLoadLeadingRows_before_c5_coeff hdDz hc7Dz hearly
  obtain ⟨r, hA0, hu, hv, hY, hZ⟩ :=
    GCD369CubeZeroLoadNormal_parametrization
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn)
      D.u D.v T.hleading hz1 hz2 hz3 hz4
  let A0 : k := GCD369CubeHahnRegular.constantCoeff T.Xn
  have hr : r ≠ 0 := by
    intro hr0
    have hu0 : D.u = 0 := by rw [hu, hr0]; norm_num
    have hv0 : D.v = 0 := by rw [hv, hr0]; norm_num
    exact D.hprojective.elim (fun h => h hu0) (fun h => h hv0)
  have hdisc : 4 * D.u ^ 3 + 27 * D.v ^ 2 = 0 := by
    rw [hu, hv]
    ring
  have hU : GCD369CubeHahnRegular.constantCoeff D.cubicU ≠ 0 := by
    rw [D.constantCoeff_cubicU, hu]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hr)
  let rr : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.movingDoubleRoot D.cubicU D.cubicV hU
  have hrr : GCD369CubeHahnRegular.constantCoeff rr = r := by
    exact GCD369CubeHahnRegular.constantCoeff_movingDoubleRoot
      D.cubicU D.cubicV hU r
      (by rw [D.constantCoeff_cubicU, hu])
      (by rw [D.constantCoeff_cubicV, hv]) hr
  have hroot : 2 * D.cubicU * rr + 3 * D.cubicV = 0 :=
    GCD369CubeHahnRegular.movingDoubleRoot_relation D.cubicU D.cubicV hU
  let A : GCD369CubeHahnRegular k := T.Xn
  let ddev : GCD369CubeHahnRegular k := D.cubicU + 3 * rr ^ 2
  let Bdev : GCD369CubeHahnRegular k := T.Yn - rr * A
  let Cdev : GCD369CubeHahnRegular k := T.Zn + 2 * rr ^ 2 * A
  let Row1 : GCD369CubeHahnRegular k :=
    A ^ 2 * ddev - 2 * A * Bdev * rr - Bdev ^ 2 - 2 * A * Cdev
  let Row2 : GCD369CubeHahnRegular k :=
    2 * A ^ 2 * rr * ddev - 3 * A * Bdev * rr ^ 2 -
      3 * A * Cdev * rr + 3 * A * Bdev * ddev - 3 * Bdev * Cdev
  let Row3 : GCD369CubeHahnRegular k :=
    -2 * A ^ 2 * rr ^ 2 * ddev + 6 * Bdev ^ 2 * rr ^ 2 +
      2 * A ^ 2 * ddev ^ 2 - 2 * Bdev ^ 2 * ddev -
      4 * A * Cdev * ddev + 3 * Cdev ^ 2
  let Row4 : GCD369CubeHahnRegular k :=
    4374 * (-3 * rr ^ 2 + ddev) *
      (A * Bdev * rr ^ 2 + 2 * Bdev ^ 2 * rr + A * Cdev * rr +
        3 * A * Bdev * ddev - 3 * Bdev * Cdev)
  have hddev0 : GCD369CubeHahnRegular.constantCoeff ddev = 0 := by
    dsimp only [ddev]
    simp only [map_add, map_mul, map_pow, map_ofNat,
      D.constantCoeff_cubicU, hrr, hu]
    ring
  have hBdev0 : GCD369CubeHahnRegular.constantCoeff Bdev = 0 := by
    dsimp only [Bdev, A, A0]
    simp only [map_sub, map_mul, hY, hrr]
    ring
  have hCdev0 : GCD369CubeHahnRegular.constantCoeff Cdev = 0 := by
    dsimp only [Cdev, A, A0]
    simp only [map_add, map_mul, map_pow, map_ofNat, hZ, hrr]
    ring
  have hrows : ∀ e : ℚ, 0 ≤ e → e < T.delta →
      Row1.1.coeff e = 0 ∧ Row2.1.coeff e = 0 ∧
        Row3.1.coeff e = 0 := by
    intro e he hedelta
    have hearly' : 2 * T.factor.delta + e < 4 * D.faber.scale.p := by
      change 2 * T.delta + e < 4 * D.faber.scale.p
      rw [htie]
      linarith
    have h := T.factor.doubleRoot_row123Coeffs_zero_before_c5_coeff
      hdDz hc7Dz rr hroot e he hedelta hearly'
    simpa only [GCD369CubeHahnCommonCoefficientData.TransverseScale.factor,
      Row1, Row2, Row3, A, ddev, Bdev, Cdev] using h
  have hhalf :=
    GCD369CubeHahnRegular.doubleBlowup_deviations_order_half_lower_of_rows
      T.delta T.hdelta A rr ddev Bdev Cdev hddev0 hBdev0 hCdev0
      (by simpa only [A, A0] using hA0)
      (by simpa only [hrr] using hr)
      (by
        intro e he hedelta
        simpa only [Row1, Row2, Row3] using hrows e he hedelta)
  have hR1 : (↑T.delta : WithTop ℚ) ≤ Row1.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro e he
    have he' : e < T.delta := WithTop.coe_lt_coe.mp he
    by_cases he0 : 0 ≤ e
    · exact (hrows e he0 he').1
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg Row1
        (lt_of_not_ge he0)
  have hR2 : (↑T.delta : WithTop ℚ) ≤ Row2.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro e he
    have he' : e < T.delta := WithTop.coe_lt_coe.mp he
    by_cases he0 : 0 ≤ e
    · exact (hrows e he0 he').2.1
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg Row2
        (lt_of_not_ge he0)
  let mu : ℚ := T.delta / 2
  have hmu : 0 < mu := by dsimp only [mu]; linarith [T.hdelta]
  have htwomu : 2 * mu = T.delta := by dsimp only [mu]; ring
  obtain ⟨d0, b0, q0, hq1, hq2, hq4⟩ :=
    GCD369CubeHahnRegular.doubleBlowup_balanced_coefficients_of_order
      mu hmu A rr ddev Bdev Cdev
      (by simpa only [A, A0] using hA0)
      (by simpa only [hrr] using hr)
      (by simpa only [mu] using hhalf.1)
      (by simpa only [mu] using hhalf.2.1)
      (by simpa only [mu] using hhalf.2.2)
      (by simpa only [htwomu, Row1] using hR1)
      (by simpa only [htwomu, Row2] using hR2)
  rw [htwomu] at hq1 hq2 hq4
  have hYeq : T.Yn = rr * A + Bdev := by
    dsimp only [Bdev, A]
    ring
  have hZeq : T.Zn = -2 * rr ^ 2 * A + Cdev := by
    dsimp only [Cdev, A]
    ring
  have hUeq : D.cubicU = -3 * rr ^ 2 + ddev := by
    dsimp only [ddev]
    ring
  let ee : GCD369CubeHahnRegular k := D.cubicV - 2 * rr ^ 3
  have hVeq : D.cubicV = 2 * rr ^ 3 + ee := by
    dsimp only [ee]
    ring
  have hre : 3 * ee + 2 * ddev * rr = 0 := by
    dsimp only [ee, ddev]
    linear_combination hroot
  have hrow1 : GCD369CubeNormalRow1 T.Xn T.Yn T.Zn D.cubicU =
      729 * Row1 := by
    rw [show T.Xn = A by rfl, hYeq, hZeq, hUeq]
    simpa only [Row1] using
      (GCD369CubeDoubleBlowupRow1 A Bdev Cdev rr ddev)
  have hrow2 : GCD369CubeNormalRow2 T.Xn T.Yn T.Zn
      D.cubicU D.cubicV = -1458 * Row2 := by
    rw [show T.Xn = A by rfl, hYeq, hZeq, hUeq, hVeq]
    simpa only [Row2] using
      (GCD369CubeDoubleBlowupRow2 A Bdev Cdev rr ddev ee hre)
  have hrow4 : GCD369CubeNormalRow4 T.Xn T.Yn T.Zn
      D.cubicU D.cubicV = Row4 := by
    rw [show T.Xn = A by rfl, hYeq, hZeq, hUeq, hVeq]
    simpa only [Row4] using
      (GCD369CubeDoubleBlowupRow4 A Bdev Cdev rr ddev ee hre)
  have hord1 : (↑T.delta : WithTop ℚ) ≤
      (GCD369CubeNormalRow1 T.Xn T.Yn T.Zn D.cubicU).1.orderTop := by
    rw [hrow1, HahnSeries.le_orderTop_iff_forall]
    intro q hq
    have hz : Row1.1.coeff q = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_orderTop (hq.trans_le hR1)
    have hs : 729 * Row1 = (729 : ℤ) * Row1 := by ring
    rw [hs, GCD369CubeHahnRegular.coeff_int_mul, hz, mul_zero]
  have hord2 : (↑T.delta : WithTop ℚ) ≤
      (GCD369CubeNormalRow2 T.Xn T.Yn T.Zn
        D.cubicU D.cubicV).1.orderTop := by
    rw [hrow2, HahnSeries.le_orderTop_iff_forall]
    intro q hq
    have hz : Row2.1.coeff q = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_orderTop (hq.trans_le hR2)
    have hs : -1458 * Row2 = (-1458 : ℤ) * Row2 := by ring
    rw [hs, GCD369CubeHahnRegular.coeff_int_mul, hz, mul_zero]
  have hcoeff1 :
      (GCD369CubeNormalRow1 T.Xn T.Yn T.Zn D.cubicU).1.coeff T.delta =
        729 * (A0 ^ 2 * d0 - 2 * A0 * q0 - b0 ^ 2) := by
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff T.delta) hrow1
    have hn : (729 * Row1).1.coeff T.delta =
        (729 : k) * Row1.1.coeff T.delta :=
      GCD369CubeHahnRegular.coeff_nat_mul 729 Row1 T.delta
    rw [hn, hq1] at hc
    simpa only [A, A0] using hc
  have hcoeff2 :
      (GCD369CubeNormalRow2 T.Xn T.Yn T.Zn
        D.cubicU D.cubicV).1.coeff T.delta =
        -1458 * (2 * A0 ^ 2 * r * d0 - 3 * A0 * r * q0 +
          3 * r * b0 ^ 2) := by
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff T.delta) hrow2
    have hs : -1458 * Row2 = (-1458 : ℤ) * Row2 := by ring
    rw [hs, GCD369CubeHahnRegular.coeff_int_mul, hq2] at hc
    norm_num at hc
    simp only [A, hrr] at hc
    linear_combination hc
  obtain ⟨hload1, hload2, hload4⟩ := T.c5LoadedNormalRowsAt_balanced
    P.c5 P.c4 P.c3 P.c2 P.c1
      R.rho1 R.rho2 R.rho3 R.rho4
    hdD hc7D hc5D hc4D hc3D hc2D hc1D
      hr1D hr2D hr3D hr4D
    r A0 hu hv rfl hY htie
  have hcoeff32 : (32 * Row4).1.coeff T.delta =
      (32 : k) * Row4.1.coeff T.delta :=
    GCD369CubeHahnRegular.coeff_nat_mul 32 Row4 T.delta
  rw [hrow1] at hload1
  rw [hrow2] at hload2
  rw [hrow4, hcoeff32, hq4] at hload4
  have hs1 : -32 * (729 * Row1) = (-23328 : ℤ) * Row1 := by ring
  have hs2 : 32 * (-1458 * Row2) = (-46656 : ℤ) * Row2 := by ring
  rw [hs1, GCD369CubeHahnRegular.coeff_int_mul, hq1] at hload1
  rw [hs2, GCD369CubeHahnRegular.coeff_int_mul, hq2] at hload2
  simp only [A, A0, hrr] at hload1 hload2 hload4
  have h5 := S.infinity_c5LoadedTerminalEquation_at_balanced
    hsdegree hdisc T
    P.c5 P.c4 P.c3 P.c2 P.c1
    hdD hc7D hc5D hc4D hc3D hc2D hc1D
    r A0 d0 b0 q0 hu hv rfl hY hZ htie
    hord1 hord2 hcoeff1 hcoeff2
  apply GCD369Cube_c5Load_balanced_terminal_inconsistent
    A0 r d0 b0 q0 P.c5 hA0 hr
  · linear_combination hload1
  · linear_combination hload2
  · linear_combination hload4
  · exact h5

end GCD369CubePolynomialSource

#print axioms GCD369Cube_c5Load_balanced_terminal_inconsistent
#print axioms GCD369CubeHahnCommonCoefficientData.terminalC5Coeff_doubleRoot
#print axioms GCD369CubeHahnCommonCoefficientData.TransverseScale.c5SpecializedTerminalCoeff_at_balanced
#print axioms GCD369CubeHahnFaberPoleData.fullN5Coeff_eq_c5Specialized
#print axioms GCD369CubeHahnCommonCoefficientData.TransverseScale.c5LoadedTerminalEquation_at_balanced
#print axioms GCD369CubeHahnCommonCoefficientData.TransverseScale.c5LoadedNormalRowsAt_balanced
#print axioms GCD369CubePolynomialSource.infinity_c5LoadedTerminalEquation_at_balanced
#print axioms GCD369CubePolynomialSource.infinity_c5_singular_balanced_inconsistent
