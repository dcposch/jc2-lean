import InfinityC7Load
import InfinitySingularTerminalCoeff

/-! # The balanced weight-two load at infinity

At the resonance `2 * p = 3 * delta`, the first four `c7` rows leave one
genuine quadratic survivor.  The infinity terminal equation supplies the
missing fifth row.  The algebra below records that the five rows are
inconsistent on a nonzero singular projective jet, and computes the pure
`c7` residue needed to extract that fifth row from the Hahn packet.
-/

noncomputable section

/-- The fifth balanced `c7` equation eliminates the survivor left by the
first four invariant rows.  The certificate uses only rows one, two, four,
and the terminal row. -/
theorem GCD369Cube_c7Load_balanced_terminal_inconsistent
    {K : Type*} [Field K] [CharZero K]
    (A r d b q T : K) (hA : A ≠ 0) (hr : r ≠ 0)
    (h1 :
      -32 * (729 * (A ^ 2 * d - 2 * A * q - b ^ 2)) -
        532224 * r ^ 8 * T = 0)
    (h2 :
      32 * (-1458 * (2 * A ^ 2 * r * d - 3 * A * r * q +
        3 * r * b ^ 2)) + 1419264 * r ^ 9 * T = 0)
    (h4 :
      32 * (-13122 * A * r ^ 3 * q - 65610 * r ^ 3 * b ^ 2) -
        314928 * r * A ^ 3 - 17418240 * r ^ 11 * T = 0)
    (h5 :
      559872 * r ^ 4 * (-A ^ 2 * d + 21 * b ^ 2 + 6 * A * q) -
        2519424 * r ^ 2 * A ^ 3 + 178827264 * r ^ 12 * T = 0) :
    False := by
  have hzero : A ^ 3 * r ^ 2 = 0 := by
    linear_combination
      (-1 / 100602 * r ^ 4) * h1 +
      (1 / 268272 * r ^ 3) * h2 +
      (-11 / 7243344 * r) * h4 +
      (-1 / 4828896) * h5
  exact (mul_ne_zero (pow_ne_zero 3 hA) (pow_ne_zero 2 hr)) hzero

namespace GCD369CubeHahnCommonCoefficientData

/-- The coefficient of a pure `c7` load on the common-cubic sheet. -/
theorem terminalC7Coeff_cubicSheet
    {R : Type*} [CommRing R]
    (u v : R) :
    terminalC7Coeff (v ^ 2) (2 * u * v) (u ^ 2) (2 * v) (2 * u) =
      14336 * (2 * u ^ 6 - 90 * u ^ 3 * v ^ 2 + 81 * v ^ 4) := by
  simp only [terminalC7Coeff]
  ring

/-- On the singular double-root parametrization, the pure `c7` terminal
residue is the displayed nonzero scalar multiple of `r^12`. -/
theorem terminalC7Coeff_doubleRoot
    {R : Type*} [CommRing R]
    (r : R) :
    terminalC7Coeff
        ((2 * r ^ 3) ^ 2)
        (2 * (-3 * r ^ 2) * (2 * r ^ 3))
        ((-3 * r ^ 2) ^ 2) (2 * (2 * r ^ 3)) (2 * (-3 * r ^ 2)) =
      178827264 * r ^ 12 := by
  rw [terminalC7Coeff_cubicSheet]
  ring

/-- Equivalently, the complete fifth numerator with only `c7` active has
the exact singular-sheet residue used at the balanced load. -/
theorem fullN5_c7_doubleRootSheet
    {R : Type*} [CommRing R]
    (r c7 : R) :
    GCD369CubeFaberFullN5
        ((2 * r ^ 3) ^ 2)
        (2 * (-3 * r ^ 2) * (2 * r ^ 3))
        ((-3 * r ^ 2) ^ 2) (2 * (2 * r ^ 3)) (2 * (-3 * r ^ 2))
        0 c7 0 0 0 0 0 =
      c7 * (178827264 * r ^ 12) := by
  rw [fullN5_c7_specialize, terminalC7Coeff_doubleRoot]
  have hzero := GCD369CubeFaberFullN5_zeroHigh_expansion
    (R := R) 0 0 0 (-3 * r ^ 2) (2 * r ^ 3) 0
  norm_num at hzero
  have hzero' :
      GCD369CubeFaberFullN5
        ((2 * r ^ 3) ^ 2)
        (2 * (-3 * r ^ 2) * (2 * r ^ 3))
        ((-3 * r ^ 2) ^ 2) (2 * (2 * r ^ 3)) (2 * (-3 * r ^ 2))
        0 0 0 0 0 0 0 = 0 := by
    convert hzero using 1 <;> ring
  rw [hzero']
  ring

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubeHahnRegular

/-- At the first possible exponent of `y`, a regular multiplier contributes
only its residue.  This is the coefficient form of multiplicativity in the
associated graded ring of the regular Hahn local ring. -/
theorem coeff_mul_eq_constantCoeff_mul_of_order_lower
    {k : Type*} [Field k]
    (x y : GCD369CubeHahnRegular k) (e : ℚ) (he : 0 < e)
    (hy : (↑e : WithTop ℚ) ≤ y.1.orderTop) :
    (x * y).1.coeff e =
      GCD369CubeHahnRegular.constantCoeff x * y.1.coeff e := by
  let H : GCD369CubeHahnRegular k := monomial e he.le
  let ys : GCD369CubeHahnRegular k := shift y e hy
  have hyfact : H * ys = y := by
    simpa only [H, ys] using monomial_mul_shift y e he.le hy
  have hc := coeff_monomial_pow_mul_at e he 1 (x * ys)
  change (H ^ 1 * (x * ys)).1.coeff (1 * e) =
    constantCoeff (x * ys) at hc
  calc
    (x * y).1.coeff e = (H ^ 1 * (x * ys)).1.coeff (1 * e) := by
      rw [pow_one, one_mul]
      congr 1
      rw [← hyfact]
      ring
    _ = constantCoeff (x * ys) := hc
    _ = constantCoeff x * constantCoeff ys := by simp
    _ = constantCoeff x * y.1.coeff e := by
      rw [constantCoeff_shift]

end GCD369CubeHahnRegular

namespace GCD369CubeHahnCommonCoefficientData

/-- The fifth quadratic normal-row coefficient at a singular double root is
forced by the first two balanced coefficients. -/
theorem normalRow5Coeff_doubleRoot_of_row12
    {k : Type*} [Field k] [CharZero k]
    (X Y Z U V : GCD369CubeHahnRegular k)
    (delta : ℚ) (hdelta : 0 < delta)
    (A r d b q : k)
    (hU : GCD369CubeHahnRegular.constantCoeff U = -3 * r ^ 2)
    (hV : GCD369CubeHahnRegular.constantCoeff V = 2 * r ^ 3)
    (hord1 : (↑delta : WithTop ℚ) ≤
      (GCD369CubeNormalRow1 X Y Z U).1.orderTop)
    (hord2 : (↑delta : WithTop ℚ) ≤
      (GCD369CubeNormalRow2 X Y Z U V).1.orderTop)
    (hcoeff1 :
      (GCD369CubeNormalRow1 X Y Z U).1.coeff delta =
        729 * (A ^ 2 * d - 2 * A * q - b ^ 2))
    (hcoeff2 :
      (GCD369CubeNormalRow2 X Y Z U V).1.coeff delta =
        -1458 * (2 * A ^ 2 * r * d - 3 * A * r * q +
          3 * r * b ^ 2)) :
    (GCD369CubeNormalRow5 X Y Z U V).1.coeff delta =
      r ^ 4 * (-A ^ 2 * d + 21 * b ^ 2 + 6 * A * q) := by
  let R1 : GCD369CubeHahnRegular k := GCD369CubeNormalRow1 X Y Z U
  let R2 : GCD369CubeHahnRegular k := GCD369CubeNormalRow2 X Y Z U V
  let R5 : GCD369CubeHahnRegular k := GCD369CubeNormalRow5 X Y Z U V
  have hmul1 :=
    GCD369CubeHahnRegular.coeff_mul_eq_constantCoeff_mul_of_order_lower
      (U ^ 2) R1 delta hdelta (by simpa only [R1] using hord1)
  have hmul2 :=
    GCD369CubeHahnRegular.coeff_mul_eq_constantCoeff_mul_of_order_lower
      V R2 delta hdelta (by simpa only [R2] using hord2)
  have hid := GCD369CubeNormalRow5_of_row1_row2 X Y Z U V
  have hc := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff delta) hid
  change (U ^ 2 * R1).1.coeff delta + (V * R2).1.coeff delta +
      (729 * R5).1.coeff delta = 0 at hc
  have hnat : (729 * R5).1.coeff delta =
      (729 : k) * R5.1.coeff delta :=
    GCD369CubeHahnRegular.coeff_nat_mul 729 R5 delta
  rw [hmul1, hmul2, hnat] at hc
  simp only [map_pow, hU, hV, R1, R2, hcoeff1, hcoeff2] at hc
  change R5.1.coeff delta =
    r ^ 4 * (-A ^ 2 * d + 21 * b ^ 2 + 6 * A * q)
  linear_combination (1 / 729) * hc

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- At `2 p = 3 delta`, the coefficient of the pure `c7` specialization is
the fifth balanced row: its quadratic part is forced by rows one and two,
while the cubic intrinsic term and the `c7` residue meet at the same
exponent. -/
theorem TransverseScale.c7SpecializedTerminalCoeff_at_balanced
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C7 : k)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant C7)
    (r A d b q : k)
    (hu : D.u = -3 * r ^ 2) (hv : D.v = 2 * r ^ 3)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r * A)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r ^ 2 * A)
    (htie : 2 * D.faber.scale.p = 3 * T.delta)
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
      D.faber.scale.regular4 0
      (D.faber.scale.weightedRegular 2 D.faber.c7)
      0 0 0 0 0).1.coeff (2 * D.faber.scale.p) =
      559872 * r ^ 4 * (-A ^ 2 * d + 21 * b ^ 2 + 6 * A * q) -
        2519424 * r ^ 2 * A ^ 3 + 178827264 * r ^ 12 * C7 := by
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let R5 : GCD369CubeHahnRegular k :=
    GCD369CubeNormalRow5 T.Xn T.Yn T.Zn D.cubicU D.cubicV
  let C : GCD369CubeHahnRegular k :=
    GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU
  let P : GCD369CubeHahnRegular k := terminalC7Coeff
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
      178827264 * r ^ 12 := by
    dsimp only [P]
    simp only [terminalC7Coeff, map_add, map_sub, map_mul, map_pow,
      map_ofNat]
    change terminalC7Coeff
      D.faber.scale.leading0 D.faber.scale.leading1
      D.faber.scale.leading2 D.faber.scale.leading3
      D.faber.scale.leading4 = 178827264 * r ^ 12
    rw [D.ha0, D.ha1, D.ha2, D.ha3, D.ha4, hu, hv]
    exact terminalC7Coeff_doubleRoot r
  have hload : D.faber.scale.weightedRegular 2 D.faber.c7 =
      H ^ 3 * GCD369CubeHahnRegular.constant C7 := by
    rw [hc7, D.faber.scale.weightedRegular_constant_eq_monomial_sq
      2 (by norm_num) C7]
    apply Subtype.ext
    change
      (HahnSeries.single (((2 : ℕ) : ℚ) * D.faber.scale.p / 2)
          (1 : k)) ^ 2 * HahnSeries.C C7 =
        (HahnSeries.single T.delta (1 : k)) ^ 3 * HahnSeries.C C7
    simp only [HahnSeries.single_pow, nsmul_eq_mul, one_pow]
    convert congrArg
      (fun z : ℚ => HahnSeries.single z (1 : k) * HahnSeries.C C7)
      htie using 1 <;> norm_num
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
        D.faber.scale.regular4 0
        (D.faber.scale.weightedRegular 2 D.faber.c7)
        0 0 0 0 0 =
      (559872 * R5) * H ^ 2 +
        H ^ 3 * (839808 * C + GCD369CubeHahnRegular.constant C7 * P) := by
    rw [fullN5_c7_specialize, hload]
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
      (839808 * C + GCD369CubeHahnRegular.constant C7 * P)
  change (H ^ 3 *
      (839808 * C + GCD369CubeHahnRegular.constant C7 * P)).1.coeff
        (3 * T.delta) =
      GCD369CubeHahnRegular.constantCoeff
        (839808 * C + GCD369CubeHahnRegular.constant C7 * P) at htop
  change
    (GCD369CubeFaberFullN5
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4 0
      (D.faber.scale.weightedRegular 2 D.faber.c7)
      0 0 0 0 0).1.coeff (3 * T.delta) =
        ((559872 * R5) * H ^ 2).1.coeff (3 * T.delta) +
        (H ^ 3 *
          (839808 * C + GCD369CubeHahnRegular.constant C7 * P)).1.coeff
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

/-- Coefficient-data bridge for the complete fifth numerator.  Later loads
are strictly above `2 p`, so the balanced coefficient is exactly the pure
`c7` coefficient computed above. -/
theorem TransverseScale.fullN5Coeff_at_c7_balanced
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C7 C5 C4 C3 C2 C1 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant C7)
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
    (htie : 2 * D.faber.scale.p = 3 * T.delta)
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
        (2 * D.faber.scale.p) =
      559872 * r ^ 4 * (-A ^ 2 * d + 21 * b ^ 2 + 6 * A * q) -
        2519424 * r ^ 2 * A ^ 3 + 178827264 * r ^ 12 * C7 := by
  calc
    _ = (GCD369CubeFaberFullN5
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 0
        (D.faber.scale.weightedRegular 2 D.faber.c7)
        0 0 0 0 0).1.coeff (2 * D.faber.scale.p) :=
      D.faber.fullN5Coeff_eq_c7Specialized
        C5 C4 C3 C2 C1 hd hc5 hc4 hc3 hc2 hc1
    _ = _ := T.c7SpecializedTerminalCoeff_at_balanced
      C7 hc7 r A d b q hu hv hX hY hZ htie
      hord1 hord2 hcoeff1 hcoeff2

/-- Vanishing of the complete fifth coefficient gives the terminal equation
used by `GCD369Cube_c7Load_balanced_terminal_inconsistent`. -/
theorem TransverseScale.c7LoadedTerminalEquation_at_balanced
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C7 C5 C4 C3 C2 C1 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant C7)
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
    (htie : 2 * D.faber.scale.p = 3 * T.delta)
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
          (2 * D.faber.scale.p) = 0) :
    559872 * r ^ 4 * (-A ^ 2 * d + 21 * b ^ 2 + 6 * A * q) -
      2519424 * r ^ 2 * A ^ 3 + 178827264 * r ^ 12 * C7 = 0 := by
  rw [T.fullN5Coeff_at_c7_balanced
    C7 C5 C4 C3 C2 C1 hd hc7 hc5 hc4 hc3 hc2 hc1
    r A d b q hu hv hX hY hZ htie
    hord1 hord2 hcoeff1 hcoeff2] at hzero
  exact hzero

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubePolynomialSource

/-- Global singular-source wrapper for the balanced fifth equation.  Degree
integrality and the terminal invariant order supply the coefficient
vanishing hypothesis automatically. -/
theorem infinity_c7LoadedTerminalEquation_at_balanced
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (hdisc :
      4 * (S.infinityCommonCoefficientData hsdegree).u ^ 3 +
        27 * (S.infinityCommonCoefficientData hsdegree).v ^ 2 = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (C7 C5 C4 C3 C2 C1 : k)
    (hd : (S.infinityCommonCoefficientData hsdegree).faber.d =
      GCD369CubeHahnRegular.constant 0)
    (hc7 : (S.infinityCommonCoefficientData hsdegree).faber.c7 =
      GCD369CubeHahnRegular.constant C7)
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
    (htie : 2 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p =
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
      2519424 * r ^ 2 * A ^ 3 + 178827264 * r ^ 12 * C7 = 0 := by
  let D := S.infinityCommonCoefficientData hsdegree
  have hzero := S.infinity_fullN5Coeff_two_p_eq_zero_of_singular
    hsdegree hdisc
  exact T.c7LoadedTerminalEquation_at_balanced
    C7 C5 C4 C3 C2 C1 hd hc7 hc5 hc4 hc3 hc2 hc1
    r A d b q hu hv hX hY hZ htie
    hord1 hord2 hcoeff1 hcoeff2 (by simpa only [D] using hzero)

end GCD369CubePolynomialSource

#print axioms GCD369Cube_c7Load_balanced_terminal_inconsistent
#print axioms GCD369CubeHahnRegular.coeff_mul_eq_constantCoeff_mul_of_order_lower
#print axioms GCD369CubeHahnCommonCoefficientData.normalRow5Coeff_doubleRoot_of_row12
#print axioms GCD369CubeHahnCommonCoefficientData.TransverseScale.c7SpecializedTerminalCoeff_at_balanced
#print axioms GCD369CubeHahnCommonCoefficientData.TransverseScale.fullN5Coeff_at_c7_balanced
#print axioms GCD369CubeHahnCommonCoefficientData.TransverseScale.c7LoadedTerminalEquation_at_balanced
#print axioms GCD369CubePolynomialSource.infinity_c7LoadedTerminalEquation_at_balanced
#print axioms GCD369CubeHahnCommonCoefficientData.terminalC7Coeff_doubleRoot
#print axioms GCD369CubeHahnCommonCoefficientData.fullN5_c7_doubleRootSheet
