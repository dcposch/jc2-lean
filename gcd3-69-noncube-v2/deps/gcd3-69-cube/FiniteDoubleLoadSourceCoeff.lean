import FiniteSimpleSourceTiedCoeff
import FiniteDoubleLoad

/-! # Source-facing weight-one coefficients on the moving double-root sheet

Between the quadratic transverse scale `2 * delta` and the intrinsic cubic
scale `3 * delta`, the complete `d`-numerators at exponent `p` split as the
shifted double-root zero-high rows plus the pure weight-one load.  The
higher-order `H ^ 3` remainders, including the intrinsic `-64 * A ^ 3`
term in row three, vanish strictly before `3 * delta`.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- Leading residue of the first integral `d` polynomial on the common
cubic. -/
theorem dLoadPoly1_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      27648 * S.normal.sextic.scale.regular0 *
          S.normal.sextic.scale.regular3 +
        27648 * S.normal.sextic.scale.regular1 *
          S.normal.sextic.scale.regular2 -
        9216 * S.normal.sextic.scale.regular1 *
          S.normal.sextic.scale.regular4 ^ 2 -
        18432 * S.normal.sextic.scale.regular2 *
          S.normal.sextic.scale.regular3 * S.normal.sextic.scale.regular4 -
        3072 * S.normal.sextic.scale.regular3 ^ 3 +
        5120 * S.normal.sextic.scale.regular3 *
          S.normal.sextic.scale.regular4 ^ 3
    GCD369CubeHahnRegular.constantCoeff P =
      -10240 * S.u ^ 3 * S.v + 30720 * S.v ^ 3 := by
  dsimp only
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change
    27648 * S.normal.sextic.scale.leading0 *
        S.normal.sextic.scale.leading3 +
      27648 * S.normal.sextic.scale.leading1 *
        S.normal.sextic.scale.leading2 -
      9216 * S.normal.sextic.scale.leading1 *
        S.normal.sextic.scale.leading4 ^ 2 -
      18432 * S.normal.sextic.scale.leading2 *
        S.normal.sextic.scale.leading3 * S.normal.sextic.scale.leading4 -
      3072 * S.normal.sextic.scale.leading3 ^ 3 +
      5120 * S.normal.sextic.scale.leading3 *
        S.normal.sextic.scale.leading4 ^ 3 = _
  rw [S.ha0, S.ha1, S.ha2, S.ha3, S.ha4]
  ring

/-- Leading residue of the second integral `d` polynomial on the common
cubic. -/
theorem dLoadPoly2_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      82944 * S.normal.sextic.scale.regular0 *
          S.normal.sextic.scale.regular2 -
        27648 * S.normal.sextic.scale.regular0 *
          S.normal.sextic.scale.regular4 ^ 2 +
        41472 * S.normal.sextic.scale.regular1 ^ 2 -
        55296 * S.normal.sextic.scale.regular1 *
          S.normal.sextic.scale.regular3 * S.normal.sextic.scale.regular4 -
        27648 * S.normal.sextic.scale.regular2 ^ 2 *
          S.normal.sextic.scale.regular4 -
        27648 * S.normal.sextic.scale.regular2 *
          S.normal.sextic.scale.regular3 ^ 2 +
        15360 * S.normal.sextic.scale.regular2 *
          S.normal.sextic.scale.regular4 ^ 3 +
        23040 * S.normal.sextic.scale.regular3 ^ 2 *
          S.normal.sextic.scale.regular4 ^ 2 -
        2048 * S.normal.sextic.scale.regular4 ^ 5
    GCD369CubeHahnRegular.constantCoeff P =
      2048 * S.u ^ 5 - 46080 * S.u ^ 2 * S.v ^ 2 := by
  dsimp only
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change
    82944 * S.normal.sextic.scale.leading0 *
        S.normal.sextic.scale.leading2 -
      27648 * S.normal.sextic.scale.leading0 *
        S.normal.sextic.scale.leading4 ^ 2 +
      41472 * S.normal.sextic.scale.leading1 ^ 2 -
      55296 * S.normal.sextic.scale.leading1 *
        S.normal.sextic.scale.leading3 * S.normal.sextic.scale.leading4 -
      27648 * S.normal.sextic.scale.leading2 ^ 2 *
        S.normal.sextic.scale.leading4 -
      27648 * S.normal.sextic.scale.leading2 *
        S.normal.sextic.scale.leading3 ^ 2 +
      15360 * S.normal.sextic.scale.leading2 *
        S.normal.sextic.scale.leading4 ^ 3 +
      23040 * S.normal.sextic.scale.leading3 ^ 2 *
        S.normal.sextic.scale.leading4 ^ 2 -
      2048 * S.normal.sextic.scale.leading4 ^ 5 = _
  rw [S.ha0, S.ha1, S.ha2, S.ha3, S.ha4]
  ring

/-- The third integral `d` polynomial has vanishing residue on the common
cubic; every `d` term carries a normal coordinate. -/
theorem dLoadPoly3_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      110592 * S.normal.sextic.scale.regular0 *
          S.normal.sextic.scale.regular1 -
        55296 * S.normal.sextic.scale.regular0 *
          S.normal.sextic.scale.regular3 * S.normal.sextic.scale.regular4 -
        55296 * S.normal.sextic.scale.regular1 *
          S.normal.sextic.scale.regular2 * S.normal.sextic.scale.regular4 -
        36864 * S.normal.sextic.scale.regular1 *
          S.normal.sextic.scale.regular3 ^ 2 +
        14336 * S.normal.sextic.scale.regular1 *
          S.normal.sextic.scale.regular4 ^ 3 -
        36864 * S.normal.sextic.scale.regular2 ^ 2 *
          S.normal.sextic.scale.regular3 +
        49152 * S.normal.sextic.scale.regular2 *
          S.normal.sextic.scale.regular3 *
            S.normal.sextic.scale.regular4 ^ 2 +
        18432 * S.normal.sextic.scale.regular3 ^ 3 *
          S.normal.sextic.scale.regular4 -
        10240 * S.normal.sextic.scale.regular3 *
          S.normal.sextic.scale.regular4 ^ 4
    GCD369CubeHahnRegular.constantCoeff P = 0 := by
  dsimp only
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change
    110592 * S.normal.sextic.scale.leading0 *
        S.normal.sextic.scale.leading1 -
      55296 * S.normal.sextic.scale.leading0 *
        S.normal.sextic.scale.leading3 * S.normal.sextic.scale.leading4 -
      55296 * S.normal.sextic.scale.leading1 *
        S.normal.sextic.scale.leading2 * S.normal.sextic.scale.leading4 -
      36864 * S.normal.sextic.scale.leading1 *
        S.normal.sextic.scale.leading3 ^ 2 +
      14336 * S.normal.sextic.scale.leading1 *
        S.normal.sextic.scale.leading4 ^ 3 -
      36864 * S.normal.sextic.scale.leading2 ^ 2 *
        S.normal.sextic.scale.leading3 +
      49152 * S.normal.sextic.scale.leading2 *
        S.normal.sextic.scale.leading3 * S.normal.sextic.scale.leading4 ^ 2 +
      18432 * S.normal.sextic.scale.leading3 ^ 3 *
        S.normal.sextic.scale.leading4 -
      10240 * S.normal.sextic.scale.leading3 *
        S.normal.sextic.scale.leading4 ^ 4 = 0
  rw [S.ha0, S.ha1, S.ha2, S.ha3, S.ha4]
  ring

/-- Leading residue of the fourth integral `d` polynomial on the common
cubic. -/
theorem dLoadPoly4_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      373248 * S.normal.sextic.scale.regular0 ^ 2 -
        248832 * S.normal.sextic.scale.regular0 *
          S.normal.sextic.scale.regular2 * S.normal.sextic.scale.regular4 -
        124416 * S.normal.sextic.scale.regular0 *
          S.normal.sextic.scale.regular3 ^ 2 +
        55296 * S.normal.sextic.scale.regular0 *
          S.normal.sextic.scale.regular4 ^ 3 -
        124416 * S.normal.sextic.scale.regular1 ^ 2 *
          S.normal.sextic.scale.regular4 -
        373248 * S.normal.sextic.scale.regular1 *
          S.normal.sextic.scale.regular2 * S.normal.sextic.scale.regular3 +
        207360 * S.normal.sextic.scale.regular1 *
          S.normal.sextic.scale.regular3 *
            S.normal.sextic.scale.regular4 ^ 2 -
        82944 * S.normal.sextic.scale.regular2 ^ 3 +
        124416 * S.normal.sextic.scale.regular2 ^ 2 *
          S.normal.sextic.scale.regular4 ^ 2 +
        248832 * S.normal.sextic.scale.regular2 *
          S.normal.sextic.scale.regular3 ^ 2 *
            S.normal.sextic.scale.regular4 -
        46080 * S.normal.sextic.scale.regular2 *
          S.normal.sextic.scale.regular4 ^ 4 +
        20736 * S.normal.sextic.scale.regular3 ^ 4 -
        92160 * S.normal.sextic.scale.regular3 ^ 2 *
          S.normal.sextic.scale.regular4 ^ 3 +
        5120 * S.normal.sextic.scale.regular4 ^ 6
    GCD369CubeHahnRegular.constantCoeff P =
      5120 * S.u ^ 6 - 184320 * S.u ^ 3 * S.v ^ 2 +
        207360 * S.v ^ 4 := by
  dsimp only
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change
    373248 * S.normal.sextic.scale.leading0 ^ 2 -
      248832 * S.normal.sextic.scale.leading0 *
        S.normal.sextic.scale.leading2 * S.normal.sextic.scale.leading4 -
      124416 * S.normal.sextic.scale.leading0 *
        S.normal.sextic.scale.leading3 ^ 2 +
      55296 * S.normal.sextic.scale.leading0 *
        S.normal.sextic.scale.leading4 ^ 3 -
      124416 * S.normal.sextic.scale.leading1 ^ 2 *
        S.normal.sextic.scale.leading4 -
      373248 * S.normal.sextic.scale.leading1 *
        S.normal.sextic.scale.leading2 * S.normal.sextic.scale.leading3 +
      207360 * S.normal.sextic.scale.leading1 *
        S.normal.sextic.scale.leading3 * S.normal.sextic.scale.leading4 ^ 2 -
      82944 * S.normal.sextic.scale.leading2 ^ 3 +
      124416 * S.normal.sextic.scale.leading2 ^ 2 *
        S.normal.sextic.scale.leading4 ^ 2 +
      248832 * S.normal.sextic.scale.leading2 *
        S.normal.sextic.scale.leading3 ^ 2 * S.normal.sextic.scale.leading4 -
      46080 * S.normal.sextic.scale.leading2 *
        S.normal.sextic.scale.leading4 ^ 4 +
      20736 * S.normal.sextic.scale.leading3 ^ 4 -
      92160 * S.normal.sextic.scale.leading3 ^ 2 *
        S.normal.sextic.scale.leading4 ^ 3 +
      5120 * S.normal.sextic.scale.leading4 ^ 6 = _
  rw [S.ha0, S.ha1, S.ha2, S.ha3, S.ha4]
  ring

/-- Coefficients of a sum in the regular Hahn local ring. -/
theorem coeff_add
    {k : Type*} [Field k] (x y : GCD369CubeHahnRegular k) (e : ℚ) :
    (x + y).1.coeff e = x.1.coeff e + y.1.coeff e :=
  HahnSeries.coeff_add

/-- Coefficients of a difference in the regular Hahn local ring. -/
theorem coeff_sub
    {k : Type*} [Field k] (x y : GCD369CubeHahnRegular k) (e : ℚ) :
    (x - y).1.coeff e = x.1.coeff e - y.1.coeff e :=
  HahnSeries.coeff_sub

/-- In the strict middle window `2 * delta < p < 3 * delta`, the four
literal `d`-numerators at exponent `p` are the shifted double-root
zero-high rows plus the pure weight-one load
`D0 * (798720 * r0 ^ 9, -2156544 * r0 ^ 10, 0, 26956800 * r0 ^ 12)`.
The intrinsic cubic remainders, including `-64 * A ^ 3 * H ^ 3` in row
three, do not meet this exponent. -/
theorem TransverseFactor.doubleRoot_dLoad_source_coeff_of_lt
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant D0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hrho1 : F.rho1 = GCD369CubeHahnRegular.constant Rho1)
    (hrho2 : F.rho2 = GCD369CubeHahnRegular.constant Rho2)
    (hrho3 : F.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : F.rho4 = GCD369CubeHahnRegular.constant Rho4)
    (r : GCD369CubeHahnRegular k)
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0)
    (hu : S.u = -3 * GCD369CubeHahnRegular.constantCoeff r ^ 2)
    (hv : S.v = 2 * GCD369CubeHahnRegular.constantCoeff r ^ 3)
    (hpLT : 2 * T.delta < F.scale.p)
    (hpGT : F.scale.p < 3 * T.delta) :
    let A := T.Xn
    let D := S.cubicU + 3 * r ^ 2
    let B := T.Yn - r * A
    let C := T.Zn + 2 * r ^ 2 * A
    let R1 := A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C
    let R2 :=
      2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
        3 * A * B * D - 3 * B * C
    let R3 :=
      -2 * A ^ 2 * r ^ 2 * D + 6 * B ^ 2 * r ^ 2 +
        2 * A ^ 2 * D ^ 2 - 2 * B ^ 2 * D - 4 * A * C * D + 3 * C ^ 2
    let R4 :=
      4374 * (-3 * r ^ 2 + D) *
        (A * B * r ^ 2 + 2 * B ^ 2 * r + A * C * r +
          3 * A * B * D - 3 * B * C)
    let lambda := F.scale.p - 2 * T.delta
    let r0 := GCD369CubeHahnRegular.constantCoeff r
    ((-32 * (729 * R1)).1.coeff lambda +
        D0 * (798720 * r0 ^ 9) = 0) ∧
    ((32 * (-1458 * R2)).1.coeff lambda +
        D0 * (-2156544 * r0 ^ 10) = 0) ∧
    ((128 * R3).1.coeff lambda = 0) ∧
    ((32 * R4).1.coeff lambda +
        D0 * (26956800 * r0 ^ 12) = 0) := by
  dsimp only
  let A : GCD369CubeHahnRegular k := T.Xn
  let D : GCD369CubeHahnRegular k := S.cubicU + 3 * r ^ 2
  let B : GCD369CubeHahnRegular k := T.Yn - r * A
  let C : GCD369CubeHahnRegular k := T.Zn + 2 * r ^ 2 * A
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let R1 : GCD369CubeHahnRegular k :=
    A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C
  let R2 : GCD369CubeHahnRegular k :=
    2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
      3 * A * B * D - 3 * B * C
  let R3 : GCD369CubeHahnRegular k :=
    -2 * A ^ 2 * r ^ 2 * D + 6 * B ^ 2 * r ^ 2 +
      2 * A ^ 2 * D ^ 2 - 2 * B ^ 2 * D - 4 * A * C * D + 3 * C ^ 2
  let R4 : GCD369CubeHahnRegular k :=
    4374 * (-3 * r ^ 2 + D) *
      (A * B * r ^ 2 + 2 * B ^ 2 * r + A * C * r +
        3 * A * B * D - 3 * B * C)
  let lambda : ℚ := F.scale.p - 2 * T.delta
  let r0 : k := GCD369CubeHahnRegular.constantCoeff r
  let N1 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberN1
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
  let N2 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberN2
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
  let N3 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberN3
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
  let N4 : GCD369CubeHahnRegular k :=
    GCD369CubeFaberN4
      S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
      S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
      S.normal.sextic.scale.regular4
  let P1 : GCD369CubeHahnRegular k :=
    27648 * S.normal.sextic.scale.regular0 *
        S.normal.sextic.scale.regular3 +
      27648 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular2 -
      9216 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular4 ^ 2 -
      18432 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular3 * S.normal.sextic.scale.regular4 -
      3072 * S.normal.sextic.scale.regular3 ^ 3 +
      5120 * S.normal.sextic.scale.regular3 *
        S.normal.sextic.scale.regular4 ^ 3
  let P2 : GCD369CubeHahnRegular k :=
    82944 * S.normal.sextic.scale.regular0 *
        S.normal.sextic.scale.regular2 -
      27648 * S.normal.sextic.scale.regular0 *
        S.normal.sextic.scale.regular4 ^ 2 +
      41472 * S.normal.sextic.scale.regular1 ^ 2 -
      55296 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular3 * S.normal.sextic.scale.regular4 -
      27648 * S.normal.sextic.scale.regular2 ^ 2 *
        S.normal.sextic.scale.regular4 -
      27648 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular3 ^ 2 +
      15360 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular4 ^ 3 +
      23040 * S.normal.sextic.scale.regular3 ^ 2 *
        S.normal.sextic.scale.regular4 ^ 2 -
      2048 * S.normal.sextic.scale.regular4 ^ 5
  let P3 : GCD369CubeHahnRegular k :=
    110592 * S.normal.sextic.scale.regular0 *
        S.normal.sextic.scale.regular1 -
      55296 * S.normal.sextic.scale.regular0 *
        S.normal.sextic.scale.regular3 * S.normal.sextic.scale.regular4 -
      55296 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular2 * S.normal.sextic.scale.regular4 -
      36864 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular3 ^ 2 +
      14336 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular4 ^ 3 -
      36864 * S.normal.sextic.scale.regular2 ^ 2 *
        S.normal.sextic.scale.regular3 +
      49152 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular3 *
          S.normal.sextic.scale.regular4 ^ 2 +
      18432 * S.normal.sextic.scale.regular3 ^ 3 *
        S.normal.sextic.scale.regular4 -
      10240 * S.normal.sextic.scale.regular3 *
        S.normal.sextic.scale.regular4 ^ 4
  let P4 : GCD369CubeHahnRegular k :=
    373248 * S.normal.sextic.scale.regular0 ^ 2 -
      248832 * S.normal.sextic.scale.regular0 *
        S.normal.sextic.scale.regular2 * S.normal.sextic.scale.regular4 -
      124416 * S.normal.sextic.scale.regular0 *
        S.normal.sextic.scale.regular3 ^ 2 +
      55296 * S.normal.sextic.scale.regular0 *
        S.normal.sextic.scale.regular4 ^ 3 -
      124416 * S.normal.sextic.scale.regular1 ^ 2 *
        S.normal.sextic.scale.regular4 -
      373248 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular2 * S.normal.sextic.scale.regular3 +
      207360 * S.normal.sextic.scale.regular1 *
        S.normal.sextic.scale.regular3 *
          S.normal.sextic.scale.regular4 ^ 2 -
      82944 * S.normal.sextic.scale.regular2 ^ 3 +
      124416 * S.normal.sextic.scale.regular2 ^ 2 *
        S.normal.sextic.scale.regular4 ^ 2 +
      248832 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular3 ^ 2 *
          S.normal.sextic.scale.regular4 -
      46080 * S.normal.sextic.scale.regular2 *
        S.normal.sextic.scale.regular4 ^ 4 +
      20736 * S.normal.sextic.scale.regular3 ^ 4 -
      92160 * S.normal.sextic.scale.regular3 ^ 2 *
        S.normal.sextic.scale.regular4 ^ 3 +
      5120 * S.normal.sextic.scale.regular4 ^ 6
  let d1 : GCD369CubeHahnRegular k :=
    S.normal.sextic.scale.weightedRegular 1
      (GCD369CubeHahnRegular.constant D0)
  have hpS : S.normal.sextic.scale.p = F.scale.p := by rw [hscale]
  have hlambda : F.scale.p = lambda + (2 : ℚ) * T.delta := by
    dsimp only [lambda]
    ring
  have hlambda_pos : 0 < lambda := by
    dsimp only [lambda]
    linarith [hpLT]
  have hexp := T.doubleRoot_zeroHigh_expansions r hroot
  have hexp1 : 729 * N1 = (-32 * (729 * R1)) * H ^ 2 := by
    simpa only [N1, R1, A, D, B, C, H] using hexp.1
  have hexp2 : 2187 * N2 = (32 * (-1458 * R2)) * H ^ 2 := by
    simpa only [N2, R2, A, D, B, C, H] using hexp.2.1
  have hexp3 : N3 = (128 * R3) * H ^ 2 - (64 * A ^ 3) * H ^ 3 := by
    simpa only [N3, R3, A, D, B, C, H] using hexp.2.2.1
  have hexp4 :
      6561 * N4 =
        (32 * R4) * H ^ 2 -
          (314928 * (r * A + B) * A ^ 2) * H ^ 3 := by
    simpa only [N4, R4, A, D, B, C, H] using hexp.2.2.2
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
    (64 * A ^ 3) T.delta (F.scale.p - 3 * T.delta) T.hdelta.le 3
  have hcubic4 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (314928 * (r * A + B) * A ^ 2) T.delta
    (F.scale.p - 3 * T.delta) T.hdelta.le 3
  change ((64 * A ^ 3) * H ^ 3).1.coeff
      ((F.scale.p - 3 * T.delta) + (3 : ℚ) * T.delta) =
        (64 * A ^ 3).1.coeff (F.scale.p - 3 * T.delta) at hcubic3
  change ((314928 * (r * A + B) * A ^ 2) * H ^ 3).1.coeff
      ((F.scale.p - 3 * T.delta) + (3 : ℚ) * T.delta) =
        (314928 * (r * A + B) * A ^ 2).1.coeff
          (F.scale.p - 3 * T.delta) at hcubic4
  have hneg : F.scale.p - 3 * T.delta < 0 := by linarith [hpGT]
  have hcubic3zero : ((64 * A ^ 3) * H ^ 3).1.coeff F.scale.p = 0 := by
    have hrew : (F.scale.p - 3 * T.delta) + (3 : ℚ) * T.delta =
        F.scale.p := by ring
    rw [← hrew, hcubic3]
    exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg _ hneg
  have hcubic4zero :
      ((314928 * (r * A + B) * A ^ 2) * H ^ 3).1.coeff F.scale.p = 0 := by
    have hrew : (F.scale.p - 3 * T.delta) + (3 : ℚ) * T.delta =
        F.scale.p := by ring
    rw [← hrew, hcubic4]
    exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg _ hneg
  have hload1 :
      GCD369CubeHahnRegular.constantCoeff P1 = 798720 * r0 ^ 9 := by
    have hP := S.dLoadPoly1_constantCoeff
    simpa only [P1] using
      (hP.trans (by
        rw [hu, hv]
        exact (GCD369Cube_dLoadRemainders_doubleRoot r0).1))
  have hload2 :
      GCD369CubeHahnRegular.constantCoeff P2 =
        -2156544 * r0 ^ 10 := by
    have hP := S.dLoadPoly2_constantCoeff
    simpa only [P2] using
      (hP.trans (by
        rw [hu, hv]
        exact (GCD369Cube_dLoadRemainders_doubleRoot r0).2.1))
  have hload3 : GCD369CubeHahnRegular.constantCoeff P3 = 0 := by
    simpa only [P3] using S.dLoadPoly3_constantCoeff
  have hload4 :
      GCD369CubeHahnRegular.constantCoeff P4 =
        26956800 * r0 ^ 12 := by
    have hP := S.dLoadPoly4_constantCoeff
    simpa only [P4] using
      (hP.trans (by
        rw [hu, hv]
        exact (GCD369Cube_dLoadRemainders_doubleRoot r0).2.2))
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hz := F.dN1Coeff_zero C7 C5 C4 C3 C2 C1 Rho1
      hc7 hc5 hc4 hc3 hc2 hc1 hrho1
    rw [hd, ← hscale] at hz
    have hform :
        GCD369CubeFaberD1
            S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
            S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
            S.normal.sextic.scale.regular4 d1 =
          729 * N1 + d1 * P1 := rfl
    rw [hform, coeff_add,
      S.normal.sextic.scale.weightedRegular_one_constant_mul_coeff D0 P1,
      hload1, hpS] at hz
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff F.scale.p) hexp1
    rw [hlambda, hshift1] at hc
    calc
      (-32 * (729 * R1)).1.coeff lambda + D0 * (798720 * r0 ^ 9) =
          (729 * N1).1.coeff F.scale.p + D0 * (798720 * r0 ^ 9) := by
        rw [← hc, hlambda]
      _ = 0 := hz
  · have hz := F.dN2Coeff_zero C7 C5 C4 C3 C2 C1 Rho2
      hc7 hc5 hc4 hc3 hc2 hc1 hrho2
    rw [hd, ← hscale] at hz
    have hform :
        GCD369CubeFaberD2
            S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
            S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
            S.normal.sextic.scale.regular4 d1 =
          2187 * N2 + d1 * P2 := rfl
    rw [hform, coeff_add,
      S.normal.sextic.scale.weightedRegular_one_constant_mul_coeff D0 P2,
      hload2, hpS] at hz
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff F.scale.p) hexp2
    rw [hlambda, hshift2] at hc
    calc
      (32 * (-1458 * R2)).1.coeff lambda + D0 * (-2156544 * r0 ^ 10) =
          (2187 * N2).1.coeff F.scale.p + D0 * (-2156544 * r0 ^ 10) := by
        rw [← hc, hlambda]
      _ = 0 := hz
  · have hz := F.dN3Coeff_zero C7 C5 C4 C3 C2 C1 Rho3
      hc7 hc5 hc4 hc3 hc2 hc1 hrho3
    rw [hd, ← hscale] at hz
    have hform :
        GCD369CubeFaberD3
            S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
            S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
            S.normal.sextic.scale.regular4 d1 =
          243 * N3 + d1 * P3 := rfl
    rw [hform, coeff_add,
      S.normal.sextic.scale.weightedRegular_one_constant_mul_coeff D0 P3,
      hload3, mul_zero, add_zero, hpS] at hz
    have h243 : (243 * N3).1.coeff F.scale.p =
        (243 : k) * N3.1.coeff F.scale.p :=
      GCD369CubeHahnRegular.coeff_nat_mul 243 N3 F.scale.p
    have hzN : N3.1.coeff F.scale.p = 0 :=
      (mul_eq_zero.mp (h243.symm.trans hz)).resolve_left (by norm_num)
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff F.scale.p) hexp3
    change N3.1.coeff F.scale.p =
        ((128 * R3) * H ^ 2).1.coeff F.scale.p -
          ((64 * A ^ 3) * H ^ 3).1.coeff F.scale.p at hc
    rw [hcubic3zero, sub_zero, hlambda, hshift3] at hc
    rw [hlambda] at hzN
    exact hc.symm.trans hzN
  · have hz := F.dN4Coeff_zero C7 C5 C4 C3 C2 C1 Rho4
      hc7 hc5 hc4 hc3 hc2 hc1 hrho4
    rw [hd, ← hscale] at hz
    have hform :
        GCD369CubeFaberD4
            S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
            S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
            S.normal.sextic.scale.regular4 d1 =
          6561 * N4 + d1 * P4 := rfl
    rw [hform, coeff_add,
      S.normal.sextic.scale.weightedRegular_one_constant_mul_coeff D0 P4,
      hload4, hpS] at hz
    have hc := congrArg
      (fun z : GCD369CubeHahnRegular k => z.1.coeff F.scale.p) hexp4
    change (6561 * N4).1.coeff F.scale.p =
        ((32 * R4) * H ^ 2).1.coeff F.scale.p -
          ((314928 * (r * A + B) * A ^ 2) * H ^ 3).1.coeff F.scale.p at hc
    rw [hcubic4zero, sub_zero, hlambda, hshift4] at hc
    calc
      (32 * R4).1.coeff lambda + D0 * (26956800 * r0 ^ 12) =
          (6561 * N4).1.coeff F.scale.p + D0 * (26956800 * r0 ^ 12) := by
        rw [← hc, hlambda]
      _ = 0 := hz

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnCommonValueData.dLoadPoly1_constantCoeff
#print axioms GCD369CubeHahnCommonValueData.dLoadPoly2_constantCoeff
#print axioms GCD369CubeHahnCommonValueData.dLoadPoly3_constantCoeff
#print axioms GCD369CubeHahnCommonValueData.dLoadPoly4_constantCoeff
#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_dLoad_source_coeff_of_lt
