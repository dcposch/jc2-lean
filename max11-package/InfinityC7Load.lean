import InfinityDBalanced
import FiniteC7Extraction

/-! # The first weight-two load at infinity

This file starts the post-`d` fan for the constant-core infinity packet.  At
the exact tie between the weight-two `c7` load and the first transverse
normal, the four source coefficients are the arbitrary-`c7` Kuranishi rows.
The result is boundary-free and therefore applies directly to the lightweight
infinity coefficient packet.
-/

noncomputable section

namespace GCD369CubeHahnCommonCoefficientData

/-- Coefficient of the pure `c7` load in the denominator-cleared terminal
numerator. -/
def terminalC7Coeff {R : Type*} [CommRing R]
    (a0 a1 a2 a3 a4 : R) : R :=
  1306368 * a0 ^ 2 - 435456 * a0 * a2 * a4 -
    217728 * a0 * a3 ^ 2 + 84672 * a0 * a4 ^ 3 -
    435456 * a1 ^ 2 * a4 - 870912 * a1 * a2 * a3 +
    508032 * a1 * a3 * a4 ^ 2 - 145152 * a2 ^ 3 +
    254016 * a2 ^ 2 * a4 ^ 2 + 544320 * a2 * a3 ^ 2 * a4 -
    95760 * a2 * a4 ^ 4 + 45360 * a3 ^ 4 -
    206640 * a3 ^ 2 * a4 ^ 3 + 10780 * a4 ^ 6

/-- Isolate the pure `c7` contribution to the terminal numerator. -/
theorem fullN5_c7_specialize
    {R : Type*} [CommRing R]
    (a0 a1 a2 a3 a4 c7 : R) :
    GCD369CubeFaberFullN5 a0 a1 a2 a3 a4 0 c7 0 0 0 0 0 =
      GCD369CubeFaberFullN5 a0 a1 a2 a3 a4 0 0 0 0 0 0 0 +
        c7 * terminalC7Coeff a0 a1 a2 a3 a4 := by
  simp only [terminalC7Coeff]
  ring

theorem TransverseScale.c7N1Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C7 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC7N1
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C7)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -32 * (56 * C7 * D.u ^ 4 - 1008 * C7 * D.u * D.v ^ 2 +
        GCD369CubeNormalRow1
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    12096 * D.faber.scale.regular0 * D.faber.scale.regular4 +
      12096 * D.faber.scale.regular1 * D.faber.scale.regular3 +
      6048 * D.faber.scale.regular2 ^ 2 -
      5040 * D.faber.scale.regular2 * D.faber.scale.regular4 ^ 2 -
      5040 * D.faber.scale.regular3 ^ 2 * D.faber.scale.regular4 +
      770 * D.faber.scale.regular4 ^ 4
  change
    (729 * GCD369CubeFaberN1
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C7 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN1Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C7 P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change _ + C7 *
    (12096 * D.faber.scale.leading0 * D.faber.scale.leading4 +
      12096 * D.faber.scale.leading1 * D.faber.scale.leading3 +
      6048 * D.faber.scale.leading2 ^ 2 -
      5040 * D.faber.scale.leading2 * D.faber.scale.leading4 ^ 2 -
      5040 * D.faber.scale.leading3 ^ 2 * D.faber.scale.leading4 +
      770 * D.faber.scale.leading4 ^ 4) = _
  rw [D.ha0, D.ha1, D.ha2, D.ha3, D.ha4]
  ring

theorem TransverseScale.c7N2Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C7 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC7N2
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C7)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -96 * (224 * C7 * D.u ^ 3 * D.v - 336 * C7 * D.v ^ 3 +
        729 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
        1458 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) -
        1458 * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    36288 * D.faber.scale.regular0 * D.faber.scale.regular3 +
      36288 * D.faber.scale.regular1 * D.faber.scale.regular2 -
      15120 * D.faber.scale.regular1 * D.faber.scale.regular4 ^ 2 -
      30240 * D.faber.scale.regular2 * D.faber.scale.regular3 *
        D.faber.scale.regular4 -
      5040 * D.faber.scale.regular3 ^ 3 +
      9240 * D.faber.scale.regular3 * D.faber.scale.regular4 ^ 3
  change
    (2187 * GCD369CubeFaberN2
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C7 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN2Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C7 P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change _ + C7 *
    (36288 * D.faber.scale.leading0 * D.faber.scale.leading3 +
      36288 * D.faber.scale.leading1 * D.faber.scale.leading2 -
      15120 * D.faber.scale.leading1 * D.faber.scale.leading4 ^ 2 -
      30240 * D.faber.scale.leading2 * D.faber.scale.leading3 *
        D.faber.scale.leading4 -
      5040 * D.faber.scale.leading3 ^ 3 +
      9240 * D.faber.scale.leading3 * D.faber.scale.leading4 ^ 3) = _
  rw [D.ha0, D.ha1, D.ha2, D.ha3, D.ha4]
  dsimp only [GCD369CubeNormalRow2]
  ring

theorem TransverseScale.c7N3Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C7 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC7N3
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C7)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      31104 * GCD369CubeNormalRow3
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    48384 * D.faber.scale.regular0 * D.faber.scale.regular2 -
      12096 * D.faber.scale.regular0 * D.faber.scale.regular4 ^ 2 +
      24192 * D.faber.scale.regular1 ^ 2 -
      32256 * D.faber.scale.regular1 * D.faber.scale.regular3 *
        D.faber.scale.regular4 -
      16128 * D.faber.scale.regular2 ^ 2 * D.faber.scale.regular4 -
      20160 * D.faber.scale.regular2 * D.faber.scale.regular3 ^ 2 +
      8960 * D.faber.scale.regular2 * D.faber.scale.regular4 ^ 3 +
      15120 * D.faber.scale.regular3 ^ 2 * D.faber.scale.regular4 ^ 2 -
      1232 * D.faber.scale.regular4 ^ 5
  have hzero :
      (243 * GCD369CubeFaberN3
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4).1.coeff (((2 : ℕ) : ℚ) * T.delta) =
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
      D.faber.scale.regular4).1.coeff (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C7 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [hzero,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C7 P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change _ + C7 *
    (48384 * D.faber.scale.leading0 * D.faber.scale.leading2 -
      12096 * D.faber.scale.leading0 * D.faber.scale.leading4 ^ 2 +
      24192 * D.faber.scale.leading1 ^ 2 -
      32256 * D.faber.scale.leading1 * D.faber.scale.leading3 *
        D.faber.scale.leading4 -
      16128 * D.faber.scale.leading2 ^ 2 * D.faber.scale.leading4 -
      20160 * D.faber.scale.leading2 * D.faber.scale.leading3 ^ 2 +
      8960 * D.faber.scale.leading2 * D.faber.scale.leading4 ^ 3 +
      15120 * D.faber.scale.leading3 ^ 2 * D.faber.scale.leading4 ^ 2 -
      1232 * D.faber.scale.leading4 ^ 5) = _
  rw [D.ha0, D.ha1, D.ha2, D.ha3, D.ha4]
  ring

theorem TransverseScale.c7N4Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C7 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC7N4
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C7)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -288 * (224 * C7 * D.u ^ 4 * D.v - 1008 * C7 * D.u * D.v ^ 3 -
        2187 * D.u * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
        1458 * D.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) +
        2916 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) +
        1458 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 +
        1458 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    326592 * D.faber.scale.regular0 * D.faber.scale.regular1 -
      108864 * D.faber.scale.regular0 * D.faber.scale.regular3 *
        D.faber.scale.regular4 -
      163296 * D.faber.scale.regular1 * D.faber.scale.regular2 *
        D.faber.scale.regular4 -
      81648 * D.faber.scale.regular1 * D.faber.scale.regular3 ^ 2 +
      37800 * D.faber.scale.regular1 * D.faber.scale.regular4 ^ 3 -
      108864 * D.faber.scale.regular2 ^ 2 * D.faber.scale.regular3 +
      136080 * D.faber.scale.regular2 * D.faber.scale.regular3 *
        D.faber.scale.regular4 ^ 2 +
      45360 * D.faber.scale.regular3 ^ 3 * D.faber.scale.regular4 -
      27720 * D.faber.scale.regular3 * D.faber.scale.regular4 ^ 4
  change
    (6561 * GCD369CubeFaberN4
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C7 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN4Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C7 P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change _ + C7 *
    (326592 * D.faber.scale.leading0 * D.faber.scale.leading1 -
      108864 * D.faber.scale.leading0 * D.faber.scale.leading3 *
        D.faber.scale.leading4 -
      163296 * D.faber.scale.leading1 * D.faber.scale.leading2 *
        D.faber.scale.leading4 -
      81648 * D.faber.scale.leading1 * D.faber.scale.leading3 ^ 2 +
      37800 * D.faber.scale.leading1 * D.faber.scale.leading4 ^ 3 -
      108864 * D.faber.scale.leading2 ^ 2 * D.faber.scale.leading3 +
      136080 * D.faber.scale.leading2 * D.faber.scale.leading3 *
        D.faber.scale.leading4 ^ 2 +
      45360 * D.faber.scale.leading3 ^ 3 * D.faber.scale.leading4 -
      27720 * D.faber.scale.leading3 * D.faber.scale.leading4 ^ 4) = _
  rw [D.ha0, D.ha1, D.ha2, D.ha3, D.ha4]
  dsimp only [GCD369CubeNormalRow4]
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- At the exact `c7`/transverse tie, the pure-`c7` terminal numerator has
coefficient `256` times the unnormalized terminal polynomial. -/
theorem TransverseScale.c7SpecializedTerminalCoeff_at_transverse
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C7 : k)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant C7)
    (htie : D.faber.scale.p = T.delta) :
    (GCD369CubeFaberFullN5
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4 0
      (D.faber.scale.weightedRegular 2 D.faber.c7)
      0 0 0 0 0).1.coeff (2 * D.faber.scale.p) =
      256 *
        (112 * C7 * D.u ^ 6 - 5040 * C7 * D.u ^ 3 * D.v ^ 2 +
          4536 * C7 * D.v ^ 4 -
          2187 * D.u ^ 3 *
            (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
          6561 * D.v ^ 2 *
            (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
          13122 * D.u * D.v *
            (GCD369CubeHahnRegular.constantCoeff T.Xn) *
            (GCD369CubeHahnRegular.constantCoeff T.Yn) +
          4374 * D.u ^ 2 *
            (GCD369CubeHahnRegular.constantCoeff T.Xn) *
            (GCD369CubeHahnRegular.constantCoeff T.Zn) +
          2187 * D.u ^ 2 *
            (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 -
          13122 * D.v *
            (GCD369CubeHahnRegular.constantCoeff T.Yn) *
            (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let P : GCD369CubeHahnRegular k := terminalC7Coeff
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4
  let K : GCD369CubeHahnRegular k :=
    559872 * GCD369CubeNormalRow5
      T.Xn T.Yn T.Zn D.cubicU D.cubicV +
      GCD369CubeHahnRegular.constant C7 * P
  let E : GCD369CubeHahnRegular k :=
    839808 * GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU
  have hload : D.faber.scale.weightedRegular 2 D.faber.c7 =
      H ^ 2 * GCD369CubeHahnRegular.constant C7 := by
    rw [hc7, D.faber.scale.weightedRegular_constant_eq_monomial_sq
      2 (by norm_num) C7]
    apply Subtype.ext
    change
      (HahnSeries.single (((2 : ℕ) : ℚ) * D.faber.scale.p / 2) (1 : k)) ^ 2 *
          HahnSeries.C C7 =
        (HahnSeries.single T.delta (1 : k)) ^ 2 * HahnSeries.C C7
    rw [htie]
    congr 4 <;> ring
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
        0 0 0 0 0 = H ^ 2 * K + H ^ 3 * E := by
    rw [fullN5_c7_specialize, hload]
    rw [hchart0, hchart1, hchart2,
      D.regular3_eq_two_cubicV, D.regular4_eq_two_cubicU]
    rw [hzero]
    dsimp only [K, E]
    rw [← hchart0, ← hchart1, ← hchart2,
      ← D.regular3_eq_two_cubicV, ← D.regular4_eq_two_cubicU]
    ring
  have hc := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * T.delta)) hfactor
  have hmain := GCD369CubeHahnRegular.coeff_monomial_pow_mul_at
    T.delta T.hdelta 2 K
  have hhigh := GCD369CubeHahnRegular.coeff_monomial_pow_mul_of_lt
    T.delta T.hdelta 2 3 (by norm_num) E
  change (H ^ 2 * K).1.coeff (2 * T.delta) =
    GCD369CubeHahnRegular.constantCoeff K at hmain
  change (H ^ 3 * E).1.coeff (2 * T.delta) = 0 at hhigh
  change
    (GCD369CubeFaberFullN5
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4 0
      (D.faber.scale.weightedRegular 2 D.faber.c7)
      0 0 0 0 0).1.coeff (2 * T.delta) =
      (H ^ 2 * K).1.coeff (2 * T.delta) +
        (H ^ 3 * E).1.coeff (2 * T.delta) at hc
  rw [hmain, hhigh, add_zero] at hc
  rw [htie]
  rw [hc]
  dsimp only [K, P, terminalC7Coeff]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat,
    GCD369CubeNormalRow5_map, D.constantCoeff_cubicU,
    D.constantCoeff_cubicV,
    GCD369CubeHahnRegular.constantCoeff_constant]
  have ha0 : GCD369CubeHahnRegular.constantCoeff
      D.faber.scale.regular0 = D.faber.scale.leading0 := rfl
  have ha1 : GCD369CubeHahnRegular.constantCoeff
      D.faber.scale.regular1 = D.faber.scale.leading1 := rfl
  have ha2 : GCD369CubeHahnRegular.constantCoeff
      D.faber.scale.regular2 = D.faber.scale.leading2 := rfl
  have ha3 : GCD369CubeHahnRegular.constantCoeff
      D.faber.scale.regular3 = D.faber.scale.leading3 := rfl
  have ha4 : GCD369CubeHahnRegular.constantCoeff
      D.faber.scale.regular4 = D.faber.scale.leading4 := rfl
  rw [ha0, ha1, ha2, ha3, ha4,
    D.ha0, D.ha1, D.ha2, D.ha3, D.ha4]
  dsimp only [GCD369CubeNormalRow5]
  ring

/-- If the weight-two load arrives before the first transverse normal, all
normal coefficients at its cutoff vanish.  The remaining pure `c7` rows
cannot meet even one root of the projective common cubic. -/
theorem TransverseScale.c7_eq_zero_before_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C7 C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (hbefore : D.faber.scale.p < T.delta) : C7 = 0 := by
  by_contra hC7
  have hz := D.faber.c7NCoeff_zero C5 C4 C3 C2 C1 R1 R2 R3 R4
    hd hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4
  rcases hz with ⟨hz1, hz2, _hz3, hz4⟩
  have he : 2 * D.faber.scale.p < 2 * T.delta := by linarith
  have hzero1 := T.zeroHighN1Coeff_zero_of_lt he
  have hzero2 := T.zeroHighN2Coeff_zero_of_lt he
  have hzero4 := T.zeroHighN4Coeff_zero_of_lt he
  have hp : 0 < D.faber.scale.p := D.faber.scale.hp
  have hweighted : D.faber.scale.weightedRegular 2 D.faber.c7 =
      (GCD369CubeHahnRegular.monomial
        D.faber.scale.p hp.le) ^ 2 *
          GCD369CubeHahnRegular.constant C7 := by
    rw [hc7, D.faber.scale.weightedRegular_constant_eq_monomial_sq
      2 (by norm_num) C7]
    congr 3 <;> ring
  let P1 : GCD369CubeHahnRegular k :=
    12096 * D.faber.scale.regular0 * D.faber.scale.regular4 +
      12096 * D.faber.scale.regular1 * D.faber.scale.regular3 +
      6048 * D.faber.scale.regular2 ^ 2 -
      5040 * D.faber.scale.regular2 * D.faber.scale.regular4 ^ 2 -
      5040 * D.faber.scale.regular3 ^ 2 * D.faber.scale.regular4 +
      770 * D.faber.scale.regular4 ^ 4
  let P2 : GCD369CubeHahnRegular k :=
    36288 * D.faber.scale.regular0 * D.faber.scale.regular3 +
      36288 * D.faber.scale.regular1 * D.faber.scale.regular2 -
      15120 * D.faber.scale.regular1 * D.faber.scale.regular4 ^ 2 -
      30240 * D.faber.scale.regular2 * D.faber.scale.regular3 *
        D.faber.scale.regular4 -
      5040 * D.faber.scale.regular3 ^ 3 +
      9240 * D.faber.scale.regular3 * D.faber.scale.regular4 ^ 3
  let P4 : GCD369CubeHahnRegular k :=
    326592 * D.faber.scale.regular0 * D.faber.scale.regular1 -
      108864 * D.faber.scale.regular0 * D.faber.scale.regular3 *
        D.faber.scale.regular4 -
      163296 * D.faber.scale.regular1 * D.faber.scale.regular2 *
        D.faber.scale.regular4 -
      81648 * D.faber.scale.regular1 * D.faber.scale.regular3 ^ 2 +
      37800 * D.faber.scale.regular1 * D.faber.scale.regular4 ^ 3 -
      108864 * D.faber.scale.regular2 ^ 2 * D.faber.scale.regular3 +
      136080 * D.faber.scale.regular2 * D.faber.scale.regular3 *
        D.faber.scale.regular4 ^ 2 +
      45360 * D.faber.scale.regular3 ^ 3 * D.faber.scale.regular4 -
      27720 * D.faber.scale.regular3 * D.faber.scale.regular4 ^ 4
  have hload1 :
      (((GCD369CubeHahnRegular.monomial
          D.faber.scale.p hp.le) ^ 2 *
        GCD369CubeHahnRegular.constant C7 * P1).1.coeff
          (2 * D.faber.scale.p)) =
        C7 * GCD369CubeHahnRegular.constantCoeff P1 := by
    exact GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      D.faber.scale.p hp C7 P1
  have hload2 :
      (((GCD369CubeHahnRegular.monomial
          D.faber.scale.p hp.le) ^ 2 *
        GCD369CubeHahnRegular.constant C7 * P2).1.coeff
          (2 * D.faber.scale.p)) =
        C7 * GCD369CubeHahnRegular.constantCoeff P2 := by
    exact GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      D.faber.scale.p hp C7 P2
  have hload4 :
      (((GCD369CubeHahnRegular.monomial
          D.faber.scale.p hp.le) ^ 2 *
        GCD369CubeHahnRegular.constant C7 * P4).1.coeff
          (2 * D.faber.scale.p)) =
        C7 * GCD369CubeHahnRegular.constantCoeff P4 := by
    exact GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      D.faber.scale.p hp C7 P4
  change
    (729 * GCD369CubeFaberN1
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff (2 * D.faber.scale.p) +
      (D.faber.scale.weightedRegular 2 D.faber.c7 * P1).1.coeff
        (2 * D.faber.scale.p) = 0 at hz1
  change
    (2187 * GCD369CubeFaberN2
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff (2 * D.faber.scale.p) +
      (D.faber.scale.weightedRegular 2 D.faber.c7 * P2).1.coeff
        (2 * D.faber.scale.p) = 0 at hz2
  change
    (6561 * GCD369CubeFaberN4
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff (2 * D.faber.scale.p) +
      (D.faber.scale.weightedRegular 2 D.faber.c7 * P4).1.coeff
        (2 * D.faber.scale.p) = 0 at hz4
  rw [hzero1, hweighted, hload1, zero_add] at hz1
  rw [hzero2, hweighted, hload2, zero_add] at hz2
  rw [hzero4, hweighted, hload4, zero_add] at hz4
  dsimp only [P1, P2, P4] at hz1 hz2 hz4
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat] at hz1 hz2 hz4
  change C7 *
    (12096 * D.faber.scale.leading0 * D.faber.scale.leading4 +
      12096 * D.faber.scale.leading1 * D.faber.scale.leading3 +
      6048 * D.faber.scale.leading2 ^ 2 -
      5040 * D.faber.scale.leading2 * D.faber.scale.leading4 ^ 2 -
      5040 * D.faber.scale.leading3 ^ 2 * D.faber.scale.leading4 +
      770 * D.faber.scale.leading4 ^ 4) = 0 at hz1
  change C7 *
    (36288 * D.faber.scale.leading0 * D.faber.scale.leading3 +
      36288 * D.faber.scale.leading1 * D.faber.scale.leading2 -
      15120 * D.faber.scale.leading1 * D.faber.scale.leading4 ^ 2 -
      30240 * D.faber.scale.leading2 * D.faber.scale.leading3 *
        D.faber.scale.leading4 - 5040 * D.faber.scale.leading3 ^ 3 +
      9240 * D.faber.scale.leading3 * D.faber.scale.leading4 ^ 3) = 0 at hz2
  change C7 *
    (326592 * D.faber.scale.leading0 * D.faber.scale.leading1 -
      108864 * D.faber.scale.leading0 * D.faber.scale.leading3 *
        D.faber.scale.leading4 -
      163296 * D.faber.scale.leading1 * D.faber.scale.leading2 *
        D.faber.scale.leading4 -
      81648 * D.faber.scale.leading1 * D.faber.scale.leading3 ^ 2 +
      37800 * D.faber.scale.leading1 * D.faber.scale.leading4 ^ 3 -
      108864 * D.faber.scale.leading2 ^ 2 * D.faber.scale.leading3 +
      136080 * D.faber.scale.leading2 * D.faber.scale.leading3 *
        D.faber.scale.leading4 ^ 2 +
      45360 * D.faber.scale.leading3 ^ 3 * D.faber.scale.leading4 -
      27720 * D.faber.scale.leading3 * D.faber.scale.leading4 ^ 4) = 0 at hz4
  rw [D.ha0, D.ha1, D.ha2, D.ha3, D.ha4] at hz1 hz2 hz4
  have hrows : GCD369CubeC7LeadingFaberRowsAt
      0 0 0 D.u D.v C7 := by
    dsimp [GCD369CubeC7LeadingFaberRowsAt]
    have hc := GCD369CubeFaberC7NormalCoefficients
      (0 : k) 0 0 D.u D.v C7
    dsimp at hc
    rcases hc with ⟨hc1', hc2', hc3', hc4'⟩
    rw [hc1', hc2', hc3', hc4']
    constructor
    · dsimp only [GCD369CubeNormalRow1]
      linear_combination hz1
    constructor
    · linear_combination hz2
    constructor
    · dsimp only [GCD369CubeNormalRow3]
      ring
    · linear_combination hz4
  have hnocommon := GCD369CubeC7LeadingFaberRowsAt_noCommonRoot
    (0 : k) 0 0 D.u D.v C7 hC7 D.hprojective hrows
  obtain ⟨r, hr⟩ := GCD369CubeExistsDepressedCubicRoot D.u D.v
  exact hnocommon r hr (by ring)

/-- At the exact `c7`/transverse tie, the four source equations are the
arbitrary-`c7` Kuranishi row packet on the infinity residue jet. -/
theorem TransverseScale.c7LeadingFaberRowsAt_at_transverse
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C7 C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : D.faber.scale.p = T.delta) :
    GCD369CubeC7LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C7 := by
  have hz := D.faber.c7NCoeff_zero C5 C4 C3 C2 C1 R1 R2 R3 R4
    hd hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4
  have hweighted : D.faber.scale.weightedRegular 2 D.faber.c7 =
      (GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
        GCD369CubeHahnRegular.constant C7 := by
    rw [hc7, D.faber.scale.weightedRegular_constant_eq_monomial_sq
      2 (by norm_num) C7]
    apply Subtype.ext
    change
      (HahnSeries.single (((2 : ℕ) : ℚ) * D.faber.scale.p / 2) (1 : k)) ^ 2 *
          HahnSeries.C C7 =
        (HahnSeries.single T.delta (1 : k)) ^ 2 * HahnSeries.C C7
    rw [htie]
    congr 4 <;> ring
  rw [hweighted] at hz
  have hc := GCD369CubeFaberC7NormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C7
  dsimp only at hc
  dsimp [GCD369CubeC7LeadingFaberRowsAt]
  rcases hz with ⟨hz1, hz2, hz3, hz4⟩
  rcases hc with ⟨hc1, hc2, hc3, hc4⟩
  have heq : ((2 : ℕ) : ℚ) * D.faber.scale.p =
      ((2 : ℕ) : ℚ) * T.delta := by rw [htie]
  rw [heq] at hz1 hz2 hz3 hz4
  have ht1 := T.c7N1Coeff C7
  have ht2 := T.c7N2Coeff C7
  have ht3 := T.c7N3Coeff C7
  have ht4 := T.c7N4Coeff C7
  rw [ht1] at hz1
  rw [ht2] at hz2
  rw [ht3] at hz3
  rw [ht4] at hz4
  constructor
  · rw [hc1]
    exact hz1
  constructor
  · rw [hc2]
    exact hz2
  constructor
  · rw [hc3]
    exact hz3
  · rw [hc4]
    exact hz4

/-- The tied `c7` row packet has a certified nonzero terminal residue when
the load itself is nonzero.  This is the algebraic input for the subsequent
constant-pole degree landing. -/
theorem TransverseScale.c7Terminal_nonzero_at_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C7 C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hC7 : C7 ≠ 0)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : D.faber.scale.p = T.delta) :
    ∃ lambda : k, lambda ≠ 0 ∧ lambda ^ 2 * C7 = 1 ∧
      112 * (lambda ^ 2 * D.u) ^ 6 -
          5040 * (lambda ^ 2 * D.u) ^ 3 * (lambda ^ 3 * D.v) ^ 2 +
          4536 * (lambda ^ 3 * D.v) ^ 4 -
          2187 * (lambda ^ 2 * D.u) ^ 3 *
            (lambda ^ 4 * GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
          6561 * (lambda ^ 3 * D.v) ^ 2 *
            (lambda ^ 4 * GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
          13122 * (lambda ^ 2 * D.u) * (lambda ^ 3 * D.v) *
            (lambda ^ 4 * GCD369CubeHahnRegular.constantCoeff T.Xn) *
            (lambda ^ 5 * GCD369CubeHahnRegular.constantCoeff T.Yn) +
          4374 * (lambda ^ 2 * D.u) ^ 2 *
            (lambda ^ 4 * GCD369CubeHahnRegular.constantCoeff T.Xn) *
            (lambda ^ 6 * GCD369CubeHahnRegular.constantCoeff T.Zn) +
          2187 * (lambda ^ 2 * D.u) ^ 2 *
            (lambda ^ 5 * GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 -
          13122 * (lambda ^ 3 * D.v) *
            (lambda ^ 5 * GCD369CubeHahnRegular.constantCoeff T.Yn) *
            (lambda ^ 6 * GCD369CubeHahnRegular.constantCoeff T.Zn) ≠ 0 := by
  have hrows := T.c7LeadingFaberRowsAt_at_transverse
    C7 C5 C4 C3 C2 C1 R1 R2 R3 R4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 htie
  dsimp [GCD369CubeC7LeadingFaberRowsAt] at hrows
  have hcoeff := GCD369CubeFaberC7NormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C7
  dsimp at hcoeff
  rcases hrows with ⟨hf1, hf2, _hf3, hf4⟩
  rcases hcoeff with ⟨hc1', hc2', _hc3', hc4'⟩
  rw [hc1'] at hf1
  rw [hc2'] at hf2
  rw [hc4'] at hf4
  have h1 :
      56 * C7 * D.u ^ 4 - 1008 * C7 * D.u * D.v ^ 2 +
        GCD369CubeNormalRow1
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u = 0 :=
    (mul_eq_zero.mp hf1).resolve_left (by norm_num)
  have h2 :
      224 * C7 * D.u ^ 3 * D.v - 336 * C7 * D.v ^ 3 +
        729 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
        1458 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) -
        1458 * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) = 0 :=
    (mul_eq_zero.mp hf2).resolve_left (by norm_num)
  have h4 :
      224 * C7 * D.u ^ 4 * D.v - 1008 * C7 * D.u * D.v ^ 3 -
        2187 * D.u * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
        1458 * D.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) +
        2916 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) +
        1458 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 +
        1458 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) = 0 :=
    (mul_eq_zero.mp hf4).resolve_left (by norm_num)
  obtain ⟨lambda, hlambda, hscale⟩ :=
    GCD369CubeExistsWeightedNormalizer 2 (by norm_num) C7 hC7
  refine ⟨lambda, hlambda, hscale, ?_⟩
  apply GCD369CubeC7TerminalNonzero
    (lambda ^ 4 * GCD369CubeHahnRegular.constantCoeff T.Xn)
    (lambda ^ 5 * GCD369CubeHahnRegular.constantCoeff T.Yn)
    (lambda ^ 6 * GCD369CubeHahnRegular.constantCoeff T.Zn)
    (lambda ^ 2 * D.u) (lambda ^ 3 * D.v)
    (GCD369CubeProjectiveOfWeightedScale lambda D.u D.v hlambda D.hprojective)
  · calc
      56 * (lambda ^ 2 * D.u) ^ 4 -
          1008 * (lambda ^ 2 * D.u) * (lambda ^ 3 * D.v) ^ 2 +
          729 * (lambda ^ 2 * D.u) *
            (lambda ^ 4 * GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
          1458 * (lambda ^ 4 * GCD369CubeHahnRegular.constantCoeff T.Xn) *
            (lambda ^ 6 * GCD369CubeHahnRegular.constantCoeff T.Zn) -
          729 * (lambda ^ 5 * GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 =
          lambda ^ 10 * (56 * C7 * D.u ^ 4 -
            1008 * C7 * D.u * D.v ^ 2 +
            GCD369CubeNormalRow1
              (GCD369CubeHahnRegular.constantCoeff T.Xn)
              (GCD369CubeHahnRegular.constantCoeff T.Yn)
              (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u) := by
            rw [GCD369CubeNormalRow1]
            linear_combination
              (-(lambda ^ 8 * (56 * D.u ^ 4 - 1008 * D.u * D.v ^ 2))) * hscale
      _ = 0 := by rw [h1, mul_zero]
  · calc
      224 * (lambda ^ 2 * D.u) ^ 3 * (lambda ^ 3 * D.v) -
          336 * (lambda ^ 3 * D.v) ^ 3 +
          729 * (lambda ^ 3 * D.v) *
            (lambda ^ 4 * GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
          1458 * (lambda ^ 2 * D.u) *
            (lambda ^ 4 * GCD369CubeHahnRegular.constantCoeff T.Xn) *
            (lambda ^ 5 * GCD369CubeHahnRegular.constantCoeff T.Yn) -
          1458 * (lambda ^ 5 * GCD369CubeHahnRegular.constantCoeff T.Yn) *
            (lambda ^ 6 * GCD369CubeHahnRegular.constantCoeff T.Zn) =
          lambda ^ 11 * (224 * C7 * D.u ^ 3 * D.v -
            336 * C7 * D.v ^ 3 +
            729 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
            1458 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
              (GCD369CubeHahnRegular.constantCoeff T.Yn) -
            1458 * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
              (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
            linear_combination
              (-(lambda ^ 9 * (224 * D.u ^ 3 * D.v - 336 * D.v ^ 3))) * hscale
      _ = 0 := by rw [h2, mul_zero]
  · calc
      224 * (lambda ^ 2 * D.u) ^ 4 * (lambda ^ 3 * D.v) -
          1008 * (lambda ^ 2 * D.u) * (lambda ^ 3 * D.v) ^ 3 -
          2187 * (lambda ^ 2 * D.u) * (lambda ^ 3 * D.v) *
            (lambda ^ 4 * GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
          1458 * (lambda ^ 2 * D.u) ^ 2 *
            (lambda ^ 4 * GCD369CubeHahnRegular.constantCoeff T.Xn) *
            (lambda ^ 5 * GCD369CubeHahnRegular.constantCoeff T.Yn) +
          2916 * (lambda ^ 3 * D.v) *
            (lambda ^ 4 * GCD369CubeHahnRegular.constantCoeff T.Xn) *
            (lambda ^ 6 * GCD369CubeHahnRegular.constantCoeff T.Zn) +
          1458 * (lambda ^ 3 * D.v) *
            (lambda ^ 5 * GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 +
          1458 * (lambda ^ 2 * D.u) *
            (lambda ^ 5 * GCD369CubeHahnRegular.constantCoeff T.Yn) *
            (lambda ^ 6 * GCD369CubeHahnRegular.constantCoeff T.Zn) =
          lambda ^ 13 * (224 * C7 * D.u ^ 4 * D.v -
            1008 * C7 * D.u * D.v ^ 3 -
            2187 * D.u * D.v *
              (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
            1458 * D.u ^ 2 *
              (GCD369CubeHahnRegular.constantCoeff T.Xn) *
              (GCD369CubeHahnRegular.constantCoeff T.Yn) +
            2916 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
              (GCD369CubeHahnRegular.constantCoeff T.Zn) +
            1458 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 +
            1458 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
              (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
            linear_combination
              (-(lambda ^ 11 * (224 * D.u ^ 4 * D.v -
                1008 * D.u * D.v ^ 3))) * hscale
      _ = 0 := by rw [h4, mul_zero]

/-- Undoing the internal weighted normalization, the unnormalized terminal
polynomial with its actual `c7` coefficient is already nonzero. -/
theorem TransverseScale.c7TerminalAt_nonzero_at_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C7 C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hC7 : C7 ≠ 0)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : D.faber.scale.p = T.delta) :
    112 * C7 * D.u ^ 6 - 5040 * C7 * D.u ^ 3 * D.v ^ 2 +
        4536 * C7 * D.v ^ 4 -
        2187 * D.u ^ 3 * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
        6561 * D.v ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
        13122 * D.u * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) +
        4374 * D.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) +
        2187 * D.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 -
        13122 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) ≠ 0 := by
  obtain ⟨lambda, hlambda, hscale, hnormalized⟩ :=
    T.c7Terminal_nonzero_at_transverse
      C7 C5 C4 C3 C2 C1 R1 R2 R3 R4 hC7
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 htie
  intro hzero
  apply hnormalized
  calc
    _ = lambda ^ 14 *
        (112 * C7 * D.u ^ 6 - 5040 * C7 * D.u ^ 3 * D.v ^ 2 +
          4536 * C7 * D.v ^ 4 -
          2187 * D.u ^ 3 * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
          6561 * D.v ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
          13122 * D.u * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
            (GCD369CubeHahnRegular.constantCoeff T.Yn) +
          4374 * D.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
            (GCD369CubeHahnRegular.constantCoeff T.Zn) +
          2187 * D.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 -
          13122 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
            (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
          linear_combination
            (-(lambda ^ 12 *
              (112 * D.u ^ 6 - 5040 * D.u ^ 3 * D.v ^ 2 +
                4536 * D.v ^ 4))) * hscale
    _ = 0 := by rw [hzero, mul_zero]

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubeHahnFaberPoleData

/-- Once `d=0`, every load strictly after `c7` is invisible through the
weight-two terminal cutoff. -/
theorem fullN5_sub_c7Specialized_mem_higherOrderIdeal
    {k : Type*} [Field k] [CharZero k]
    (F : GCD369CubeHahnFaberPoleData k)
    (C5 C4 C3 C2 C1 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
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
      F.scale.regular3 F.scale.regular4 0
      (F.scale.weightedRegular 2 F.c7) 0 0 0 0 0 ∈
        GCD369CubeHahnRegular.higherOrderIdeal
          (2 * F.scale.p) (mul_nonneg (by norm_num) F.scale.hp.le) := by
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal
      (2 * F.scale.p) (mul_nonneg (by norm_num) F.scale.hp.le)
  let q := Ideal.Quotient.mk I
  have hweight (w : ℕ) (hw : 2 < w) :
      2 * F.scale.p < (w : ℚ) * F.scale.p := by
    exact mul_lt_mul_of_pos_right
      (show (2 : ℚ) < (w : ℚ) by exact_mod_cast hw) F.scale.hp
  have hdq : q (F.scale.weightedRegular 1 F.d) = 0 := by
    rw [hd]
    have hz : F.scale.weightedRegular 1
        (GCD369CubeHahnRegular.constant (0 : k)) = 0 := by
      apply Subtype.ext
      change F.scale.t ^ 1 * HahnSeries.C (0 : k) = 0
      simp
    rw [hz, map_zero]
  have hc5q : q (F.scale.weightedRegular 4 F.c5) = 0 := by
    rw [hc5, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 4 C5 (mul_nonneg (by norm_num) F.scale.hp.le)
        (hweight 4 (by norm_num))
  have hc4q : q (F.scale.weightedRegular 5 F.c4) = 0 := by
    rw [hc4, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 5 C4 (mul_nonneg (by norm_num) F.scale.hp.le)
        (hweight 5 (by norm_num))
  have hc3q : q (F.scale.weightedRegular 6 F.c3) = 0 := by
    rw [hc3, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 6 C3 (mul_nonneg (by norm_num) F.scale.hp.le)
        (hweight 6 (by norm_num))
  have hc2q : q (F.scale.weightedRegular 7 F.c2) = 0 := by
    rw [hc2, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 7 C2 (mul_nonneg (by norm_num) F.scale.hp.le)
        (hweight 7 (by norm_num))
  have hc1q : q (F.scale.weightedRegular 8 F.c1) = 0 := by
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
  let c7row : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4 0
    (F.scale.weightedRegular 2 F.c7) 0 0 0 0 0
  have hq : q full = q c7row := by
    dsimp only [full, c7row]
    rw [GCD369CubeFaberFullN5_map, GCD369CubeFaberFullN5_map,
      hdq, hc5q, hc4q, hc3q, hc2q, hc1q]
    simp
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [map_sub, hq, sub_self]

/-- Coefficient form of the preceding higher-order comparison. -/
theorem fullN5Coeff_eq_c7Specialized
    {k : Type*} [Field k] [CharZero k]
    (F : GCD369CubeHahnFaberPoleData k)
    (C5 C4 C3 C2 C1 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
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
      (F.scale.weightedRegular 8 F.c1)).1.coeff (2 * F.scale.p) =
    (GCD369CubeFaberFullN5
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4 0
      (F.scale.weightedRegular 2 F.c7) 0 0 0 0 0).1.coeff
        (2 * F.scale.p) := by
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
  let c7row : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4 0
    (F.scale.weightedRegular 2 F.c7) 0 0 0 0 0
  have hdiff := F.fullN5_sub_c7Specialized_mem_higherOrderIdeal
    C5 C4 C3 C2 C1 hd hc5 hc4 hc3 hc2 hc1
  have hcoeff : (full - c7row).1.coeff (2 * F.scale.p) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop hdiff
  change full.1.coeff (2 * F.scale.p) = c7row.1.coeff (2 * F.scale.p)
  change full.1.coeff (2 * F.scale.p) -
      c7row.1.coeff (2 * F.scale.p) = 0 at hcoeff
  exact sub_eq_zero.mp hcoeff

end GCD369CubeHahnFaberPoleData

namespace GCD369CubeHahnCommonCoefficientData

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- A nonzero tied `c7` load makes the complete terminal numerator have
exact order `2 p`; all later loads are strictly higher. -/
theorem TransverseScale.fullN5_orderTop_eq_two_p_of_c7_tie
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C7 C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hC7 : C7 ≠ 0)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : D.faber.scale.p = T.delta) :
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
      (D.faber.scale.weightedRegular 8 D.faber.c1)).1.orderTop =
        (↑(2 * D.faber.scale.p) : WithTop ℚ) := by
  let full : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4
    (D.faber.scale.weightedRegular 1 D.faber.d)
    (D.faber.scale.weightedRegular 2 D.faber.c7)
    (D.faber.scale.weightedRegular 4 D.faber.c5)
    (D.faber.scale.weightedRegular 5 D.faber.c4)
    (D.faber.scale.weightedRegular 6 D.faber.c3)
    (D.faber.scale.weightedRegular 7 D.faber.c2)
    (D.faber.scale.weightedRegular 8 D.faber.c1)
  let c7row : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4 0
    (D.faber.scale.weightedRegular 2 D.faber.c7) 0 0 0 0 0
  have hterminal := T.c7TerminalAt_nonzero_at_transverse
    C7 C5 C4 C3 C2 C1 R1 R2 R3 R4 hC7
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 htie
  have hspecialCoeff := T.c7SpecializedTerminalCoeff_at_transverse
    C7 hc7 htie
  have hspecialCoeffNe : c7row.1.coeff (2 * D.faber.scale.p) ≠ 0 := by
    change
      (GCD369CubeFaberFullN5
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 0
        (D.faber.scale.weightedRegular 2 D.faber.c7)
        0 0 0 0 0).1.coeff (2 * D.faber.scale.p) ≠ 0
    rw [hspecialCoeff]
    exact mul_ne_zero (by norm_num) hterminal
  have hspecialUpper : c7row.1.orderTop ≤
      (↑(2 * D.faber.scale.p) : WithTop ℚ) :=
    HahnSeries.orderTop_le_of_coeff_ne_zero hspecialCoeffNe
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let P : GCD369CubeHahnRegular k := terminalC7Coeff
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4
  let K : GCD369CubeHahnRegular k :=
    559872 * GCD369CubeNormalRow5
      T.Xn T.Yn T.Zn D.cubicU D.cubicV +
      GCD369CubeHahnRegular.constant C7 * P
  let E : GCD369CubeHahnRegular k :=
    839808 * GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU
  have hload : D.faber.scale.weightedRegular 2 D.faber.c7 =
      H ^ 2 * GCD369CubeHahnRegular.constant C7 := by
    rw [hc7, D.faber.scale.weightedRegular_constant_eq_monomial_sq
      2 (by norm_num) C7]
    apply Subtype.ext
    change
      (HahnSeries.single (((2 : ℕ) : ℚ) * D.faber.scale.p / 2) (1 : k)) ^ 2 *
          HahnSeries.C C7 =
        (HahnSeries.single T.delta (1 : k)) ^ 2 * HahnSeries.C C7
    rw [htie]
    congr 4 <;> ring
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
  have hfactor : c7row = H ^ 2 * (K + H * E) := by
    dsimp only [c7row]
    rw [fullN5_c7_specialize, hload]
    rw [hchart0, hchart1, hchart2,
      D.regular3_eq_two_cubicV, D.regular4_eq_two_cubicU]
    rw [hzero]
    dsimp only [K, E]
    rw [← hchart0, ← hchart1, ← hchart2,
      ← D.regular3_eq_two_cubicV, ← D.regular4_eq_two_cubicU]
    ring
  have hspecialLower : (↑(2 * D.faber.scale.p) : WithTop ℚ) ≤
      c7row.1.orderTop := by
    rw [hfactor, htie]
    exact GCD369CubeHahnRegular.orderTop_monomial_pow_mul_lower
      T.delta T.hdelta 2 (K + H * E)
  have hspecialOrder : c7row.1.orderTop =
      (↑(2 * D.faber.scale.p) : WithTop ℚ) :=
    le_antisymm hspecialUpper hspecialLower
  have hdiff : full - c7row ∈
      GCD369CubeHahnRegular.higherOrderIdeal
        (2 * D.faber.scale.p)
        (mul_nonneg (by norm_num) D.faber.scale.hp.le) :=
    D.faber.fullN5_sub_c7Specialized_mem_higherOrderIdeal
      C5 C4 C3 C2 C1 hd hc5 hc4 hc3 hc2 hc1
  have hlt : c7row.1.orderTop < (full - c7row).1.orderTop := by
    rw [hspecialOrder]
    exact hdiff
  have hsum := HahnSeries.orderTop_add_eq_right hlt
  have hfull : (full - c7row + c7row) = full := by ring
  have hfullval : (full - c7row).1 + c7row.1 = full.1 :=
    congrArg Subtype.val hfull
  rw [hfullval] at hsum
  change full.1.orderTop = (↑(2 * D.faber.scale.p) : WithTop ℚ)
  exact hsum.trans hspecialOrder

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubePolynomialSource

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- A nonzero `c7` load cannot tie the first transverse normal at a
constant-core infinity pole.  Its exact terminal order forces the impossible
weight-two polynomial-degree landing. -/
theorem infinity_c7_eq_zero_at_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hd : S.faberConstantParameters.d = 0)
    (htie :
      (S.infinityCommonCoefficientData hsdegree).faber.scale.p = T.delta) :
    S.faberConstantParameters.c7 = 0 := by
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let D := S.infinityCommonCoefficientData hsdegree
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  obtain ⟨hdraw, hc7, hc5, hc4, hc3, hc2, hc1,
      hr1, hr2, hr3, hr4⟩ :=
    S.infinityFaberPoleData_constant_loads hpole
  have hdD : D.faber.d = GCD369CubeHahnRegular.constant 0 := by
    have h := hdraw
    rw [hd] at h
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using h
  have hc7D : D.faber.c7 = GCD369CubeHahnRegular.constant P.c7 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc7
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
  by_contra hPc7
  have hNorder := T.fullN5_orderTop_eq_two_p_of_c7_tie
    P.c7 P.c5 P.c4 P.c3 P.c2 P.c1
      R.rho1 R.rho2 R.rho3 R.rho4 hPc7
    hdD hc7D hc5D hc4D hc3D hc2D hc1D
      hr1D hr2D hr3D hr4D htie
  have hterminalOrder :=
    GCD369CubeHahnFaberPoleData.faberR5_order_eq_of_fullN5_orderTop_eq
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (D.faber.scale.weightedRegular 1 D.faber.d)
      (D.faber.scale.weightedRegular 2 D.faber.c7)
      (D.faber.scale.weightedRegular 4 D.faber.c5)
      (D.faber.scale.weightedRegular 5 D.faber.c4)
      (D.faber.scale.weightedRegular 6 D.faber.c3)
      (D.faber.scale.weightedRegular 7 D.faber.c2)
      (D.faber.scale.weightedRegular 8 D.faber.c1)
      (2 * D.faber.scale.p) hNorder
  let terminal : HahnSeries ℚ k := GCD369CubeFaberR5
    (D.faber.scale.regular0 : HahnSeries ℚ k)
    D.faber.scale.regular1 D.faber.scale.regular2
    D.faber.scale.regular3 D.faber.scale.regular4
    (D.faber.scale.weightedRegular 1 D.faber.d)
    (D.faber.scale.weightedRegular 2 D.faber.c7)
    (D.faber.scale.weightedRegular 4 D.faber.c5)
    (D.faber.scale.weightedRegular 5 D.faber.c4)
    (D.faber.scale.weightedRegular 6 D.faber.c3)
    (D.faber.scale.weightedRegular 7 D.faber.c2)
    (D.faber.scale.weightedRegular 8 D.faber.c1)
  have hscaled : terminal = D.faber.scale.t ^ 14 *
      GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant := by
    have hs := S.infinityFaberPoleData_scaled_terminal hpole
    change terminal = D.faber.scale.t ^ 14 *
      GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant at hs
    exact hs
  have hfirst :
      (D.faber.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order =
          2 * D.faber.scale.p := by
    rw [← hscaled]
    simpa only [terminal] using hterminalOrder
  have hscale : 12 * (S.infinityFaberPoleData hpole).scale.p = 1 := by
    have h := S.infinity_terminal_scale_eq_of_order_eq_weight
      hsdegree hpole 2 hfirst
    norm_num at h
    simpa only [D, S.infinityCommonCoefficientData_faber hsdegree] using h
  have hcoordinateD :
      D.faber.scale.leading4 ≠ 0 ∨ D.faber.scale.leading3 ≠ 0 := by
    rcases D.hprojective with hu | hv
    · left
      rw [D.ha4]
      exact mul_ne_zero (by norm_num) hu
    · right
      rw [D.ha3]
      exact mul_ne_zero (by norm_num) hv
  have hcoordinate :
      (S.infinityFaberPoleData hpole).scale.leading4 ≠ 0 ∨
      (S.infinityFaberPoleData hpole).scale.leading3 ≠ 0 := by
    simpa only [D, S.infinityCommonCoefficientData_faber hsdegree]
      using hcoordinateD
  exact GCD369CubeConstantPoleDegreeLandingEmpty
    (S.infinityConstantPoleDegreeLanding_of_c7_scale
      hsdegree hpole hscale hcoordinate)

end GCD369CubePolynomialSource

#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.c7LeadingFaberRowsAt_at_transverse
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.c7Terminal_nonzero_at_transverse
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.c7_eq_zero_before_transverse
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.fullN5_orderTop_eq_two_p_of_c7_tie
#print axioms GCD369CubePolynomialSource.infinity_c7_eq_zero_at_transverse
