import FiniteCommonSource

/-! # Pure `c5` load polynomials on the common cubic

The four integral `c5` numerators split as the zero-high Faber rows plus a
weight-four load polynomial in the scaled sextic coordinates.  This file
records the leading residues of those load polynomials under the common-cubic
normalization, and their specialization on the double-root sheet
`u = -3 r^2`, `v = 2 r^3`.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- Leading residue of the first integral `c5` polynomial on the common
cubic. -/
theorem c5LoadPoly1_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      51840 * S.normal.sextic.scale.regular0 -
        8640 * S.normal.sextic.scale.regular2 *
          S.normal.sextic.scale.regular4 -
        4320 * S.normal.sextic.scale.regular3 ^ 2 +
        1680 * S.normal.sextic.scale.regular4 ^ 3
    GCD369CubeHahnRegular.constantCoeff P =
      -3840 * S.u ^ 3 + 34560 * S.v ^ 2 := by
  dsimp only
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change
    51840 * S.normal.sextic.scale.leading0 -
      8640 * S.normal.sextic.scale.leading2 *
        S.normal.sextic.scale.leading4 -
      4320 * S.normal.sextic.scale.leading3 ^ 2 +
      1680 * S.normal.sextic.scale.leading4 ^ 3 = _
  rw [S.ha0, S.ha2, S.ha3, S.ha4]
  ring

/-- Leading residue of the second integral `c5` polynomial on the common
cubic. -/
theorem c5LoadPoly2_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      -25920 * S.normal.sextic.scale.regular1 *
          S.normal.sextic.scale.regular4 -
        25920 * S.normal.sextic.scale.regular2 *
          S.normal.sextic.scale.regular3 +
        15120 * S.normal.sextic.scale.regular3 *
          S.normal.sextic.scale.regular4 ^ 2
    GCD369CubeHahnRegular.constantCoeff P =
      -34560 * S.u ^ 2 * S.v := by
  dsimp only
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
  change
    -25920 * S.normal.sextic.scale.leading1 *
        S.normal.sextic.scale.leading4 -
      25920 * S.normal.sextic.scale.leading2 *
        S.normal.sextic.scale.leading3 +
      15120 * S.normal.sextic.scale.leading3 *
        S.normal.sextic.scale.leading4 ^ 2 = _
  rw [S.ha1, S.ha2, S.ha3, S.ha4]
  ring

/-- The third integral `c5` polynomial has vanishing residue on the common
cubic. -/
theorem c5LoadPoly3_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      -34560 * S.normal.sextic.scale.regular1 *
          S.normal.sextic.scale.regular3 -
        17280 * S.normal.sextic.scale.regular2 ^ 2 +
        14400 * S.normal.sextic.scale.regular2 *
          S.normal.sextic.scale.regular4 ^ 2 +
        17280 * S.normal.sextic.scale.regular3 ^ 2 *
          S.normal.sextic.scale.regular4 -
        2520 * S.normal.sextic.scale.regular4 ^ 4
    GCD369CubeHahnRegular.constantCoeff P = 0 := by
  dsimp only
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
  change
    -34560 * S.normal.sextic.scale.leading1 *
        S.normal.sextic.scale.leading3 -
      17280 * S.normal.sextic.scale.leading2 ^ 2 +
      14400 * S.normal.sextic.scale.leading2 *
        S.normal.sextic.scale.leading4 ^ 2 +
      17280 * S.normal.sextic.scale.leading3 ^ 2 *
        S.normal.sextic.scale.leading4 -
      2520 * S.normal.sextic.scale.leading4 ^ 4 = 0
  rw [S.ha1, S.ha2, S.ha3, S.ha4]
  ring

/-- Leading residue of the fourth integral `c5` polynomial on the common
cubic. -/
theorem c5LoadPoly4_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      -233280 * S.normal.sextic.scale.regular1 *
          S.normal.sextic.scale.regular2 +
        58320 * S.normal.sextic.scale.regular1 *
          S.normal.sextic.scale.regular4 ^ 2 +
        155520 * S.normal.sextic.scale.regular2 *
          S.normal.sextic.scale.regular3 * S.normal.sextic.scale.regular4 +
        25920 * S.normal.sextic.scale.regular3 ^ 3 -
        45360 * S.normal.sextic.scale.regular3 *
          S.normal.sextic.scale.regular4 ^ 3
    GCD369CubeHahnRegular.constantCoeff P =
      -103680 * S.u ^ 3 * S.v + 207360 * S.v ^ 3 := by
  dsimp only
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
  change
    -233280 * S.normal.sextic.scale.leading1 *
        S.normal.sextic.scale.leading2 +
      58320 * S.normal.sextic.scale.leading1 *
        S.normal.sextic.scale.leading4 ^ 2 +
      155520 * S.normal.sextic.scale.leading2 *
        S.normal.sextic.scale.leading3 * S.normal.sextic.scale.leading4 +
      25920 * S.normal.sextic.scale.leading3 ^ 3 -
      45360 * S.normal.sextic.scale.leading3 *
        S.normal.sextic.scale.leading4 ^ 3 = _
  rw [S.ha1, S.ha2, S.ha3, S.ha4]
  ring

end GCD369CubeHahnCommonValueData

/-- The four pure `c5`-load remainders on the double-root sheet
`u = -3 r^2`, `v = 2 r^3`.  Row three vanishes identically; the surviving
constants are `241920 r^6`, `-622080 r^7`, and `7257600 r^9`. -/
theorem GCD369Cube_c5LoadRemainders_doubleRoot
    {R : Type*} [CommRing R] (r : R) :
    (-3840 * (-3 * r ^ 2) ^ 3 +
        34560 * (2 * r ^ 3) ^ 2 =
      241920 * r ^ 6) ∧
    (-34560 * (-3 * r ^ 2) ^ 2 * (2 * r ^ 3) =
      -622080 * r ^ 7) ∧
    ((0 : R) = 0) ∧
    (-103680 * (-3 * r ^ 2) ^ 3 * (2 * r ^ 3) +
        207360 * (2 * r ^ 3) ^ 3 =
      7257600 * r ^ 9) := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · ring
  · ring
  · ring

#print axioms GCD369CubeHahnCommonValueData.c5LoadPoly1_constantCoeff
#print axioms GCD369CubeHahnCommonValueData.c5LoadPoly2_constantCoeff
#print axioms GCD369CubeHahnCommonValueData.c5LoadPoly3_constantCoeff
#print axioms GCD369CubeHahnCommonValueData.c5LoadPoly4_constantCoeff
#print axioms GCD369Cube_c5LoadRemainders_doubleRoot
