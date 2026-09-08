import FiniteCommonSource

/-! # Pure `c7` load polynomials on the common cubic

The four integral `c7` numerators split as the zero-high Faber rows plus a
weight-two load polynomial in the scaled sextic coordinates.  This file
records the leading residues of those load polynomials under the common-cubic
normalization, and their specialization on the double-root sheet
`u = -3 r^2`, `v = 2 r^3`.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- Leading residue of the first integral `c7` polynomial on the common
cubic. -/
theorem c7LoadPoly1_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      12096 * S.normal.sextic.scale.regular0 *
          S.normal.sextic.scale.regular4 +
        12096 * S.normal.sextic.scale.regular1 *
          S.normal.sextic.scale.regular3 +
        6048 * S.normal.sextic.scale.regular2 ^ 2 -
        5040 * S.normal.sextic.scale.regular2 *
          S.normal.sextic.scale.regular4 ^ 2 -
        5040 * S.normal.sextic.scale.regular3 ^ 2 *
          S.normal.sextic.scale.regular4 +
        770 * S.normal.sextic.scale.regular4 ^ 4
    GCD369CubeHahnRegular.constantCoeff P =
      -1792 * S.u ^ 4 + 32256 * S.u * S.v ^ 2 := by
  dsimp only
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change
    12096 * S.normal.sextic.scale.leading0 *
        S.normal.sextic.scale.leading4 +
      12096 * S.normal.sextic.scale.leading1 *
        S.normal.sextic.scale.leading3 +
      6048 * S.normal.sextic.scale.leading2 ^ 2 -
      5040 * S.normal.sextic.scale.leading2 *
        S.normal.sextic.scale.leading4 ^ 2 -
      5040 * S.normal.sextic.scale.leading3 ^ 2 *
        S.normal.sextic.scale.leading4 +
      770 * S.normal.sextic.scale.leading4 ^ 4 = _
  rw [S.ha0, S.ha1, S.ha2, S.ha3, S.ha4]
  ring

/-- Leading residue of the second integral `c7` polynomial on the common
cubic. -/
theorem c7LoadPoly2_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      36288 * S.normal.sextic.scale.regular0 *
          S.normal.sextic.scale.regular3 +
        36288 * S.normal.sextic.scale.regular1 *
          S.normal.sextic.scale.regular2 -
        15120 * S.normal.sextic.scale.regular1 *
          S.normal.sextic.scale.regular4 ^ 2 -
        30240 * S.normal.sextic.scale.regular2 *
          S.normal.sextic.scale.regular3 * S.normal.sextic.scale.regular4 -
        5040 * S.normal.sextic.scale.regular3 ^ 3 +
        9240 * S.normal.sextic.scale.regular3 *
          S.normal.sextic.scale.regular4 ^ 3
    GCD369CubeHahnRegular.constantCoeff P =
      -21504 * S.u ^ 3 * S.v + 32256 * S.v ^ 3 := by
  dsimp only
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change
    36288 * S.normal.sextic.scale.leading0 *
        S.normal.sextic.scale.leading3 +
      36288 * S.normal.sextic.scale.leading1 *
        S.normal.sextic.scale.leading2 -
      15120 * S.normal.sextic.scale.leading1 *
        S.normal.sextic.scale.leading4 ^ 2 -
      30240 * S.normal.sextic.scale.leading2 *
        S.normal.sextic.scale.leading3 * S.normal.sextic.scale.leading4 -
      5040 * S.normal.sextic.scale.leading3 ^ 3 +
      9240 * S.normal.sextic.scale.leading3 *
        S.normal.sextic.scale.leading4 ^ 3 = _
  rw [S.ha0, S.ha1, S.ha2, S.ha3, S.ha4]
  ring

/-- The third integral `c7` polynomial has vanishing residue on the common
cubic. -/
theorem c7LoadPoly3_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      48384 * S.normal.sextic.scale.regular0 *
          S.normal.sextic.scale.regular2 -
        12096 * S.normal.sextic.scale.regular0 *
          S.normal.sextic.scale.regular4 ^ 2 +
        24192 * S.normal.sextic.scale.regular1 ^ 2 -
        32256 * S.normal.sextic.scale.regular1 *
          S.normal.sextic.scale.regular3 * S.normal.sextic.scale.regular4 -
        16128 * S.normal.sextic.scale.regular2 ^ 2 *
          S.normal.sextic.scale.regular4 -
        20160 * S.normal.sextic.scale.regular2 *
          S.normal.sextic.scale.regular3 ^ 2 +
        8960 * S.normal.sextic.scale.regular2 *
          S.normal.sextic.scale.regular4 ^ 3 +
        15120 * S.normal.sextic.scale.regular3 ^ 2 *
          S.normal.sextic.scale.regular4 ^ 2 -
        1232 * S.normal.sextic.scale.regular4 ^ 5
    GCD369CubeHahnRegular.constantCoeff P = 0 := by
  dsimp only
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change
    48384 * S.normal.sextic.scale.leading0 *
        S.normal.sextic.scale.leading2 -
      12096 * S.normal.sextic.scale.leading0 *
        S.normal.sextic.scale.leading4 ^ 2 +
      24192 * S.normal.sextic.scale.leading1 ^ 2 -
      32256 * S.normal.sextic.scale.leading1 *
        S.normal.sextic.scale.leading3 * S.normal.sextic.scale.leading4 -
      16128 * S.normal.sextic.scale.leading2 ^ 2 *
        S.normal.sextic.scale.leading4 -
      20160 * S.normal.sextic.scale.leading2 *
        S.normal.sextic.scale.leading3 ^ 2 +
      8960 * S.normal.sextic.scale.leading2 *
        S.normal.sextic.scale.leading4 ^ 3 +
      15120 * S.normal.sextic.scale.leading3 ^ 2 *
        S.normal.sextic.scale.leading4 ^ 2 -
      1232 * S.normal.sextic.scale.leading4 ^ 5 = 0
  rw [S.ha0, S.ha1, S.ha2, S.ha3, S.ha4]
  ring

/-- Leading residue of the fourth integral `c7` polynomial on the common
cubic. -/
theorem c7LoadPoly4_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      326592 * S.normal.sextic.scale.regular0 *
          S.normal.sextic.scale.regular1 -
        108864 * S.normal.sextic.scale.regular0 *
          S.normal.sextic.scale.regular3 * S.normal.sextic.scale.regular4 -
        163296 * S.normal.sextic.scale.regular1 *
          S.normal.sextic.scale.regular2 * S.normal.sextic.scale.regular4 -
        81648 * S.normal.sextic.scale.regular1 *
          S.normal.sextic.scale.regular3 ^ 2 +
        37800 * S.normal.sextic.scale.regular1 *
          S.normal.sextic.scale.regular4 ^ 3 -
        108864 * S.normal.sextic.scale.regular2 ^ 2 *
          S.normal.sextic.scale.regular3 +
        136080 * S.normal.sextic.scale.regular2 *
          S.normal.sextic.scale.regular3 *
            S.normal.sextic.scale.regular4 ^ 2 +
        45360 * S.normal.sextic.scale.regular3 ^ 3 *
          S.normal.sextic.scale.regular4 -
        27720 * S.normal.sextic.scale.regular3 *
          S.normal.sextic.scale.regular4 ^ 4
    GCD369CubeHahnRegular.constantCoeff P =
      -64512 * S.u ^ 4 * S.v + 290304 * S.u * S.v ^ 3 := by
  dsimp only
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change
    326592 * S.normal.sextic.scale.leading0 *
        S.normal.sextic.scale.leading1 -
      108864 * S.normal.sextic.scale.leading0 *
        S.normal.sextic.scale.leading3 * S.normal.sextic.scale.leading4 -
      163296 * S.normal.sextic.scale.leading1 *
        S.normal.sextic.scale.leading2 * S.normal.sextic.scale.leading4 -
      81648 * S.normal.sextic.scale.leading1 *
        S.normal.sextic.scale.leading3 ^ 2 +
      37800 * S.normal.sextic.scale.leading1 *
        S.normal.sextic.scale.leading4 ^ 3 -
      108864 * S.normal.sextic.scale.leading2 ^ 2 *
        S.normal.sextic.scale.leading3 +
      136080 * S.normal.sextic.scale.leading2 *
        S.normal.sextic.scale.leading3 * S.normal.sextic.scale.leading4 ^ 2 +
      45360 * S.normal.sextic.scale.leading3 ^ 3 *
        S.normal.sextic.scale.leading4 -
      27720 * S.normal.sextic.scale.leading3 *
        S.normal.sextic.scale.leading4 ^ 4 = _
  rw [S.ha0, S.ha1, S.ha2, S.ha3, S.ha4]
  ring

end GCD369CubeHahnCommonValueData

/-- The four pure `c7`-load remainders on the double-root sheet
`u = -3 r^2`, `v = 2 r^3`.  Row three vanishes identically; the surviving
constants are `-532224 r^8`, `1419264 r^9`, and `-17418240 r^11`. -/
theorem GCD369Cube_c7LoadRemainders_doubleRoot
    {R : Type*} [CommRing R] (r : R) :
    (-1792 * (-3 * r ^ 2) ^ 4 +
        32256 * (-3 * r ^ 2) * (2 * r ^ 3) ^ 2 =
      -532224 * r ^ 8) ∧
    (-21504 * (-3 * r ^ 2) ^ 3 * (2 * r ^ 3) +
        32256 * (2 * r ^ 3) ^ 3 =
      1419264 * r ^ 9) ∧
    ((0 : R) = 0) ∧
    (-64512 * (-3 * r ^ 2) ^ 4 * (2 * r ^ 3) +
        290304 * (-3 * r ^ 2) * (2 * r ^ 3) ^ 3 =
      -17418240 * r ^ 11) := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · ring
  · ring
  · ring

#print axioms GCD369CubeHahnCommonValueData.c7LoadPoly1_constantCoeff
#print axioms GCD369CubeHahnCommonValueData.c7LoadPoly2_constantCoeff
#print axioms GCD369CubeHahnCommonValueData.c7LoadPoly3_constantCoeff
#print axioms GCD369CubeHahnCommonValueData.c7LoadPoly4_constantCoeff
#print axioms GCD369Cube_c7LoadRemainders_doubleRoot
