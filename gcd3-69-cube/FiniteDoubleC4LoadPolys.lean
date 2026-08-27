import FiniteCommonSource

/-! # Pure `c4` load polynomials on the common cubic

The four integral `c4` numerators split as the zero-high Faber rows plus a
weight-five load polynomial in the scaled sextic coordinates.  This file
records their leading residues and their specialization on the double-root
sheet `u = -3 r^2`, `v = 2 r^3`.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

theorem c4LoadPoly1_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      41472 * S.normal.sextic.scale.regular1 -
        13824 * S.normal.sextic.scale.regular3 *
          S.normal.sextic.scale.regular4
    GCD369CubeHahnRegular.constantCoeff P = 27648 * S.u * S.v := by
  dsimp only
  simp only [map_sub, map_mul, map_ofNat]
  change
    41472 * S.normal.sextic.scale.leading1 -
      13824 * S.normal.sextic.scale.leading3 *
        S.normal.sextic.scale.leading4 = _
  rw [S.ha1, S.ha3, S.ha4]
  ring

theorem c4LoadPoly2_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      124416 * S.normal.sextic.scale.regular0 -
        41472 * S.normal.sextic.scale.regular2 *
          S.normal.sextic.scale.regular4 -
        20736 * S.normal.sextic.scale.regular3 ^ 2 +
        9216 * S.normal.sextic.scale.regular4 ^ 3
    GCD369CubeHahnRegular.constantCoeff P =
      -9216 * S.u ^ 3 + 41472 * S.v ^ 2 := by
  dsimp only
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change
    124416 * S.normal.sextic.scale.leading0 -
      41472 * S.normal.sextic.scale.leading2 *
        S.normal.sextic.scale.leading4 -
      20736 * S.normal.sextic.scale.leading3 ^ 2 +
      9216 * S.normal.sextic.scale.leading4 ^ 3 = _
  rw [S.ha0, S.ha2, S.ha3, S.ha4]
  ring

theorem c4LoadPoly3_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      -27648 * S.normal.sextic.scale.regular1 *
          S.normal.sextic.scale.regular4 -
        55296 * S.normal.sextic.scale.regular2 *
          S.normal.sextic.scale.regular3 +
        27648 * S.normal.sextic.scale.regular3 *
          S.normal.sextic.scale.regular4 ^ 2
    GCD369CubeHahnRegular.constantCoeff P = 0 := by
  dsimp only
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
  change
    -27648 * S.normal.sextic.scale.leading1 *
        S.normal.sextic.scale.leading4 -
      55296 * S.normal.sextic.scale.leading2 *
        S.normal.sextic.scale.leading3 +
      27648 * S.normal.sextic.scale.leading3 *
        S.normal.sextic.scale.leading4 ^ 2 = 0
  rw [S.ha1, S.ha2, S.ha3, S.ha4]
  ring

theorem c4LoadPoly4_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      -186624 * S.normal.sextic.scale.regular1 *
          S.normal.sextic.scale.regular3 -
        186624 * S.normal.sextic.scale.regular2 ^ 2 +
        124416 * S.normal.sextic.scale.regular2 *
          S.normal.sextic.scale.regular4 ^ 2 +
        124416 * S.normal.sextic.scale.regular3 ^ 2 *
          S.normal.sextic.scale.regular4 -
        20736 * S.normal.sextic.scale.regular4 ^ 4
    GCD369CubeHahnRegular.constantCoeff P =
      -20736 * S.u ^ 4 + 248832 * S.u * S.v ^ 2 := by
  dsimp only
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
  change
    -186624 * S.normal.sextic.scale.leading1 *
        S.normal.sextic.scale.leading3 -
      186624 * S.normal.sextic.scale.leading2 ^ 2 +
      124416 * S.normal.sextic.scale.leading2 *
        S.normal.sextic.scale.leading4 ^ 2 +
      124416 * S.normal.sextic.scale.leading3 ^ 2 *
        S.normal.sextic.scale.leading4 -
      20736 * S.normal.sextic.scale.leading4 ^ 4 = _
  rw [S.ha1, S.ha2, S.ha3, S.ha4]
  ring

end GCD369CubeHahnCommonValueData

theorem GCD369Cube_c4LoadRemainders_doubleRoot
    {R : Type*} [CommRing R] (r : R) :
    (27648 * (-3 * r ^ 2) * (2 * r ^ 3) = -165888 * r ^ 5) ∧
    (-9216 * (-3 * r ^ 2) ^ 3 + 41472 * (2 * r ^ 3) ^ 2 =
      414720 * r ^ 6) ∧
    ((0 : R) = 0) ∧
    (-20736 * (-3 * r ^ 2) ^ 4 +
        248832 * (-3 * r ^ 2) * (2 * r ^ 3) ^ 2 =
      -4665600 * r ^ 8) := by
  refine ⟨?_, ?_, rfl, ?_⟩ <;> ring

#print axioms GCD369CubeHahnCommonValueData.c4LoadPoly1_constantCoeff
#print axioms GCD369CubeHahnCommonValueData.c4LoadPoly2_constantCoeff
#print axioms GCD369CubeHahnCommonValueData.c4LoadPoly3_constantCoeff
#print axioms GCD369CubeHahnCommonValueData.c4LoadPoly4_constantCoeff
#print axioms GCD369Cube_c4LoadRemainders_doubleRoot
