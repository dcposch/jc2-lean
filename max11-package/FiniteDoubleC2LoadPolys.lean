import FiniteCommonSource

/-! # Pure `c2` load polynomials on the common cubic

The four integral `c2` numerators split as the zero-high Faber rows plus a
weight-seven load polynomial in the scaled sextic coordinates.  This file
records the leading residues of those load polynomials under the common-cubic
normalization, and their specialization on the double-root sheet
`u = -3 r^2`, `v = 2 r^3`.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- Leading residue of the first integral `c2` polynomial on the common
cubic. -/
theorem c2LoadPoly1_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      20736 * S.normal.sextic.scale.regular3
    GCD369CubeHahnRegular.constantCoeff P = 41472 * S.v := by
  dsimp only
  simp only [map_mul, map_ofNat]
  change 20736 * S.normal.sextic.scale.leading3 = _
  rw [S.ha3]
  ring

/-- Leading residue of the second integral `c2` polynomial on the common
cubic. -/
theorem c2LoadPoly2_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      62208 * S.normal.sextic.scale.regular2 -
        20736 * S.normal.sextic.scale.regular4 ^ 2
    GCD369CubeHahnRegular.constantCoeff P = -20736 * S.u ^ 2 := by
  dsimp only
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  change
    62208 * S.normal.sextic.scale.leading2 -
      20736 * S.normal.sextic.scale.leading4 ^ 2 = _
  rw [S.ha2, S.ha4]
  ring

/-- The third integral `c2` polynomial has vanishing residue on the common
cubic. -/
theorem c2LoadPoly3_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      82944 * S.normal.sextic.scale.regular1 -
        41472 * S.normal.sextic.scale.regular3 *
          S.normal.sextic.scale.regular4
    GCD369CubeHahnRegular.constantCoeff P = 0 := by
  dsimp only
  simp only [map_sub, map_mul, map_ofNat]
  change
    82944 * S.normal.sextic.scale.leading1 -
      41472 * S.normal.sextic.scale.leading3 *
        S.normal.sextic.scale.leading4 = 0
  rw [S.ha1, S.ha3, S.ha4]
  ring

/-- Leading residue of the fourth integral `c2` polynomial on the common
cubic. -/
theorem c2LoadPoly4_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      559872 * S.normal.sextic.scale.regular0 -
        186624 * S.normal.sextic.scale.regular2 *
          S.normal.sextic.scale.regular4 -
        93312 * S.normal.sextic.scale.regular3 ^ 2 +
        41472 * S.normal.sextic.scale.regular4 ^ 3
    GCD369CubeHahnRegular.constantCoeff P =
      -41472 * S.u ^ 3 + 186624 * S.v ^ 2 := by
  dsimp only
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change
    559872 * S.normal.sextic.scale.leading0 -
      186624 * S.normal.sextic.scale.leading2 *
        S.normal.sextic.scale.leading4 -
      93312 * S.normal.sextic.scale.leading3 ^ 2 +
      41472 * S.normal.sextic.scale.leading4 ^ 3 = _
  rw [S.ha0, S.ha2, S.ha3, S.ha4]
  ring

end GCD369CubeHahnCommonValueData

/-- The four pure `c2`-load remainders on the double-root sheet
`u = -3 r^2`, `v = 2 r^3`.  Row three vanishes identically; the surviving
constants are `82944 r^3`, `-186624 r^4`, and `1866240 r^6`. -/
theorem GCD369Cube_c2LoadRemainders_doubleRoot
    {R : Type*} [CommRing R] (r : R) :
    (41472 * (2 * r ^ 3) = 82944 * r ^ 3) ∧
    (-20736 * (-3 * r ^ 2) ^ 2 = -186624 * r ^ 4) ∧
    ((0 : R) = 0) ∧
    (-41472 * (-3 * r ^ 2) ^ 3 + 186624 * (2 * r ^ 3) ^ 2 =
      1866240 * r ^ 6) := by
  refine ⟨?_, ?_, rfl, ?_⟩ <;> ring

#print axioms GCD369CubeHahnCommonValueData.c2LoadPoly1_constantCoeff
#print axioms GCD369CubeHahnCommonValueData.c2LoadPoly2_constantCoeff
#print axioms GCD369CubeHahnCommonValueData.c2LoadPoly3_constantCoeff
#print axioms GCD369CubeHahnCommonValueData.c2LoadPoly4_constantCoeff
#print axioms GCD369Cube_c2LoadRemainders_doubleRoot
