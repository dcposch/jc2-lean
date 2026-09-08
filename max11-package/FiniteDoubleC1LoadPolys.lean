import FiniteCommonSource

/-! # Pure `c1` load polynomials on the common cubic

The four integral `c1` numerators split as the zero-high Faber rows plus a
weight-eight load polynomial in the scaled sextic coordinates.  This file
records the leading residues of those load polynomials under the common-cubic
normalization, and their specialization on the double-root sheet
`u = -3 r^2`, `v = 2 r^3`.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- Leading residue of the first integral `c1` polynomial on the common
cubic. -/
theorem c1LoadPoly1_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      10368 * S.normal.sextic.scale.regular4
    GCD369CubeHahnRegular.constantCoeff P = 20736 * S.u := by
  dsimp only
  simp only [map_mul, map_ofNat]
  change 10368 * S.normal.sextic.scale.leading4 = _
  rw [S.ha4]
  ring

/-- Leading residue of the second integral `c1` polynomial on the common
cubic. -/
theorem c1LoadPoly2_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      31104 * S.normal.sextic.scale.regular3
    GCD369CubeHahnRegular.constantCoeff P = 62208 * S.v := by
  dsimp only
  simp only [map_mul, map_ofNat]
  change 31104 * S.normal.sextic.scale.leading3 = _
  rw [S.ha3]
  ring

/-- The third integral `c1` polynomial has vanishing residue on the common
cubic. -/
theorem c1LoadPoly3_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      41472 * S.normal.sextic.scale.regular2 -
        10368 * S.normal.sextic.scale.regular4 ^ 2
    GCD369CubeHahnRegular.constantCoeff P = 0 := by
  dsimp only
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  change
    41472 * S.normal.sextic.scale.leading2 -
      10368 * S.normal.sextic.scale.leading4 ^ 2 = 0
  rw [S.ha2, S.ha4]
  ring

/-- Leading residue of the fourth integral `c1` polynomial on the common
cubic. -/
theorem c1LoadPoly4_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      279936 * S.normal.sextic.scale.regular1 -
        93312 * S.normal.sextic.scale.regular3 *
          S.normal.sextic.scale.regular4
    GCD369CubeHahnRegular.constantCoeff P = 186624 * S.u * S.v := by
  dsimp only
  simp only [map_sub, map_mul, map_ofNat]
  change
    279936 * S.normal.sextic.scale.leading1 -
      93312 * S.normal.sextic.scale.leading3 *
        S.normal.sextic.scale.leading4 = _
  rw [S.ha1, S.ha3, S.ha4]
  ring

end GCD369CubeHahnCommonValueData

/-- The four pure `c1`-load remainders on the double-root sheet
`u = -3 r^2`, `v = 2 r^3`.  Row three vanishes identically; the surviving
constants are `-62208 r^2`, `124416 r^3`, and `-1119744 r^5`. -/
theorem GCD369Cube_c1LoadRemainders_doubleRoot
    {R : Type*} [CommRing R] (r : R) :
    (20736 * (-3 * r ^ 2) = -62208 * r ^ 2) ∧
    (62208 * (2 * r ^ 3) = 124416 * r ^ 3) ∧
    ((0 : R) = 0) ∧
    (186624 * (-3 * r ^ 2) * (2 * r ^ 3) = -1119744 * r ^ 5) := by
  refine ⟨?_, ?_, rfl, ?_⟩ <;> ring

#print axioms GCD369CubeHahnCommonValueData.c1LoadPoly1_constantCoeff
#print axioms GCD369CubeHahnCommonValueData.c1LoadPoly2_constantCoeff
#print axioms GCD369CubeHahnCommonValueData.c1LoadPoly3_constantCoeff
#print axioms GCD369CubeHahnCommonValueData.c1LoadPoly4_constantCoeff
#print axioms GCD369Cube_c1LoadRemainders_doubleRoot
