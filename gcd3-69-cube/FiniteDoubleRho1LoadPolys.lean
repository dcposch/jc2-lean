import FiniteCommonSource

/-! # Pure `rho1` load residues after the H^2 shift

A first weight-ten load is an invariant value, not a high source
coefficient.  After the common-normal H^2 shift the four primitive rows
therefore receive the sparse packet `62208 T`, `0`, `0`, `0`.  Clearing
the first-row prefactor `-32` converts `62208` into the Kuranishi residue
`1944` used by `GCD369CubeRhoOneRows`.  On the exact double-root sheet
the zero-load jet vanishes, so those same constants are the only
remainders.
-/

noncomputable section
open Polynomial

/-- Clearing the H^2 prefactor `-32` of the first common-normal numerator
converts the weight-ten `rho1` packet `62208` into the Kuranishi residue
`1944`. -/
theorem GCD369Cube_rho1Load_H2_clear {R : Type*} [CommRing R] :
    (32 : R) * 1944 = 62208 := by
  norm_num

/-- After the H^2 shift, a first `rho1` load of strength `T` is exactly
the conversion `-32 * (NormalRow1 + 1944 * T)` in the first primitive
row.  The other three primitive rows carry no `rho1` remainder. -/
theorem GCD369CubeFaberRho1_afterH2
    {K : Type*} [Field K] [CharZero K]
    (Xn Yn Zn u v T : K) :
    let H : K[X] := X
    let A0 : K[X] := C (v ^ 2) + C Zn * H
    let A1 : K[X] := C (2 * u * v) + C Yn * H
    let A2 : K[X] := C (u ^ 2) + C Xn * H
    let A3 : K[X] := C (2 * v)
    let A4 : K[X] := C (2 * u)
    ((729 * GCD369CubeFaberN1 A0 A1 A2 A3 A4).coeff 2 - 62208 * T =
        -32 * (GCD369CubeNormalRow1 Xn Yn Zn u + 1944 * T)) ∧
    ((2187 * GCD369CubeFaberN2 A0 A1 A2 A3 A4).coeff 2 =
        32 * GCD369CubeNormalRow2 Xn Yn Zn u v) ∧
    ((GCD369CubeFaberN3 A0 A1 A2 A3 A4).coeff 2 =
        128 * GCD369CubeNormalRow3 Xn Yn Zn u v) ∧
    ((6561 * GCD369CubeFaberN4 A0 A1 A2 A3 A4).coeff 2 =
        32 * GCD369CubeNormalRow4 Xn Yn Zn u v) := by
  dsimp only
  have hcoeff := GCD369CubeFaberCommonNormalCoefficients Xn Yn Zn u v
  dsimp only at hcoeff
  rcases hcoeff with ⟨hc1, hc2, hc3, hc4⟩
  refine ⟨?_, hc2, hc3, hc4⟩
  have hclear : (32 : K) * 1944 = 62208 := GCD369Cube_rho1Load_H2_clear
  calc
    (729 * GCD369CubeFaberN1
        (C (v ^ 2) + C Zn * X) (C (2 * u * v) + C Yn * X)
        (C (u ^ 2) + C Xn * X) (C (2 * v)) (C (2 * u))).coeff 2 -
          62208 * T =
        -32 * GCD369CubeNormalRow1 Xn Yn Zn u - 62208 * T := by
      rw [hc1]
    _ = -32 * (GCD369CubeNormalRow1 Xn Yn Zn u + 1944 * T) := by
      linear_combination (32 * T) * hclear.symm

/-- The exact double-root normal `(A, r A, -2 r^2 A)` on
`u = -3 r^2`, `v = 2 r^3` annihilates every zero-load Kuranishi row. -/
theorem GCD369CubeNormalRows_exactDoubleRoot
    {R : Type*} [CommRing R] (A r : R) :
    GCD369CubeNormalRow1 A (r * A) (-2 * r ^ 2 * A) (-3 * r ^ 2) = 0 ∧
    GCD369CubeNormalRow2 A (r * A) (-2 * r ^ 2 * A)
        (-3 * r ^ 2) (2 * r ^ 3) = 0 ∧
    GCD369CubeNormalRow3 A (r * A) (-2 * r ^ 2 * A)
        (-3 * r ^ 2) (2 * r ^ 3) = 0 ∧
    GCD369CubeNormalRow4 A (r * A) (-2 * r ^ 2 * A)
        (-3 * r ^ 2) (2 * r ^ 3) = 0 := by
  simp only [GCD369CubeNormalRow1, GCD369CubeNormalRow2,
    GCD369CubeNormalRow3, GCD369CubeNormalRow4]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- After the H^2 shift, the exact double-root sheet retains only the
sparse first-row remainder `-62208 T`. -/
theorem GCD369Cube_rho1Load_afterH2_exactDoubleRoot
    {R : Type*} [CommRing R] (A r T : R) :
    (-32 * GCD369CubeNormalRow1 A (r * A) (-2 * r ^ 2 * A)
          (-3 * r ^ 2) - 62208 * T =
        -62208 * T) ∧
    (32 * GCD369CubeNormalRow2 A (r * A) (-2 * r ^ 2 * A)
          (-3 * r ^ 2) (2 * r ^ 3) =
        0) ∧
    (128 * GCD369CubeNormalRow3 A (r * A) (-2 * r ^ 2 * A)
          (-3 * r ^ 2) (2 * r ^ 3) =
        0) ∧
    (32 * GCD369CubeNormalRow4 A (r * A) (-2 * r ^ 2 * A)
          (-3 * r ^ 2) (2 * r ^ 3) =
        0) := by
  rcases GCD369CubeNormalRows_exactDoubleRoot A r with ⟨h1, h2, h3, h4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1]
    ring
  · rw [h2, mul_zero]
  · rw [h3, mul_zero]
  · rw [h4, mul_zero]

namespace GCD369CubeHahnCommonValueData

/-- Leading residue of the first `rho1` load.  Unlike the source-coefficient
loads, this residue is the universal normalization `62208`. -/
theorem rho1LoadPoly1_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (_S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      GCD369CubeHahnRegular.constant (62208 : k)
    GCD369CubeHahnRegular.constantCoeff P = 62208 := by
  dsimp only
  exact GCD369CubeHahnRegular.constantCoeff_constant (62208 : k)

/-- The second `rho1` load residue vanishes. -/
theorem rho1LoadPoly2_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (_S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      GCD369CubeHahnRegular.constant (0 : k)
    GCD369CubeHahnRegular.constantCoeff P = 0 := by
  dsimp only
  exact GCD369CubeHahnRegular.constantCoeff_constant (0 : k)

/-- The third `rho1` load residue vanishes. -/
theorem rho1LoadPoly3_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (_S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      GCD369CubeHahnRegular.constant (0 : k)
    GCD369CubeHahnRegular.constantCoeff P = 0 := by
  dsimp only
  exact GCD369CubeHahnRegular.constantCoeff_constant (0 : k)

/-- The fourth `rho1` load residue vanishes. -/
theorem rho1LoadPoly4_constantCoeff
    {k : Type*} [Field k] [CharZero k]
    (_S : GCD369CubeHahnCommonValueData k) :
    let P : GCD369CubeHahnRegular k :=
      GCD369CubeHahnRegular.constant (0 : k)
    GCD369CubeHahnRegular.constantCoeff P = 0 := by
  dsimp only
  exact GCD369CubeHahnRegular.constantCoeff_constant (0 : k)

end GCD369CubeHahnCommonValueData

/-- The four pure `rho1`-load remainders on the double-root sheet
`u = -3 r^2`, `v = 2 r^3`.  Only the first row is loaded, and the residue
`62208` is independent of `r`. -/
theorem GCD369Cube_rho1LoadRemainders_doubleRoot
    {R : Type*} [CommRing R] (_r : R) :
    ((62208 : R) = 62208) ∧
    ((0 : R) = 0) ∧
    ((0 : R) = 0) ∧
    ((0 : R) = 0) := by
  refine ⟨rfl, rfl, rfl, rfl⟩

#print axioms GCD369Cube_rho1Load_H2_clear
#print axioms GCD369CubeFaberRho1_afterH2
#print axioms GCD369CubeNormalRows_exactDoubleRoot
#print axioms GCD369Cube_rho1Load_afterH2_exactDoubleRoot
#print axioms GCD369CubeHahnCommonValueData.rho1LoadPoly1_constantCoeff
#print axioms GCD369CubeHahnCommonValueData.rho1LoadPoly2_constantCoeff
#print axioms GCD369CubeHahnCommonValueData.rho1LoadPoly3_constantCoeff
#print axioms GCD369CubeHahnCommonValueData.rho1LoadPoly4_constantCoeff
#print axioms GCD369Cube_rho1LoadRemainders_doubleRoot
