import FiniteLoadAnnihilation

/-! # Terminal fifth Faber numerator on the common-cubic sheet

The first four denominator-cleared Faber rows are source equations at a
finite common-cubic pole.  The fifth row is the terminal invariant: current
source data do not constrain `GCD369CubeFaberFullN5` to vanish, and the
identities below are therefore exact polynomial expansions rather than
vanishing obstructions.

Its quadratic jet is a linear combination of the first two normal rows, so
it cannot supply a new quadratic condition.  After specializing to the
double root a cubic remainder survives, including along the residual
half-scale direction with arbitrary second corrections, but that remainder
is not forced to vanish by the present finite-place source package.
-/

noncomputable section
open Polynomial

/-- Fifth universal quadratic row on the common-cubic normal cone.  This is
the exact `h ^ 2` coefficient of the zero-high terminal numerator, up to
the displayed constant `559872`. -/
def GCD369CubeNormalRow5 {R : Type*} [CommRing R]
    (X Y Z U V : R) : R :=
  -U ^ 3 * X ^ 2 + 3 * V ^ 2 * X ^ 2 + 6 * U * V * X * Y +
    2 * U ^ 2 * X * Z + U ^ 2 * Y ^ 2 - 6 * V * Y * Z

/-- Cubic remainder of the zero-high terminal numerator.  It is independent
of `V`. -/
def GCD369CubeNormalRow5Cubic {R : Type*} [CommRing R]
    (X Y Z U : R) : R :=
  U * X ^ 3 - X ^ 2 * Z - 2 * X * Y ^ 2

/-- Coefficient of the pure `d` load in the terminal numerator. -/
def GCD369CubeFaberFullN5_dCoeff {R : Type*} [CommRing R]
    (a0 a1 a2 a3 a4 : R) : R :=
  -995328 * a0 * a1 * a4 - 995328 * a0 * a2 * a3 +
    580608 * a0 * a3 * a4 ^ 2 - 995328 * a1 ^ 2 * a3 -
    995328 * a1 * a2 ^ 2 + 912384 * a1 * a2 * a4 ^ 2 +
    995328 * a1 * a3 ^ 2 * a4 - 156672 * a1 * a4 ^ 4 +
    995328 * a2 ^ 2 * a3 * a4 + 331776 * a2 * a3 ^ 3 -
    681984 * a2 * a3 * a4 ^ 3 - 359424 * a3 ^ 3 * a4 ^ 2 +
    107520 * a3 * a4 ^ 5

/-- The fifth quadratic row is not an independent constraint: it is the
displayed combination of the first two normal rows. -/
theorem GCD369CubeNormalRow5_of_row1_row2
    {R : Type*} [CommRing R] (X Y Z U V : R) :
    U ^ 2 * GCD369CubeNormalRow1 X Y Z U +
        V * GCD369CubeNormalRow2 X Y Z U V +
        729 * GCD369CubeNormalRow5 X Y Z U V = 0 := by
  dsimp only [GCD369CubeNormalRow1, GCD369CubeNormalRow2,
    GCD369CubeNormalRow5]
  ring

/-- The fifth quadratic row commutes with ring maps. -/
theorem GCD369CubeNormalRow5_map
    {R L : Type*} [CommRing R] [CommRing L] (f : R →+* L)
    (X Y Z U V : R) :
    f (GCD369CubeNormalRow5 X Y Z U V) =
      GCD369CubeNormalRow5 (f X) (f Y) (f Z) (f U) (f V) := by
  simp only [GCD369CubeNormalRow5, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat]

/-- The cubic remainder commutes with ring maps. -/
theorem GCD369CubeNormalRow5Cubic_map
    {R L : Type*} [CommRing R] [CommRing L] (f : R →+* L)
    (X Y Z U : R) :
    f (GCD369CubeNormalRow5Cubic X Y Z U) =
      GCD369CubeNormalRow5Cubic (f X) (f Y) (f Z) (f U) := by
  simp only [GCD369CubeNormalRow5Cubic, map_sub, map_mul, map_pow,
    map_ofNat]

/-- The terminal numerator commutes with ring maps. -/
theorem GCD369CubeFaberFullN5_map
    {R L : Type*} [CommRing R] [CommRing L] (f : R →+* L)
    (a0 a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1 : R) :
    f (GCD369CubeFaberFullN5 a0 a1 a2 a3 a4 d c7 c5 c4 c3 c2 c1) =
      GCD369CubeFaberFullN5 (f a0) (f a1) (f a2) (f a3) (f a4)
        (f d) (f c7) (f c5) (f c4) (f c3) (f c2) (f c1) := by
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]

/-- Isolating the pure `d` load from every later high parameter. -/
theorem GCD369CubeFaberFullN5_d_specialize
    {R : Type*} [CommRing R] (a0 a1 a2 a3 a4 d : R) :
    GCD369CubeFaberFullN5 a0 a1 a2 a3 a4 d 0 0 0 0 0 0 =
      GCD369CubeFaberFullN5 a0 a1 a2 a3 a4 0 0 0 0 0 0 0 +
        d * GCD369CubeFaberFullN5_dCoeff a0 a1 a2 a3 a4 := by
  simp only [GCD369CubeFaberFullN5_dCoeff]
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Exact expansion of the terminal numerator along the common-cubic chart
`a0 = V^2 + h Z`, `a1 = 2 U V + h Y`, `a2 = U^2 + h X`, `a3 = 2 V`,
`a4 = 2 U`, with a pure `d` load and every later high parameter zero.
There are no terms beyond `h ^ 3`. -/
theorem GCD369CubeFaberFullN5_d_expansion
    {R : Type*} [CommRing R] (X Y Z U V h d : R) :
    GCD369CubeFaberFullN5
        (V ^ 2 + h * Z) (2 * U * V + h * Y) (U ^ 2 + h * X)
        (2 * V) (2 * U) d 0 0 0 0 0 0 =
      559872 * h ^ 2 * GCD369CubeNormalRow5 X Y Z U V +
      839808 * h ^ 3 * GCD369CubeNormalRow5Cubic X Y Z U +
      245760 * U ^ 2 * V * (U ^ 3 - 9 * V ^ 2) * d +
      73728 * h *
        (2 * U ^ 4 * Y + 5 * U ^ 3 * V * X - 27 * U * V ^ 2 * Y +
          9 * V ^ 3 * X - 18 * U ^ 2 * V * Z) * d +
      331776 * h ^ 2 *
        (5 * U ^ 2 * X * Y + 6 * U * V * X ^ 2 - 6 * U * Y * Z -
          6 * V * Y ^ 2 - 6 * V * X * Z) * d -
      995328 * h ^ 3 * X ^ 2 * Y * d := by
  simp only [GCD369CubeNormalRow5, GCD369CubeNormalRow5Cubic]
  ring

/-- Zero-high specialization of the chart expansion. -/
theorem GCD369CubeFaberFullN5_zeroHigh_expansion
    {R : Type*} [CommRing R] (X Y Z U V h : R) :
    GCD369CubeFaberFullN5
        (V ^ 2 + h * Z) (2 * U * V + h * Y) (U ^ 2 + h * X)
        (2 * V) (2 * U) 0 0 0 0 0 0 0 =
      559872 * h ^ 2 * GCD369CubeNormalRow5 X Y Z U V +
      839808 * h ^ 3 * GCD369CubeNormalRow5Cubic X Y Z U := by
  simpa using GCD369CubeFaberFullN5_d_expansion X Y Z U V h 0

/-- Polynomial form of the zero-high chart expansion, matching the first
four common-normal numerator identities. -/
theorem GCD369CubeFaberFullN5_commonNormalNumerator
    {R : Type*} [CommRing R] (Xn Yn Zn u v : R) :
    let H : R[X] := X
    let A0 : R[X] := C (v ^ 2) + C Zn * H
    let A1 : R[X] := C (2 * u * v) + C Yn * H
    let A2 : R[X] := C (u ^ 2) + C Xn * H
    let A3 : R[X] := C (2 * v)
    let A4 : R[X] := C (2 * u)
    GCD369CubeFaberFullN5 A0 A1 A2 A3 A4 0 0 0 0 0 0 0 =
      C (559872 * GCD369CubeNormalRow5 Xn Yn Zn u v) * H ^ 2 +
      C (839808 * GCD369CubeNormalRow5Cubic Xn Yn Zn u) * H ^ 3 := by
  dsimp only
  have h := GCD369CubeFaberFullN5_zeroHigh_expansion
    (C Xn) (C Yn) (C Zn) (C u) (C v) X
  have ha0 : C (v ^ 2) + C Zn * X = C v ^ 2 + X * C Zn := by
    rw [C_pow, mul_comm (C Zn)]
  have ha1 : C (2 * u * v) + C Yn * X =
      2 * C u * C v + X * C Yn := by
    rw [map_mul, map_mul, map_ofNat, mul_comm (C Yn)]
  have ha2 : C (u ^ 2) + C Xn * X = C u ^ 2 + X * C Xn := by
    rw [C_pow, mul_comm (C Xn)]
  have ha3 : C (2 * v) = 2 * C v := by
    rw [map_mul, map_ofNat]
  have ha4 : C (2 * u) = 2 * C u := by
    rw [map_mul, map_ofNat]
  rw [ha0, ha1, ha2, ha3, ha4, h,
    ← GCD369CubeNormalRow5_map (C : R →+* R[X]) Xn Yn Zn u v,
    ← GCD369CubeNormalRow5Cubic_map (C : R →+* R[X]) Xn Yn Zn u]
  simp only [map_mul, map_ofNat]
  ring

/-- Quadratic and cubic coefficients of the zero-high terminal numerator. -/
theorem GCD369CubeFaberFullN5_commonNormalCoefficients
    {R : Type*} [CommRing R] (Xn Yn Zn u v : R) :
    let H : R[X] := X
    let A0 : R[X] := C (v ^ 2) + C Zn * H
    let A1 : R[X] := C (2 * u * v) + C Yn * H
    let A2 : R[X] := C (u ^ 2) + C Xn * H
    let A3 : R[X] := C (2 * v)
    let A4 : R[X] := C (2 * u)
    (GCD369CubeFaberFullN5 A0 A1 A2 A3 A4 0 0 0 0 0 0 0).coeff 2 =
        559872 * GCD369CubeNormalRow5 Xn Yn Zn u v ∧
    (GCD369CubeFaberFullN5 A0 A1 A2 A3 A4 0 0 0 0 0 0 0).coeff 3 =
        839808 * GCD369CubeNormalRow5Cubic Xn Yn Zn u := by
  dsimp only
  have h := GCD369CubeFaberFullN5_commonNormalNumerator Xn Yn Zn u v
  dsimp only at h
  constructor
  · rw [h]
    simp only [coeff_add, coeff_C_mul_X_pow]
    norm_num
  · rw [h]
    simp only [coeff_add, coeff_C_mul_X_pow]
    norm_num

/-- On the cubic sheet itself, the pure `d` remainder is this displayed
multiple of `U^2 V (U^3 - 9 V^2)`. -/
theorem GCD369CubeFaberFullN5_d_cubicSheet
    {R : Type*} [CommRing R] (U V d : R) :
    GCD369CubeFaberFullN5 (V ^ 2) (2 * U * V) (U ^ 2) (2 * V) (2 * U)
        d 0 0 0 0 0 0 =
      245760 * U ^ 2 * V * (U ^ 3 - 9 * V ^ 2) * d := by
  simpa using GCD369CubeFaberFullN5_d_expansion 0 0 0 U V 0 d

/-- Double-root specialization of that cubic-sheet `d` remainder. -/
theorem GCD369CubeFaberFullN5_d_doubleRootSheet
    {R : Type*} [CommRing R] (r d : R) :
    GCD369CubeFaberFullN5
        ((2 * r ^ 3) ^ 2) (2 * (-3 * r ^ 2) * (2 * r ^ 3))
        ((-3 * r ^ 2) ^ 2) (2 * (2 * r ^ 3)) (2 * (-3 * r ^ 2))
        d 0 0 0 0 0 0 =
      -278691840 * r ^ 13 * d := by
  rw [GCD369CubeFaberFullN5_d_cubicSheet]
  ring

/-- If the pure `d` load annihilates the three normal coordinates, every
mixed `d`-normal term drops and the terminal numerator is its zero-high
chart expansion plus the cubic-sheet `d` remainder. -/
theorem GCD369CubeFaberFullN5_eq_zeroHigh_of_d_annihilates_normals
    {R : Type*} [CommRing R] (X Y Z U V h d : R)
    (hd : d * X = 0 ∧ d * Y = 0 ∧ d * Z = 0) :
    GCD369CubeFaberFullN5
        (V ^ 2 + h * Z) (2 * U * V + h * Y) (U ^ 2 + h * X)
        (2 * V) (2 * U) d 0 0 0 0 0 0 =
      559872 * h ^ 2 * GCD369CubeNormalRow5 X Y Z U V +
      839808 * h ^ 3 * GCD369CubeNormalRow5Cubic X Y Z U +
      245760 * U ^ 2 * V * (U ^ 3 - 9 * V ^ 2) * d := by
  rcases hd with ⟨hdX, hdY, hdZ⟩
  rw [GCD369CubeFaberFullN5_d_expansion]
  linear_combination
    (73728 * h * (5 * U ^ 3 * V + 9 * V ^ 3) +
      331776 * h ^ 2 * (5 * U ^ 2 * Y + 6 * U * V * X - 6 * V * Z) -
      995328 * h ^ 3 * X * Y) * hdX +
    (73728 * h * (2 * U ^ 4 - 27 * U * V ^ 2) +
      331776 * h ^ 2 * (-6 * U * Z - 6 * V * Y)) * hdY +
    (73728 * h * (-18 * U ^ 2 * V)) * hdZ

/-- The double-root first jet lies on the fifth quadratic row. -/
theorem GCD369CubeNormalRow5_doubleRoot
    {R : Type*} [CommRing R] (r A : R) :
    GCD369CubeNormalRow5 A (r * A) (-2 * r ^ 2 * A)
        (-3 * r ^ 2) (2 * r ^ 3) = 0 := by
  dsimp only [GCD369CubeNormalRow5]
  ring

/-- Its cubic remainder is `-3 r^2 A^3`. -/
theorem GCD369CubeNormalRow5Cubic_doubleRoot
    {R : Type*} [CommRing R] (r A : R) :
    GCD369CubeNormalRow5Cubic A (r * A) (-2 * r ^ 2 * A) (-3 * r ^ 2) =
      -3 * r ^ 2 * A ^ 3 := by
  dsimp only [GCD369CubeNormalRow5Cubic]
  ring

/-- On the residual half-scale kernel direction `C = -r B`, the fifth
quadratic row is `21 r^4 B^2`. -/
theorem GCD369CubeNormalRow5_doubleRoot_kernel
    {R : Type*} [CommRing R] (r A B : R) :
    GCD369CubeNormalRow5 A (r * A + B) (-2 * r ^ 2 * A - r * B)
        (-3 * r ^ 2) (2 * r ^ 3) =
      21 * r ^ 4 * B ^ 2 := by
  dsimp only [GCD369CubeNormalRow5]
  ring

/-- Unlike the third quadratic row, the double-root first jet is not in the
radical of the fifth row: a second correction contributes a bilinear
`h`-term `6 r^4 A (r^2 X1 + r Y1 + Z1)`. -/
theorem GCD369CubeNormalRow5_doubleRoot_secondCorrection
    {R : Type*} [CommRing R] (r A X1 Y1 Z1 h : R) :
    GCD369CubeNormalRow5
        (A + h * X1) (r * A + h * Y1) (-2 * r ^ 2 * A + h * Z1)
        (-3 * r ^ 2) (2 * r ^ 3) =
      6 * r ^ 4 * A * (r ^ 2 * X1 + r * Y1 + Z1) * h +
        h ^ 2 * GCD369CubeNormalRow5 X1 Y1 Z1
          (-3 * r ^ 2) (2 * r ^ 3) := by
  dsimp only [GCD369CubeNormalRow5]
  ring

/-- Zero-high terminal numerator on the exact double-root first jet.  The
quadratic row vanishes and the cubic remainder is `-2519424 r^2 A^3`. -/
theorem GCD369CubeFaberFullN5_doubleRoot
    {R : Type*} [CommRing R] (r A h : R) :
    GCD369CubeFaberFullN5
        ((2 * r ^ 3) ^ 2 + h * (-2 * r ^ 2 * A))
        (2 * (-3 * r ^ 2) * (2 * r ^ 3) + h * (r * A))
        ((-3 * r ^ 2) ^ 2 + h * A)
        (2 * (2 * r ^ 3)) (2 * (-3 * r ^ 2))
        0 0 0 0 0 0 0 =
      -2519424 * r ^ 2 * A ^ 3 * h ^ 3 := by
  rw [GCD369CubeFaberFullN5_zeroHigh_expansion,
    GCD369CubeNormalRow5_doubleRoot,
    GCD369CubeNormalRow5Cubic_doubleRoot]
  ring

/-- Zero-high terminal numerator along the residual kernel direction, with
no second correction. -/
theorem GCD369CubeFaberFullN5_doubleRoot_kernelResidual
    {R : Type*} [CommRing R] (r A B h : R) :
    GCD369CubeFaberFullN5
        ((2 * r ^ 3) ^ 2 + h * (-2 * r ^ 2 * A - r * B))
        (2 * (-3 * r ^ 2) * (2 * r ^ 3) + h * (r * A + B))
        ((-3 * r ^ 2) ^ 2 + h * A)
        (2 * (2 * r ^ 3)) (2 * (-3 * r ^ 2))
        0 0 0 0 0 0 0 =
      11757312 * r ^ 4 * B ^ 2 * h ^ 2 +
        839808 * h ^ 3 *
          (-2 * A * B ^ 2 - 3 * r * A ^ 2 * B - 3 * r ^ 2 * A ^ 3) := by
  rw [GCD369CubeFaberFullN5_zeroHigh_expansion,
    GCD369CubeNormalRow5_doubleRoot_kernel]
  dsimp only [GCD369CubeNormalRow5Cubic]
  ring

/-- Zero-high terminal numerator on the residual kernel direction, allowing
an arbitrary second correction `(P, Q, S)`.  This is the general chart
identity evaluated at that jet; it is not a vanishing constraint. -/
theorem GCD369CubeFaberFullN5_doubleRoot_secondCorrections
    {R : Type*} [CommRing R] (r A B P Q S h : R) :
    GCD369CubeFaberFullN5
        ((2 * r ^ 3) ^ 2 +
          h * (-2 * r ^ 2 * A - r * B + h * S))
        (2 * (-3 * r ^ 2) * (2 * r ^ 3) +
          h * (r * A + B + h * Q))
        ((-3 * r ^ 2) ^ 2 + h * (A + h * P))
        (2 * (2 * r ^ 3)) (2 * (-3 * r ^ 2))
        0 0 0 0 0 0 0 =
      559872 * h ^ 2 *
        GCD369CubeNormalRow5
          (A + h * P) (r * A + B + h * Q)
          (-2 * r ^ 2 * A - r * B + h * S)
          (-3 * r ^ 2) (2 * r ^ 3) +
      839808 * h ^ 3 *
        GCD369CubeNormalRow5Cubic
          (A + h * P) (r * A + B + h * Q)
          (-2 * r ^ 2 * A - r * B + h * S) (-3 * r ^ 2) := by
  exact GCD369CubeFaberFullN5_zeroHigh_expansion
    (A + h * P) (r * A + B + h * Q)
    (-2 * r ^ 2 * A - r * B + h * S) (-3 * r ^ 2) (2 * r ^ 3) h

/-- Pure `d` load on the double-root first jet, including the zero-high
cubic remainder. -/
theorem GCD369CubeFaberFullN5_d_doubleRoot
    {R : Type*} [CommRing R] (r A h d : R) :
    GCD369CubeFaberFullN5
        ((2 * r ^ 3) ^ 2 + h * (-2 * r ^ 2 * A))
        (2 * (-3 * r ^ 2) * (2 * r ^ 3) + h * (r * A))
        ((-3 * r ^ 2) ^ 2 + h * A)
        (2 * (2 * r ^ 3)) (2 * (-3 * r ^ 2))
        d 0 0 0 0 0 0 =
      -278691840 * r ^ 13 * d +
        69009408 * r ^ 9 * A * h * d -
        4976640 * r ^ 5 * A ^ 2 * h ^ 2 * d -
        995328 * r * A ^ 3 * h ^ 3 * d -
        2519424 * r ^ 2 * A ^ 3 * h ^ 3 := by
  rw [GCD369CubeFaberFullN5_d_expansion,
    GCD369CubeNormalRow5_doubleRoot,
    GCD369CubeNormalRow5Cubic_doubleRoot]
  ring

#print axioms GCD369CubeNormalRow5_of_row1_row2
#print axioms GCD369CubeNormalRow5_map
#print axioms GCD369CubeNormalRow5Cubic_map
#print axioms GCD369CubeFaberFullN5_map
#print axioms GCD369CubeFaberFullN5_d_specialize
#print axioms GCD369CubeFaberFullN5_d_expansion
#print axioms GCD369CubeFaberFullN5_zeroHigh_expansion
#print axioms GCD369CubeFaberFullN5_commonNormalNumerator
#print axioms GCD369CubeFaberFullN5_commonNormalCoefficients
#print axioms GCD369CubeFaberFullN5_d_cubicSheet
#print axioms GCD369CubeFaberFullN5_d_doubleRootSheet
#print axioms GCD369CubeFaberFullN5_eq_zeroHigh_of_d_annihilates_normals
#print axioms GCD369CubeNormalRow5_doubleRoot
#print axioms GCD369CubeNormalRow5Cubic_doubleRoot
#print axioms GCD369CubeNormalRow5_doubleRoot_kernel
#print axioms GCD369CubeNormalRow5_doubleRoot_secondCorrection
#print axioms GCD369CubeFaberFullN5_doubleRoot
#print axioms GCD369CubeFaberFullN5_doubleRoot_kernelResidual
#print axioms GCD369CubeFaberFullN5_doubleRoot_secondCorrections
#print axioms GCD369CubeFaberFullN5_d_doubleRoot
