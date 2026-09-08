import LowScale410LWall

/-!
# The boundary of the first nonzero-load wall for `(4,10)`, scale zero

At `deg A = 3n`, `deg B = 4n`, and `deg U = 5n`, the first invariant keeps
the two-term face from the open low-`U` chamber.  The second face acquires
exactly one new monomial, `960 A B^2 U`.  Eliminating the nonic load from
the two face equations leaves the finite residual wall
`7 lc(A) lc(U) = 9 lc(B)^2`.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section LWallBoundary410

variable {k : Type*} [Field k] [CharZero k]

/-- The first-invariant remainder is still strictly below its face on the
closed boundary `deg U = 5n`. -/
theorem lWallBoundaryRestTwo410_natDegree_lt
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) (n : ℕ)
    (hn : 0 < n)
    (hA : A.natDegree = 3 * n) (hB : B.natDegree = 4 * n)
    (hU : U.natDegree = 5 * n) :
    (lWallLowURestTwo410 l beta gamma delta zeta eta theta A B U).natDegree <
      15 * n := by
  simp only [lWallLowURestTwo410]
  compute_degree
  omega

/-- All second-invariant terms below the three-term boundary face. -/
def lWallBoundaryRestOne410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  -(112 * beta : k) • (A ^ 3 * B) +
    (180 * l : k) • (A ^ 2 * B * U) - (320 * delta : k) • (A ^ 2 * B) -
    (720 * l : k) • (A * B ^ 3) -
    (1536 * gamma : k) • (A * B ^ 2) +
    (672 * beta : k) • (A * B * U) - (1536 * zeta : k) • (A * B) -
    (448 * beta : k) • B ^ 3 + (180 * l : k) • (B * U ^ 2) -
    (640 * delta : k) • (B * U) + (2048 * theta : k) • B -
    (40 : k) • U ^ 3 + (192 * gamma : k) • U ^ 2 -
    (1024 * eta : k) • U

theorem discriminantInvariantOneNumerator410_eq_boundaryFace_add_rest
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantOneNumerator410 l beta gamma delta zeta eta theta
        A B U =
      -(45 * l : k) • (A ^ 4 * B) - (320 : k) • B ^ 4 +
        (960 : k) • (A * B ^ 2 * U) +
          lWallBoundaryRestOne410 l beta gamma delta zeta eta theta A B U := by
  simp only [discriminantInvariantOneNumerator410, lWallBoundaryRestOne410]
  module

theorem lWallBoundaryRestOne410_natDegree_lt
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) (n : ℕ)
    (hn : 0 < n)
    (hA : A.natDegree = 3 * n) (hB : B.natDegree = 4 * n)
    (hU : U.natDegree = 5 * n) :
    (lWallBoundaryRestOne410 l beta gamma delta zeta eta theta A B U).natDegree <
      16 * n := by
  simp only [lWallBoundaryRestOne410]
  compute_degree
  omega

/-- Exact first leading face at the boundary. -/
theorem discriminantInvariantTwoNumerator410_boundary_coeff_fifteen
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) (n : ℕ)
    (hn : 0 < n)
    (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = 3 * n) (hB : B.natDegree = 4 * n)
    (hU : U.natDegree = 5 * n) :
    (discriminantInvariantTwoNumerator410 l beta gamma delta zeta eta theta
      A B U).coeff (15 * n) =
        (63 * l : k) * A.leadingCoeff ^ 5 -
          (1280 : k) * (A.leadingCoeff * B.leadingCoeff ^ 3) := by
  have hA5deg : (A ^ 5).natDegree = 15 * n := by
    rw [natDegree_pow, hA]
    omega
  have hAB3deg : (A * B ^ 3).natDegree = 15 * n := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow, hA, hB]
    omega
  have hA5coeff : (A ^ 5).coeff (15 * n) = A.leadingCoeff ^ 5 := by
    rw [← hA5deg, coeff_natDegree, leadingCoeff_pow]
  have hAB3coeff : (A * B ^ 3).coeff (15 * n) =
      A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hAB3deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hrest := lWallBoundaryRestTwo410_natDegree_lt
    l beta gamma delta zeta eta theta A B U n hn hA hB hU
  rw [discriminantInvariantTwoNumerator410_eq_leading_add_rest,
    coeff_add, coeff_sub, coeff_smul, coeff_smul,
    coeff_eq_zero_of_natDegree_lt hrest, add_zero, hA5coeff, hAB3coeff]
  simp only [smul_eq_mul]

/-- Exact three-term second face at radius `16n`. -/
theorem discriminantInvariantOneNumerator410_boundary_coeff_sixteen
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) (n : ℕ)
    (hn : 0 < n) (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = 3 * n) (hB : B.natDegree = 4 * n)
    (hU : U.natDegree = 5 * n) :
    (discriminantInvariantOneNumerator410 l beta gamma delta zeta eta theta
      A B U).coeff (16 * n) =
        -(45 * l : k) * (A.leadingCoeff ^ 4 * B.leadingCoeff) -
          (320 : k) * B.leadingCoeff ^ 4 +
            (960 : k) *
              (A.leadingCoeff * B.leadingCoeff ^ 2 * U.leadingCoeff) := by
  have hUne : U ≠ 0 := by
    intro hzero
    subst U
    simp at hU
    omega
  have hA4Bdeg : (A ^ 4 * B).natDegree = 16 * n := by
    rw [natDegree_mul (pow_ne_zero 4 hAne) hBne, natDegree_pow, hA, hB]
    omega
  have hB4deg : (B ^ 4).natDegree = 16 * n := by
    rw [natDegree_pow, hB]
    omega
  have hAB2Udeg : (A * B ^ 2 * U).natDegree = 16 * n := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hUne,
      natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow, hA, hB, hU]
    omega
  have hA4Bcoeff : (A ^ 4 * B).coeff (16 * n) =
      A.leadingCoeff ^ 4 * B.leadingCoeff := by
    rw [← hA4Bdeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hB4coeff : (B ^ 4).coeff (16 * n) = B.leadingCoeff ^ 4 := by
    rw [← hB4deg, coeff_natDegree, leadingCoeff_pow]
  have hAB2Ucoeff : (A * B ^ 2 * U).coeff (16 * n) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * U.leadingCoeff := by
    rw [← hAB2Udeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_pow]
  have hrest := lWallBoundaryRestOne410_natDegree_lt
    l beta gamma delta zeta eta theta A B U n hn hA hB hU
  rw [discriminantInvariantOneNumerator410_eq_boundaryFace_add_rest,
    coeff_add, coeff_add, coeff_sub, coeff_smul, coeff_smul, coeff_smul,
    coeff_eq_zero_of_natDegree_lt hrest, add_zero, hA4Bcoeff, hB4coeff,
    hAB2Ucoeff]
  simp only [smul_eq_mul]

/-- The complete finite residual of the `deg U = 5n` boundary. -/
theorem lWall410_boundary_leadingCoeff_residual
    (l beta gamma delta zeta eta theta k₂ k₁ : k) (A B U : k[X])
    (n : ℕ) (hn : 0 < n) (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = 3 * n) (hB : B.natDegree = 4 * n)
    (hU : U.natDegree = 5 * n)
    (hTwo : discriminantInvariantTwoNumerator410
      l beta gamma delta zeta eta theta A B U = C k₂)
    (hOne : discriminantInvariantOneNumerator410
      l beta gamma delta zeta eta theta A B U = C k₁) :
    (7 : k) * A.leadingCoeff * U.leadingCoeff =
      (9 : k) * B.leadingCoeff ^ 2 := by
  have hk₂ : (C k₂ : k[X]).coeff (15 * n) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  have hk₁ : (C k₁ : k[X]).coeff (16 * n) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  have hTwoCoeff := congrArg (fun P : k[X] => P.coeff (15 * n)) hTwo
  rw [discriminantInvariantTwoNumerator410_boundary_coeff_fifteen
    l beta gamma delta zeta eta theta A B U n hn hAne hBne hA hB hU,
    hk₂] at hTwoCoeff
  have hOneCoeff := congrArg (fun P : k[X] => P.coeff (16 * n)) hOne
  rw [discriminantInvariantOneNumerator410_boundary_coeff_sixteen
    l beta gamma delta zeta eta theta A B U n hn hAne hBne hA hB hU,
    hk₁] at hOneCoeff
  have hAle : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBle : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hrelTwo :
      (63 * l : k) * A.leadingCoeff ^ 4 =
        (1280 : k) * B.leadingCoeff ^ 3 := by
    apply mul_left_cancel₀ hAle
    linear_combination hTwoCoeff
  have hrelOne :
      -(45 * l : k) * A.leadingCoeff ^ 4 -
          (320 : k) * B.leadingCoeff ^ 3 +
            (960 : k) *
              (A.leadingCoeff * B.leadingCoeff * U.leadingCoeff) = 0 := by
    apply mul_right_cancel₀ hBle
    linear_combination hOneCoeff
  apply mul_right_cancel₀ hBle
  linear_combination (1 / 960 : k) * (7 * hrelOne + 5 * hrelTwo)

/-- Source-coordinate form of the boundary residual. -/
theorem lWall410_boundary_original_invariants_leadingCoeff_residual
    (l beta gamma delta zeta eta theta k₂ k₁ : k) (A B C0 : k[X])
    (n : ℕ) (hn : 0 < n) (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = 3 * n) (hB : B.natDegree = 4 * n)
    (hU : (A ^ 2 - (4 : k) • C0).natDegree = 5 * n)
    (hTwo : firstIntegralTwoPolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k₂)
    (hOne : firstIntegralOnePolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k₁) :
    (7 : k) * A.leadingCoeff *
        (A ^ 2 - (4 : k) • C0).leadingCoeff =
      (9 : k) * B.leadingCoeff ^ 2 := by
  have hTwoD :
      discriminantInvariantTwoNumerator410 l beta gamma delta zeta eta theta
          A B (A ^ 2 - (4 : k) • C0) = C (2048 * k₂) := by
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hOneD :
      discriminantInvariantOneNumerator410 l beta gamma delta zeta eta theta
          A B (A ^ 2 - (4 : k) • C0) = C (2048 * k₁) := by
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  exact lWall410_boundary_leadingCoeff_residual
    l beta gamma delta zeta eta theta (2048 * k₂) (2048 * k₁)
      A B (A ^ 2 - (4 : k) • C0) n hn hAne hBne hA hB hU hTwoD hOneD

/-! ## The high-discriminant split -/

/-- Remainder after extracting `960 A B² U`, the unique top term when
`5n < deg U < 11n/2`. -/
def lWallHighABRestOne410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  -(45 * l : k) • (A ^ 4 * B) - (320 : k) • B ^ 4 +
    lWallBoundaryRestOne410 l beta gamma delta zeta eta theta A B U

theorem discriminantInvariantOneNumerator410_eq_highAB_add_rest
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantOneNumerator410 l beta gamma delta zeta eta theta
        A B U =
      (960 : k) • (A * B ^ 2 * U) +
        lWallHighABRestOne410 l beta gamma delta zeta eta theta A B U := by
  rw [discriminantInvariantOneNumerator410_eq_boundaryFace_add_rest]
  simp only [lWallHighABRestOne410]
  module

theorem lWallHighABRestOne410_natDegree_lt
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) (n : ℕ)
    (hn : 0 < n) (hA : A.natDegree = 3 * n)
    (hB : B.natDegree = 4 * n) (hUlow : 5 * n < U.natDegree)
    (hUhigh : 2 * U.natDegree < 11 * n) :
    (lWallHighABRestOne410 l beta gamma delta zeta eta theta A B U).natDegree <
      11 * n + U.natDegree := by
  simp only [lWallHighABRestOne410, lWallBoundaryRestOne410]
  compute_degree
  omega

/-- The lower open part of the high-`U` region is empty. -/
theorem lWall410_highU_belowHalf_impossible
    (l beta gamma delta zeta eta theta k₁ : k) (A B U : k[X])
    (n : ℕ) (hn : 0 < n) (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = 3 * n) (hB : B.natDegree = 4 * n)
    (hUlow : 5 * n < U.natDegree)
    (hUhigh : 2 * U.natDegree < 11 * n)
    (hOne : discriminantInvariantOneNumerator410
      l beta gamma delta zeta eta theta A B U = C k₁) : False := by
  have hUne : U ≠ 0 := by
    intro hzero
    subst U
    simp at hUlow
  have htopdeg : (A * B ^ 2 * U).natDegree = 11 * n + U.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hUne,
      natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow, hA, hB]
    omega
  have htopcoeff : (A * B ^ 2 * U).coeff (11 * n + U.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * U.leadingCoeff := by
    rw [← htopdeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_pow]
  have hrest := lWallHighABRestOne410_natDegree_lt
    l beta gamma delta zeta eta theta A B U n hn hA hB hUlow hUhigh
  have hk₁ : (C k₁ : k[X]).coeff (11 * n + U.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  have hcoeff := congrArg
    (fun P : k[X] => P.coeff (11 * n + U.natDegree)) hOne
  rw [discriminantInvariantOneNumerator410_eq_highAB_add_rest,
    coeff_add, coeff_smul, coeff_eq_zero_of_natDegree_lt hrest, add_zero,
    htopcoeff, hk₁] at hcoeff
  simp only [smul_eq_mul] at hcoeff
  have hAle : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBle : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hUle : U.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hUne
  have hnonzero :
      (960 : k) *
          (A.leadingCoeff * B.leadingCoeff ^ 2 * U.leadingCoeff) ≠ 0 :=
    mul_ne_zero (by norm_num)
      (mul_ne_zero (mul_ne_zero hAle (pow_ne_zero 2 hBle)) hUle)
  exact hnonzero hcoeff

/-- Remainder after extracting `-40 U³`, the unique top term above the
half-wall `2 deg U = 11n`. -/
def lWallHighU3RestOne410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  -(45 * l : k) • (A ^ 4 * B) - (112 * beta : k) • (A ^ 3 * B) +
    (180 * l : k) • (A ^ 2 * B * U) -
    (320 * delta : k) • (A ^ 2 * B) -
    (720 * l : k) • (A * B ^ 3) + (960 : k) • (A * B ^ 2 * U) -
    (1536 * gamma : k) • (A * B ^ 2) +
    (672 * beta : k) • (A * B * U) - (1536 * zeta : k) • (A * B) -
    (320 : k) • B ^ 4 - (448 * beta : k) • B ^ 3 +
    (180 * l : k) • (B * U ^ 2) - (640 * delta : k) • (B * U) +
    (2048 * theta : k) • B + (192 * gamma : k) • U ^ 2 -
    (1024 * eta : k) • U

theorem discriminantInvariantOneNumerator410_eq_highU3_add_rest
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantOneNumerator410 l beta gamma delta zeta eta theta
        A B U =
      -(40 : k) • U ^ 3 +
        lWallHighU3RestOne410 l beta gamma delta zeta eta theta A B U := by
  simp only [discriminantInvariantOneNumerator410, lWallHighU3RestOne410]
  module

theorem lWallHighU3RestOne410_natDegree_lt
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) (n : ℕ)
    (hn : 0 < n) (hA : A.natDegree = 3 * n)
    (hB : B.natDegree = 4 * n) (hUlow : 5 * n < U.natDegree)
    (hUhigh : 11 * n < 2 * U.natDegree) :
    (lWallHighU3RestOne410 l beta gamma delta zeta eta theta A B U).natDegree <
      3 * U.natDegree := by
  simp only [lWallHighU3RestOne410]
  compute_degree
  omega

/-- The upper open part of the high-`U` region is empty. -/
theorem lWall410_highU_aboveHalf_impossible
    (l beta gamma delta zeta eta theta k₁ : k) (A B U : k[X])
    (n : ℕ) (hn : 0 < n) (hA : A.natDegree = 3 * n)
    (hB : B.natDegree = 4 * n) (hUlow : 5 * n < U.natDegree)
    (hUhigh : 11 * n < 2 * U.natDegree)
    (hOne : discriminantInvariantOneNumerator410
      l beta gamma delta zeta eta theta A B U = C k₁) : False := by
  have hUne : U ≠ 0 := by
    intro hzero
    subst U
    simp at hUlow
  have hU3deg : (U ^ 3).natDegree = 3 * U.natDegree := by
    rw [natDegree_pow]
  have hU3coeff : (U ^ 3).coeff (3 * U.natDegree) =
      U.leadingCoeff ^ 3 := by
    rw [← hU3deg, coeff_natDegree, leadingCoeff_pow]
  have hrest := lWallHighU3RestOne410_natDegree_lt
    l beta gamma delta zeta eta theta A B U n hn hA hB hUlow hUhigh
  have hk₁ : (C k₁ : k[X]).coeff (3 * U.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  have hcoeff := congrArg
    (fun P : k[X] => P.coeff (3 * U.natDegree)) hOne
  rw [discriminantInvariantOneNumerator410_eq_highU3_add_rest,
    coeff_add, coeff_smul, coeff_eq_zero_of_natDegree_lt hrest, add_zero,
    hU3coeff, hk₁] at hcoeff
  simp only [smul_eq_mul] at hcoeff
  have hUle : U.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hUne
  exact (mul_ne_zero (by norm_num) (pow_ne_zero 3 hUle)) hcoeff

/-- Away from the exact half-wall, every high-discriminant chamber is
empty. -/
theorem lWall410_highU_offHalf_impossible
    (l beta gamma delta zeta eta theta k₁ : k) (A B U : k[X])
    (n : ℕ) (hn : 0 < n) (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = 3 * n) (hB : B.natDegree = 4 * n)
    (hUlow : 5 * n < U.natDegree)
    (hUnequal : 2 * U.natDegree ≠ 11 * n)
    (hOne : discriminantInvariantOneNumerator410
      l beta gamma delta zeta eta theta A B U = C k₁) : False := by
  rcases lt_or_gt_of_ne hUnequal with hbelow | habove
  · exact lWall410_highU_belowHalf_impossible
      l beta gamma delta zeta eta theta k₁ A B U n hn hAne hBne
        hA hB hUlow hbelow hOne
  · exact lWall410_highU_aboveHalf_impossible
      l beta gamma delta zeta eta theta k₁ A B U n hn hA hB
        hUlow habove hOne

/-- Source-coordinate form of the complete off-half-wall exclusion. -/
theorem lWall410_highU_offHalf_original_invariants_impossible
    (l beta gamma delta zeta eta theta k₁ : k) (A B C0 : k[X])
    (n : ℕ) (hn : 0 < n) (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = 3 * n) (hB : B.natDegree = 4 * n)
    (hUlow : 5 * n < (A ^ 2 - (4 : k) • C0).natDegree)
    (hUnequal : 2 * (A ^ 2 - (4 : k) • C0).natDegree ≠ 11 * n)
    (hOne : firstIntegralOnePolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k₁) : False := by
  have hOneD :
      discriminantInvariantOneNumerator410 l beta gamma delta zeta eta theta
          A B (A ^ 2 - (4 : k) • C0) = C (2048 * k₁) := by
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  exact lWall410_highU_offHalf_impossible
    l beta gamma delta zeta eta theta (2048 * k₁)
      A B (A ^ 2 - (4 : k) • C0) n hn hAne hBne hA hB
        hUlow hUnequal hOneD

/-! ## The exceptional half-wall -/

/-- First-invariant terms below the half-wall face. -/
def lWallHalfRestTwo410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (140 * beta : k) • A ^ 4 - (180 * l : k) • (A ^ 3 * U) +
    (320 * delta : k) • A ^ 3 - (360 * l : k) • (A ^ 2 * B ^ 2) -
    (336 * beta : k) • (A ^ 2 * U) + (768 * zeta : k) • A ^ 2 -
    (1344 * beta : k) • (A * B ^ 2) + (180 * l : k) • (A * U ^ 2) -
    (640 * delta : k) • (A * U) + (2048 * theta : k) • A -
    (720 * l : k) • (B ^ 2 * U) + (1280 * delta : k) • B ^ 2 -
    (1536 * gamma : k) • (B * U) + (4096 * eta : k) • B +
    (336 * beta : k) • U ^ 2 - (1536 * zeta : k) • U

theorem discriminantInvariantTwoNumerator410_eq_halfFace_add_rest
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantTwoNumerator410 l beta gamma delta zeta eta theta
        A B U =
      (63 * l : k) • A ^ 5 - (1280 : k) • (A * B ^ 3) +
        (480 : k) • (B * U ^ 2) +
          lWallHalfRestTwo410 l beta gamma delta zeta eta theta A B U := by
  simp only [discriminantInvariantTwoNumerator410, lWallHalfRestTwo410]
  module

theorem lWallHalfRestTwo410_natDegree_lt
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) (n : ℕ)
    (hn : 0 < n) (hA : A.natDegree = 3 * n)
    (hB : B.natDegree = 4 * n) (hU : 2 * U.natDegree = 11 * n) :
    (lWallHalfRestTwo410 l beta gamma delta zeta eta theta A B U).natDegree <
      15 * n := by
  simp only [lWallHalfRestTwo410]
  compute_degree
  omega

/-- Second-invariant terms below `960 A B² U - 40 U³`. -/
def lWallHalfRestOne410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  -(45 * l : k) • (A ^ 4 * B) - (112 * beta : k) • (A ^ 3 * B) +
    (180 * l : k) • (A ^ 2 * B * U) -
    (320 * delta : k) • (A ^ 2 * B) -
    (720 * l : k) • (A * B ^ 3) -
    (1536 * gamma : k) • (A * B ^ 2) +
    (672 * beta : k) • (A * B * U) - (1536 * zeta : k) • (A * B) -
    (320 : k) • B ^ 4 - (448 * beta : k) • B ^ 3 +
    (180 * l : k) • (B * U ^ 2) - (640 * delta : k) • (B * U) +
    (2048 * theta : k) • B + (192 * gamma : k) • U ^ 2 -
    (1024 * eta : k) • U

theorem discriminantInvariantOneNumerator410_eq_halfFace_add_rest
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantOneNumerator410 l beta gamma delta zeta eta theta
        A B U =
      (960 : k) • (A * B ^ 2 * U) - (40 : k) • U ^ 3 +
        lWallHalfRestOne410 l beta gamma delta zeta eta theta A B U := by
  simp only [discriminantInvariantOneNumerator410, lWallHalfRestOne410]
  module

theorem lWallHalfRestOne410_natDegree_lt
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) (n : ℕ)
    (hn : 0 < n) (hA : A.natDegree = 3 * n)
    (hB : B.natDegree = 4 * n) (hU : 2 * U.natDegree = 11 * n) :
    (lWallHalfRestOne410 l beta gamma delta zeta eta theta A B U).natDegree <
      3 * U.natDegree := by
  simp only [lWallHalfRestOne410]
  compute_degree
  omega

/-- The exact two leading-coefficient equations on the exceptional
half-wall. -/
theorem lWall410_halfWall_leadingCoeff_residual
    (l beta gamma delta zeta eta theta k₂ k₁ : k) (A B U : k[X])
    (n : ℕ) (hn : 0 < n) (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = 3 * n) (hB : B.natDegree = 4 * n)
    (hU : 2 * U.natDegree = 11 * n)
    (hTwo : discriminantInvariantTwoNumerator410
      l beta gamma delta zeta eta theta A B U = C k₂)
    (hOne : discriminantInvariantOneNumerator410
      l beta gamma delta zeta eta theta A B U = C k₁) :
    (24 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 =
        U.leadingCoeff ^ 2 ∧
      (63 * l : k) * A.leadingCoeff ^ 4 =
        -(10240 : k) * B.leadingCoeff ^ 3 := by
  have hUlow : 5 * n < U.natDegree := by omega
  have hUne : U ≠ 0 := by
    intro hzero
    subst U
    simp at hUlow
  have hBU2deg : (B * U ^ 2).natDegree = 15 * n := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hUne), natDegree_pow, hB]
    omega
  have hA5deg : (A ^ 5).natDegree = 15 * n := by
    rw [natDegree_pow, hA]
    omega
  have hAB3deg : (A * B ^ 3).natDegree = 15 * n := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow, hA, hB]
    omega
  have hBU2coeff : (B * U ^ 2).coeff (15 * n) =
      B.leadingCoeff * U.leadingCoeff ^ 2 := by
    rw [← hBU2deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hA5coeff : (A ^ 5).coeff (15 * n) = A.leadingCoeff ^ 5 := by
    rw [← hA5deg, coeff_natDegree, leadingCoeff_pow]
  have hAB3coeff : (A * B ^ 3).coeff (15 * n) =
      A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hAB3deg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hAB2Udeg : (A * B ^ 2 * U).natDegree = 3 * U.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hUne,
      natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow, hA, hB]
    omega
  have hU3deg : (U ^ 3).natDegree = 3 * U.natDegree := by
    rw [natDegree_pow]
  have hAB2Ucoeff : (A * B ^ 2 * U).coeff (3 * U.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * U.leadingCoeff := by
    rw [← hAB2Udeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul,
      leadingCoeff_pow]
  have hU3coeff : (U ^ 3).coeff (3 * U.natDegree) =
      U.leadingCoeff ^ 3 := by
    rw [← hU3deg, coeff_natDegree, leadingCoeff_pow]
  have hrestTwo := lWallHalfRestTwo410_natDegree_lt
    l beta gamma delta zeta eta theta A B U n hn hA hB hU
  have hrestOne := lWallHalfRestOne410_natDegree_lt
    l beta gamma delta zeta eta theta A B U n hn hA hB hU
  have hk₂ : (C k₂ : k[X]).coeff (15 * n) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  have hk₁ : (C k₁ : k[X]).coeff (3 * U.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  have hTwoCoeff := congrArg (fun P : k[X] => P.coeff (15 * n)) hTwo
  rw [discriminantInvariantTwoNumerator410_eq_halfFace_add_rest,
    coeff_add, coeff_add, coeff_sub, coeff_smul, coeff_smul, coeff_smul,
    coeff_eq_zero_of_natDegree_lt hrestTwo, add_zero, hA5coeff,
    hAB3coeff, hBU2coeff, hk₂] at hTwoCoeff
  simp only [smul_eq_mul] at hTwoCoeff
  have hOneCoeff := congrArg
    (fun P : k[X] => P.coeff (3 * U.natDegree)) hOne
  rw [discriminantInvariantOneNumerator410_eq_halfFace_add_rest,
    coeff_add, coeff_sub, coeff_smul, coeff_smul,
    coeff_eq_zero_of_natDegree_lt hrestOne, add_zero, hAB2Ucoeff,
    hU3coeff, hk₁] at hOneCoeff
  simp only [smul_eq_mul] at hOneCoeff
  have hAle : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hUle : U.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hUne
  have hshape :
      (24 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 =
        U.leadingCoeff ^ 2 := by
    apply mul_right_cancel₀ hUle
    linear_combination (1 / 40 : k) * hOneCoeff
  refine ⟨hshape, ?_⟩
  apply mul_left_cancel₀ hAle
  linear_combination hTwoCoeff + 480 * B.leadingCoeff * hshape

/-- Source-coordinate form of the exceptional half-wall residual. -/
theorem lWall410_halfWall_original_invariants_leadingCoeff_residual
    (l beta gamma delta zeta eta theta k₂ k₁ : k) (A B C0 : k[X])
    (n : ℕ) (hn : 0 < n) (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = 3 * n) (hB : B.natDegree = 4 * n)
    (hU : 2 * (A ^ 2 - (4 : k) • C0).natDegree = 11 * n)
    (hTwo : firstIntegralTwoPolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k₂)
    (hOne : firstIntegralOnePolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k₁) :
    (24 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 =
        (A ^ 2 - (4 : k) • C0).leadingCoeff ^ 2 ∧
      (63 * l : k) * A.leadingCoeff ^ 4 =
        -(10240 : k) * B.leadingCoeff ^ 3 := by
  have hTwoD :
      discriminantInvariantTwoNumerator410 l beta gamma delta zeta eta theta
          A B (A ^ 2 - (4 : k) • C0) = C (2048 * k₂) := by
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hOneD :
      discriminantInvariantOneNumerator410 l beta gamma delta zeta eta theta
          A B (A ^ 2 - (4 : k) • C0) = C (2048 * k₁) := by
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  exact lWall410_halfWall_leadingCoeff_residual
    l beta gamma delta zeta eta theta (2048 * k₂) (2048 * k₁)
      A B (A ^ 2 - (4 : k) • C0) n hn hAne hBne hA hB hU hTwoD hOneD

end LWallBoundary410

end Max11DegreeRoutes
