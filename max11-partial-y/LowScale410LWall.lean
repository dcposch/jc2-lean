import LowScale410LoadCascade

/-!
# The first nonzero-load wall for `(4,10)`, scale zero

We pass to the denominator-free discriminant coordinate `U = A^2 - 4 C0`.
The resulting two invariant numerators expose the true first `l ≠ 0`
Newton chamber.  In particular the tentative `(3,3,5)` cone is not a
face: the low-`U` chamber has `(deg A,deg B)=(3n,4n)` and `deg U < 5n`.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial

namespace Max11DegreeRoutes

section LWall410

variable {k : Type*} [Field k] [CharZero k]

/-- Numerator `2048 I₂` in the discriminant coordinate. -/
def discriminantInvariantTwoNumerator410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (63 * l : k) • A ^ 5 + (140 * beta : k) • A ^ 4 -
    (180 * l : k) • (A ^ 3 * U) + (320 * delta : k) • A ^ 3 -
    (360 * l : k) • (A ^ 2 * B ^ 2) -
    (336 * beta : k) • (A ^ 2 * U) + (768 * zeta : k) • A ^ 2 -
    (1280 : k) • (A * B ^ 3) - (1344 * beta : k) • (A * B ^ 2) +
    (180 * l : k) • (A * U ^ 2) - (640 * delta : k) • (A * U) +
    (2048 * theta : k) • A - (720 * l : k) • (B ^ 2 * U) +
    (1280 * delta : k) • B ^ 2 + (480 : k) • (B * U ^ 2) -
    (1536 * gamma : k) • (B * U) + (4096 * eta : k) • B +
    (336 * beta : k) • U ^ 2 - (1536 * zeta : k) • U

/-- Numerator `2048 I₁` in discriminant coordinates. -/
def discriminantInvariantOneNumerator410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  -(45 * l : k) • (A ^ 4 * B) - (112 * beta : k) • (A ^ 3 * B) +
    (180 * l : k) • (A ^ 2 * B * U) -
    (320 * delta : k) • (A ^ 2 * B) -
    (720 * l : k) • (A * B ^ 3) + (960 : k) • (A * B ^ 2 * U) -
    (1536 * gamma : k) • (A * B ^ 2) +
    (672 * beta : k) • (A * B * U) - (1536 * zeta : k) • (A * B) -
    (320 : k) • B ^ 4 - (448 * beta : k) • B ^ 3 +
    (180 * l : k) • (B * U ^ 2) - (640 * delta : k) • (B * U) +
    (2048 * theta : k) • B - (40 : k) • U ^ 3 +
    (192 * gamma : k) • U ^ 2 - (1024 * eta : k) • U

/-- Exact denominator-free change of coordinates for the first invariant. -/
theorem firstIntegralTwoPolynomial410_discriminantNumerator
    (l beta gamma delta zeta eta theta : k) (A B C0 : k[X]) :
    (2048 : k) • firstIntegralTwoPolynomial410
        l beta gamma delta zeta eta theta A B C0 =
      discriminantInvariantTwoNumerator410 l beta gamma delta zeta eta theta
        A B (A ^ 2 - (4 : k) • C0) := by
  simp [firstIntegralTwoPolynomial410,
    discriminantInvariantTwoNumerator410, Polynomial.smul_eq_C_mul]
  ring_nf
  have hC (x : k) : Polynomial.C x = x • (1 : k[X]) := by
    simp [Algebra.smul_def, Polynomial.C_eq_algebraMap]
  simp only [hC, pow_two, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    smul_smul]
  have h2 : (2 : k[X]) = (2 : k) • (1 : k[X]) := by
    rw [← hC]
    exact (Polynomial.C_ofNat 2).symm
  rw [h2]
  simp only [one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul]
  module

/-- Exact denominator-free change of coordinates for the second invariant. -/
theorem firstIntegralOnePolynomial410_discriminantNumerator
    (l beta gamma delta zeta eta theta : k) (A B C0 : k[X]) :
    (2048 : k) • firstIntegralOnePolynomial410
        l beta gamma delta zeta eta theta A B C0 =
      discriminantInvariantOneNumerator410 l beta gamma delta zeta eta theta
        A B (A ^ 2 - (4 : k) • C0) := by
  simp [firstIntegralOnePolynomial410,
    discriminantInvariantOneNumerator410, Polynomial.smul_eq_C_mul]
  ring_nf
  have hC (x : k) : Polynomial.C x = x • (1 : k[X]) := by
    simp [Algebra.smul_def, Polynomial.C_eq_algebraMap]
  simp only [hC, pow_two, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    smul_smul]
  have h2 : (2 : k[X]) = (2 : k) • (1 : k[X]) := by
    rw [← hC]
    exact (Polynomial.C_ofNat 2).symm
  have h3 : (3 : k[X]) = (3 : k) • (1 : k[X]) := by
    rw [← hC]
    exact (Polynomial.C_ofNat 3).symm
  rw [h2, h3]
  simp only [one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul,
    _root_.smul_pow, one_pow]
  module

/-- Terms below the first invariant's two leading monomials in the
`(3,4,<5)` chamber. -/
def lWallLowURestTwo410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (140 * beta : k) • A ^ 4 - (180 * l : k) • (A ^ 3 * U) +
    (320 * delta : k) • A ^ 3 - (360 * l : k) • (A ^ 2 * B ^ 2) -
    (336 * beta : k) • (A ^ 2 * U) + (768 * zeta : k) • A ^ 2 -
    (1344 * beta : k) • (A * B ^ 2) + (180 * l : k) • (A * U ^ 2) -
    (640 * delta : k) • (A * U) + (2048 * theta : k) • A -
    (720 * l : k) • (B ^ 2 * U) + (1280 * delta : k) • B ^ 2 +
    (480 : k) • (B * U ^ 2) - (1536 * gamma : k) • (B * U) +
    (4096 * eta : k) • B + (336 * beta : k) • U ^ 2 -
    (1536 * zeta : k) • U

/-- Terms below the second invariant's two leading monomials in the same
chamber. -/
def lWallLowURestOne410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  -(112 * beta : k) • (A ^ 3 * B) +
    (180 * l : k) • (A ^ 2 * B * U) - (320 * delta : k) • (A ^ 2 * B) -
    (720 * l : k) • (A * B ^ 3) + (960 : k) • (A * B ^ 2 * U) -
    (1536 * gamma : k) • (A * B ^ 2) +
    (672 * beta : k) • (A * B * U) - (1536 * zeta : k) • (A * B) -
    (448 * beta : k) • B ^ 3 + (180 * l : k) • (B * U ^ 2) -
    (640 * delta : k) • (B * U) + (2048 * theta : k) • B -
    (40 : k) • U ^ 3 + (192 * gamma : k) • U ^ 2 -
    (1024 * eta : k) • U

theorem discriminantInvariantTwoNumerator410_eq_leading_add_rest
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantTwoNumerator410 l beta gamma delta zeta eta theta
        A B U =
      (63 * l : k) • A ^ 5 - (1280 : k) • (A * B ^ 3) +
        lWallLowURestTwo410 l beta gamma delta zeta eta theta A B U := by
  simp only [discriminantInvariantTwoNumerator410, lWallLowURestTwo410]
  module

theorem discriminantInvariantOneNumerator410_eq_leading_add_rest
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantOneNumerator410 l beta gamma delta zeta eta theta
        A B U =
      -(45 * l : k) • (A ^ 4 * B) - (320 : k) • B ^ 4 +
        lWallLowURestOne410 l beta gamma delta zeta eta theta A B U := by
  simp only [discriminantInvariantOneNumerator410, lWallLowURestOne410]
  module

/-- Every omitted first-invariant monomial is strictly below radius `15n`.
This verifies, rather than assumes, the open Newton chamber. -/
theorem lWallLowURestTwo410_natDegree_lt
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) (n : ℕ)
    (hA : A.natDegree = 3 * n) (hB : B.natDegree = 4 * n)
    (hU : U.natDegree < 5 * n) :
    (lWallLowURestTwo410 l beta gamma delta zeta eta theta A B U).natDegree <
      15 * n := by
  simp only [lWallLowURestTwo410]
  compute_degree
  omega

/-- Every omitted second-invariant monomial is strictly below radius `16n`.
-/
theorem lWallLowURestOne410_natDegree_lt
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) (n : ℕ)
    (hA : A.natDegree = 3 * n) (hB : B.natDegree = 4 * n)
    (hU : U.natDegree < 5 * n) :
    (lWallLowURestOne410 l beta gamma delta zeta eta theta A B U).natDegree <
      16 * n := by
  simp only [lWallLowURestOne410]
  compute_degree
  omega

/-- Exact first leading face on the low-discriminant wall. -/
theorem discriminantInvariantTwoNumerator410_coeff_fifteen
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) (n : ℕ)
    (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = 3 * n) (hB : B.natDegree = 4 * n)
    (hU : U.natDegree < 5 * n) :
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
  have hrest := lWallLowURestTwo410_natDegree_lt
    l beta gamma delta zeta eta theta A B U n hA hB hU
  rw [discriminantInvariantTwoNumerator410_eq_leading_add_rest,
    coeff_add, coeff_sub, coeff_smul, coeff_smul,
    coeff_eq_zero_of_natDegree_lt hrest, add_zero, hA5coeff, hAB3coeff]
  simp only [smul_eq_mul]

/-- Exact second leading face on the low-discriminant wall. -/
theorem discriminantInvariantOneNumerator410_coeff_sixteen
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) (n : ℕ)
    (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = 3 * n) (hB : B.natDegree = 4 * n)
    (hU : U.natDegree < 5 * n) :
    (discriminantInvariantOneNumerator410 l beta gamma delta zeta eta theta
      A B U).coeff (16 * n) =
        -(45 * l : k) * (A.leadingCoeff ^ 4 * B.leadingCoeff) -
          (320 : k) * B.leadingCoeff ^ 4 := by
  have hA4Bdeg : (A ^ 4 * B).natDegree = 16 * n := by
    rw [natDegree_mul (pow_ne_zero 4 hAne) hBne, natDegree_pow, hA, hB]
    omega
  have hB4deg : (B ^ 4).natDegree = 16 * n := by
    rw [natDegree_pow, hB]
    omega
  have hA4Bcoeff : (A ^ 4 * B).coeff (16 * n) =
      A.leadingCoeff ^ 4 * B.leadingCoeff := by
    rw [← hA4Bdeg, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hB4coeff : (B ^ 4).coeff (16 * n) = B.leadingCoeff ^ 4 := by
    rw [← hB4deg, coeff_natDegree, leadingCoeff_pow]
  have hrest := lWallLowURestOne410_natDegree_lt
    l beta gamma delta zeta eta theta A B U n hA hB hU
  rw [discriminantInvariantOneNumerator410_eq_leading_add_rest,
    coeff_add, coeff_sub, coeff_smul, coeff_smul,
    coeff_eq_zero_of_natDegree_lt hrest, add_zero, hA4Bcoeff, hB4coeff]
  simp only [smul_eq_mul]

/-- The first genuine `l ≠ 0` open chamber is empty.  Its two leading
faces demand respectively `63 l a⁴ = 1280 b³` and
`45 l a⁴ = -320 b³`, which are incompatible in characteristic zero. -/
theorem lWall410_lowU_chamber_impossible
    (l beta gamma delta zeta eta theta k₂ k₁ : k) (A B U : k[X])
    (n : ℕ) (hn : 0 < n) (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = 3 * n) (hB : B.natDegree = 4 * n)
    (hU : U.natDegree < 5 * n)
    (hTwo : discriminantInvariantTwoNumerator410
      l beta gamma delta zeta eta theta A B U = C k₂)
    (hOne : discriminantInvariantOneNumerator410
      l beta gamma delta zeta eta theta A B U = C k₁) : False := by
  have hk₂ : (C k₂ : k[X]).coeff (15 * n) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  have hk₁ : (C k₁ : k[X]).coeff (16 * n) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  have hTwoCoeff := congrArg (fun P : k[X] => P.coeff (15 * n)) hTwo
  rw [discriminantInvariantTwoNumerator410_coeff_fifteen
    l beta gamma delta zeta eta theta A B U n hAne hBne hA hB hU,
    hk₂] at hTwoCoeff
  have hOneCoeff := congrArg (fun P : k[X] => P.coeff (16 * n)) hOne
  rw [discriminantInvariantOneNumerator410_coeff_sixteen
    l beta gamma delta zeta eta theta A B U n hAne hBne hA hB hU,
    hk₁] at hOneCoeff
  have hAle : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBle : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hrelTwo :
      (63 * l : k) * A.leadingCoeff ^ 4 =
        (1280 : k) * B.leadingCoeff ^ 3 := by
    apply mul_left_cancel₀ hAle
    linear_combination hTwoCoeff
  have hrelOne :
      (45 * l : k) * A.leadingCoeff ^ 4 =
        -(320 : k) * B.leadingCoeff ^ 3 := by
    apply mul_right_cancel₀ hBle
    linear_combination -hOneCoeff
  have hzero : (8640 : k) * B.leadingCoeff ^ 3 = 0 := by
    linear_combination -5 * hrelTwo + 7 * hrelOne
  exact (mul_ne_zero (by norm_num) (pow_ne_zero 3 hBle)) hzero

/-- Usable source-coordinate form of the empty-chamber result.  The
discriminant is not an extra variable here: it is literally `A² - 4C0`. -/
theorem lWall410_lowU_original_invariants_impossible
    (l beta gamma delta zeta eta theta k₂ k₁ : k) (A B C0 : k[X])
    (n : ℕ) (hn : 0 < n) (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = 3 * n) (hB : B.natDegree = 4 * n)
    (hU : (A ^ 2 - (4 : k) • C0).natDegree < 5 * n)
    (hTwo : firstIntegralTwoPolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k₂)
    (hOne : firstIntegralOnePolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k₁) : False := by
  have hTwoD :
      discriminantInvariantTwoNumerator410 l beta gamma delta zeta eta theta
          A B (A ^ 2 - (4 : k) • C0) = C (2048 * k₂) := by
    rw [← firstIntegralTwoPolynomial410_discriminantNumerator, hTwo]
    rw [Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  have hOneD :
      discriminantInvariantOneNumerator410 l beta gamma delta zeta eta theta
          A B (A ^ 2 - (4 : k) • C0) = C (2048 * k₁) := by
    rw [← firstIntegralOnePolynomial410_discriminantNumerator, hOne]
    rw [Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  exact lWall410_lowU_chamber_impossible
    l beta gamma delta zeta eta theta (2048 * k₂) (2048 * k₁)
      A B (A ^ 2 - (4 : k) • C0) n hn hAne hBne hA hB hU hTwoD hOneD

end LWall410

end Max11DegreeRoutes
