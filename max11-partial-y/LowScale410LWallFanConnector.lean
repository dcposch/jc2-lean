import LowScale410LWallOtherCones

/-!
# Newton-fan connector for the `(4,10)`, scale-zero `l ≠ 0` wall

The two constant discriminant invariants force a tie on each exposed
Newton vertex.  The resulting arithmetic fan is either the `(3n,4n)`
ray or the closed sector treated in `LowScale410LWallOtherCones`.
-/

noncomputable section

set_option maxHeartbeats 8000000

open Polynomial

namespace Max11DegreeRoutes

section LWallFanConnector410

variable {k : Type*} [Field k] [CharZero k]

def fanTwoA5Unique410 (a b u : ℕ) : Prop :=
  a + 2 * u < 5 * a ∧ a + 3 * b < 5 * a ∧ b + 2 * u < 5 * a

def fanTwoAB3Unique410 (a b u : ℕ) : Prop :=
  5 * a < a + 3 * b ∧ a + 2 * u < a + 3 * b ∧
    b + 2 * u < a + 3 * b

def fanTwoBU2Unique410 (a b u : ℕ) : Prop :=
  5 * a < b + 2 * u ∧ a + 2 * u < b + 2 * u ∧
    a + 3 * b < b + 2 * u

def fanOneA4BUnique410 (a b u : ℕ) : Prop :=
  a + 2 * b + u < 4 * a + b ∧ 4 * b < 4 * a + b ∧
    3 * u < 4 * a + b

def fanOneAB2UUnique410 (a b u : ℕ) : Prop :=
  4 * a + b < a + 2 * b + u ∧ 4 * b < a + 2 * b + u ∧
    3 * u < a + 2 * b + u

def fanOneB4Unique410 (a b u : ℕ) : Prop :=
  4 * a + b < 4 * b ∧ a + 2 * b + u < 4 * b ∧ 3 * u < 4 * b

def fanOneU3Unique410 (a b u : ℕ) : Prop :=
  4 * a + b < 3 * u ∧ a + 2 * b + u < 3 * u ∧ 4 * b < 3 * u

/-- A nonzero scalar multiple of a unique positive-degree leading monomial
cannot equal a constant polynomial. -/
theorem smul_add_lower_ne_C410 (c q : k) (M R : k[X]) (d : ℕ)
    (hc : c ≠ 0) (hM : M ≠ 0) (hd : 0 < d)
    (hMdeg : M.natDegree = d) (hRdeg : R.natDegree < d) :
    c • M + R ≠ C q := by
  intro heq
  have hRcoeff : R.coeff d = 0 := coeff_eq_zero_of_natDegree_lt hRdeg
  have hCcoeff : (C q : k[X]).coeff d = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_C]
    omega
  have hMcoeff : M.coeff d = M.leadingCoeff := by
    rw [← hMdeg, coeff_natDegree]
  have hcoeff := congrArg (fun P : k[X] => P.coeff d) heq
  rw [coeff_add, coeff_smul, hMcoeff, hRcoeff, add_zero, hCcoeff] at hcoeff
  simp only [smul_eq_mul] at hcoeff
  exact (mul_ne_zero hc (leadingCoeff_ne_zero.mpr hM)) hcoeff

/-! ## Remainders at the seven exposed vertices -/

def lWallFanRestTwoA5_410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  -(1280 : k) • (A * B ^ 3) +
    lWallLowURestTwo410 l beta gamma delta zeta eta theta A B U

def lWallFanRestTwoAB3_410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (63 * l : k) • A ^ 5 +
    lWallLowURestTwo410 l beta gamma delta zeta eta theta A B U

def lWallFanRestTwoBU2_410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  -(1280 : k) • (A * B ^ 3) +
    lWallIntermediateRestTwo410 l beta gamma delta zeta eta theta A B U

def lWallFanRestOneA4B_410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  -(320 : k) • B ^ 4 +
    lWallLowURestOne410 l beta gamma delta zeta eta theta A B U

def lWallFanRestOneAB2U_410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  -(40 : k) • U ^ 3 +
    lWallIntermediateRestOne410 l beta gamma delta zeta eta theta A B U

def lWallFanRestOneB4_410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  -(45 * l : k) • (A ^ 4 * B) +
    lWallLowURestOne410 l beta gamma delta zeta eta theta A B U

def lWallFanRestOneU3_410
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) : k[X] :=
  (960 : k) • (A * B ^ 2 * U) +
    lWallIntermediateRestOne410 l beta gamma delta zeta eta theta A B U

theorem discriminantInvariantTwoNumerator410_eq_fanA5_add_rest
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantTwoNumerator410 l beta gamma delta zeta eta theta
        A B U =
      (63 * l : k) • A ^ 5 +
        lWallFanRestTwoA5_410 l beta gamma delta zeta eta theta A B U := by
  rw [discriminantInvariantTwoNumerator410_eq_leading_add_rest]
  simp only [lWallFanRestTwoA5_410]
  module

theorem discriminantInvariantTwoNumerator410_eq_fanAB3_add_rest
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantTwoNumerator410 l beta gamma delta zeta eta theta
        A B U =
      -(1280 : k) • (A * B ^ 3) +
        lWallFanRestTwoAB3_410 l beta gamma delta zeta eta theta A B U := by
  rw [discriminantInvariantTwoNumerator410_eq_leading_add_rest]
  simp only [lWallFanRestTwoAB3_410]
  module

theorem discriminantInvariantTwoNumerator410_eq_fanBU2_add_rest
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantTwoNumerator410 l beta gamma delta zeta eta theta
        A B U =
      (480 : k) • (B * U ^ 2) +
        lWallFanRestTwoBU2_410 l beta gamma delta zeta eta theta A B U := by
  rw [discriminantInvariantTwoNumerator410_eq_intermediateFace_add_rest]
  simp only [lWallFanRestTwoBU2_410]
  module

theorem discriminantInvariantOneNumerator410_eq_fanA4B_add_rest
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantOneNumerator410 l beta gamma delta zeta eta theta
        A B U =
      -(45 * l : k) • (A ^ 4 * B) +
        lWallFanRestOneA4B_410 l beta gamma delta zeta eta theta A B U := by
  rw [discriminantInvariantOneNumerator410_eq_leading_add_rest]
  simp only [lWallFanRestOneA4B_410]
  module

theorem discriminantInvariantOneNumerator410_eq_fanAB2U_add_rest
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantOneNumerator410 l beta gamma delta zeta eta theta
        A B U =
      (960 : k) • (A * B ^ 2 * U) +
        lWallFanRestOneAB2U_410 l beta gamma delta zeta eta theta A B U := by
  rw [discriminantInvariantOneNumerator410_eq_intermediateFace_add_rest]
  simp only [lWallFanRestOneAB2U_410]
  module

theorem discriminantInvariantOneNumerator410_eq_fanB4_add_rest
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantOneNumerator410 l beta gamma delta zeta eta theta
        A B U =
      -(320 : k) • B ^ 4 +
        lWallFanRestOneB4_410 l beta gamma delta zeta eta theta A B U := by
  rw [discriminantInvariantOneNumerator410_eq_leading_add_rest]
  simp only [lWallFanRestOneB4_410]
  module

theorem discriminantInvariantOneNumerator410_eq_fanU3_add_rest
    (l beta gamma delta zeta eta theta : k) (A B U : k[X]) :
    discriminantInvariantOneNumerator410 l beta gamma delta zeta eta theta
        A B U =
      -(40 : k) • U ^ 3 +
        lWallFanRestOneU3_410 l beta gamma delta zeta eta theta A B U := by
  rw [discriminantInvariantOneNumerator410_eq_intermediateFace_add_rest]
  simp only [lWallFanRestOneU3_410]
  module

/-! ## Degree bounds for the exposed-vertex remainders -/

theorem lWallFanRestTwoA5_410_natDegree_lt
    (l beta gamma delta zeta eta theta : k) (A B U : k[X])
    (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hunique : fanTwoA5Unique410 a b u) :
    (lWallFanRestTwoA5_410 l beta gamma delta zeta eta theta A B U).natDegree <
      5 * a := by
  simp only [lWallFanRestTwoA5_410, lWallLowURestTwo410,
    fanTwoA5Unique410] at *
  compute_degree
  omega

theorem lWallFanRestTwoAB3_410_natDegree_lt
    (l beta gamma delta zeta eta theta : k) (A B U : k[X])
    (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hunique : fanTwoAB3Unique410 a b u) :
    (lWallFanRestTwoAB3_410 l beta gamma delta zeta eta theta A B U).natDegree <
      a + 3 * b := by
  simp only [lWallFanRestTwoAB3_410, lWallLowURestTwo410,
    fanTwoAB3Unique410] at *
  compute_degree
  omega

theorem lWallFanRestTwoBU2_410_natDegree_lt
    (l beta gamma delta zeta eta theta : k) (A B U : k[X])
    (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hunique : fanTwoBU2Unique410 a b u) :
    (lWallFanRestTwoBU2_410 l beta gamma delta zeta eta theta A B U).natDegree <
      b + 2 * u := by
  simp only [lWallFanRestTwoBU2_410, lWallIntermediateRestTwo410,
    fanTwoBU2Unique410] at *
  compute_degree
  omega

theorem lWallFanRestOneA4B_410_natDegree_lt
    (l beta gamma delta zeta eta theta : k) (A B U : k[X])
    (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hunique : fanOneA4BUnique410 a b u) :
    (lWallFanRestOneA4B_410 l beta gamma delta zeta eta theta A B U).natDegree <
      4 * a + b := by
  simp only [lWallFanRestOneA4B_410, lWallLowURestOne410,
    fanOneA4BUnique410] at *
  compute_degree
  omega

theorem lWallFanRestOneAB2U_410_natDegree_lt
    (l beta gamma delta zeta eta theta : k) (A B U : k[X])
    (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hunique : fanOneAB2UUnique410 a b u) :
    (lWallFanRestOneAB2U_410 l beta gamma delta zeta eta theta A B U).natDegree <
      a + 2 * b + u := by
  simp only [lWallFanRestOneAB2U_410, lWallIntermediateRestOne410,
    fanOneAB2UUnique410] at *
  compute_degree
  omega

theorem lWallFanRestOneB4_410_natDegree_lt
    (l beta gamma delta zeta eta theta : k) (A B U : k[X])
    (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hunique : fanOneB4Unique410 a b u) :
    (lWallFanRestOneB4_410 l beta gamma delta zeta eta theta A B U).natDegree <
      4 * b := by
  simp only [lWallFanRestOneB4_410, lWallLowURestOne410,
    fanOneB4Unique410] at *
  compute_degree
  omega

theorem lWallFanRestOneU3_410_natDegree_lt
    (l beta gamma delta zeta eta theta : k) (A B U : k[X])
    (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hunique : fanOneU3Unique410 a b u) :
    (lWallFanRestOneU3_410 l beta gamma delta zeta eta theta A B U).natDegree <
      3 * u := by
  simp only [lWallFanRestOneU3_410, lWallIntermediateRestOne410,
    fanOneU3Unique410] at *
  compute_degree
  omega

/-! ## Constant invariants forbid every exposed unique vertex -/

theorem fanTwoA5_not_unique410
    (l beta gamma delta zeta eta theta k₂ : k) (A B U : k[X])
    (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hl : l ≠ 0) (hAne : A ≠ 0)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hTwo : discriminantInvariantTwoNumerator410
      l beta gamma delta zeta eta theta A B U = C k₂) :
    ¬ fanTwoA5Unique410 a b u := by
  intro hunique
  rw [discriminantInvariantTwoNumerator410_eq_fanA5_add_rest] at hTwo
  apply (smul_add_lower_ne_C410 (63 * l) k₂ (A ^ 5)
    (lWallFanRestTwoA5_410 l beta gamma delta zeta eta theta A B U)
      (5 * a))
  · exact mul_ne_zero (by norm_num) hl
  · exact pow_ne_zero 5 hAne
  · omega
  · rw [natDegree_pow, hA]
  · exact lWallFanRestTwoA5_410_natDegree_lt
      l beta gamma delta zeta eta theta A B U a b u ha hb hu
        hA hB hU hunique
  · exact hTwo

theorem fanTwoAB3_not_unique410
    (l beta gamma delta zeta eta theta k₂ : k) (A B U : k[X])
    (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hTwo : discriminantInvariantTwoNumerator410
      l beta gamma delta zeta eta theta A B U = C k₂) :
    ¬ fanTwoAB3Unique410 a b u := by
  intro hunique
  rw [discriminantInvariantTwoNumerator410_eq_fanAB3_add_rest] at hTwo
  apply (smul_add_lower_ne_C410 (-(1280 : k)) k₂ (A * B ^ 3)
    (lWallFanRestTwoAB3_410 l beta gamma delta zeta eta theta A B U)
      (a + 3 * b))
  · norm_num
  · exact mul_ne_zero hAne (pow_ne_zero 3 hBne)
  · omega
  · rw [natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow, hA, hB]
  · exact lWallFanRestTwoAB3_410_natDegree_lt
      l beta gamma delta zeta eta theta A B U a b u ha hb hu
        hA hB hU hunique
  · exact hTwo

theorem fanTwoBU2_not_unique410
    (l beta gamma delta zeta eta theta k₂ : k) (A B U : k[X])
    (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hBne : B ≠ 0) (hUne : U ≠ 0)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hTwo : discriminantInvariantTwoNumerator410
      l beta gamma delta zeta eta theta A B U = C k₂) :
    ¬ fanTwoBU2Unique410 a b u := by
  intro hunique
  rw [discriminantInvariantTwoNumerator410_eq_fanBU2_add_rest] at hTwo
  apply (smul_add_lower_ne_C410 (480 : k) k₂ (B * U ^ 2)
    (lWallFanRestTwoBU2_410 l beta gamma delta zeta eta theta A B U)
      (b + 2 * u))
  · norm_num
  · exact mul_ne_zero hBne (pow_ne_zero 2 hUne)
  · omega
  · rw [natDegree_mul hBne (pow_ne_zero 2 hUne), natDegree_pow, hB, hU]
  · exact lWallFanRestTwoBU2_410_natDegree_lt
      l beta gamma delta zeta eta theta A B U a b u ha hb hu
        hA hB hU hunique
  · exact hTwo

theorem fanOneA4B_not_unique410
    (l beta gamma delta zeta eta theta k₁ : k) (A B U : k[X])
    (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hl : l ≠ 0) (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hOne : discriminantInvariantOneNumerator410
      l beta gamma delta zeta eta theta A B U = C k₁) :
    ¬ fanOneA4BUnique410 a b u := by
  intro hunique
  rw [discriminantInvariantOneNumerator410_eq_fanA4B_add_rest] at hOne
  apply (smul_add_lower_ne_C410 (-(45 * l : k)) k₁ (A ^ 4 * B)
    (lWallFanRestOneA4B_410 l beta gamma delta zeta eta theta A B U)
      (4 * a + b))
  · exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) hl)
  · exact mul_ne_zero (pow_ne_zero 4 hAne) hBne
  · omega
  · rw [natDegree_mul (pow_ne_zero 4 hAne) hBne, natDegree_pow, hA, hB]
  · exact lWallFanRestOneA4B_410_natDegree_lt
      l beta gamma delta zeta eta theta A B U a b u ha hb hu
        hA hB hU hunique
  · exact hOne

theorem fanOneAB2U_not_unique410
    (l beta gamma delta zeta eta theta k₁ : k) (A B U : k[X])
    (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hUne : U ≠ 0)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hOne : discriminantInvariantOneNumerator410
      l beta gamma delta zeta eta theta A B U = C k₁) :
    ¬ fanOneAB2UUnique410 a b u := by
  intro hunique
  rw [discriminantInvariantOneNumerator410_eq_fanAB2U_add_rest] at hOne
  apply (smul_add_lower_ne_C410 (960 : k) k₁ (A * B ^ 2 * U)
    (lWallFanRestOneAB2U_410 l beta gamma delta zeta eta theta A B U)
      (a + 2 * b + u))
  · norm_num
  · exact mul_ne_zero (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hUne
  · omega
  · rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hUne,
      natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow, hA, hB, hU]
  · exact lWallFanRestOneAB2U_410_natDegree_lt
      l beta gamma delta zeta eta theta A B U a b u ha hb hu
        hA hB hU hunique
  · exact hOne

theorem fanOneB4_not_unique410
    (l beta gamma delta zeta eta theta k₁ : k) (A B U : k[X])
    (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hBne : B ≠ 0)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hOne : discriminantInvariantOneNumerator410
      l beta gamma delta zeta eta theta A B U = C k₁) :
    ¬ fanOneB4Unique410 a b u := by
  intro hunique
  rw [discriminantInvariantOneNumerator410_eq_fanB4_add_rest] at hOne
  apply (smul_add_lower_ne_C410 (-(320 : k)) k₁ (B ^ 4)
    (lWallFanRestOneB4_410 l beta gamma delta zeta eta theta A B U)
      (4 * b))
  · norm_num
  · exact pow_ne_zero 4 hBne
  · omega
  · rw [natDegree_pow, hB]
  · exact lWallFanRestOneB4_410_natDegree_lt
      l beta gamma delta zeta eta theta A B U a b u ha hb hu
        hA hB hU hunique
  · exact hOne

theorem fanOneU3_not_unique410
    (l beta gamma delta zeta eta theta k₁ : k) (A B U : k[X])
    (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hUne : U ≠ 0)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hOne : discriminantInvariantOneNumerator410
      l beta gamma delta zeta eta theta A B U = C k₁) :
    ¬ fanOneU3Unique410 a b u := by
  intro hunique
  rw [discriminantInvariantOneNumerator410_eq_fanU3_add_rest] at hOne
  apply (smul_add_lower_ne_C410 (-(40 : k)) k₁ (U ^ 3)
    (lWallFanRestOneU3_410 l beta gamma delta zeta eta theta A B U)
      (3 * u))
  · norm_num
  · exact pow_ne_zero 3 hUne
  · omega
  · rw [natDegree_pow, hU]
  · exact lWallFanRestOneU3_410_natDegree_lt
      l beta gamma delta zeta eta theta A B U a b u ha hb hu
        hA hB hU hunique
  · exact hOne

/-! ## The complete arithmetic fan -/

theorem lWall410_fan_split_of_no_unique
    (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hTwoA5 : ¬ fanTwoA5Unique410 a b u)
    (hTwoAB3 : ¬ fanTwoAB3Unique410 a b u)
    (hTwoBU2 : ¬ fanTwoBU2Unique410 a b u)
    (hOneA4B : ¬ fanOneA4BUnique410 a b u)
    (hOneAB2U : ¬ fanOneAB2UUnique410 a b u)
    (hOneB4 : ¬ fanOneB4Unique410 a b u)
    (hOneU3 : ¬ fanOneU3Unique410 a b u) :
    (∃ n, 0 < n ∧ a = 3 * n ∧ b = 4 * n) ∨
      (2 * u = a + 2 * b ∧ 4 * a ≤ 3 * b ∧ 2 * b ≤ 3 * a) := by
  have hfan :
      4 * a = 3 * b ∨
        (2 * u = a + 2 * b ∧ 4 * a < 3 * b ∧ 2 * b ≤ 3 * a) := by
    simp only [fanTwoA5Unique410, fanTwoAB3Unique410,
      fanTwoBU2Unique410, fanOneA4BUnique410, fanOneAB2UUnique410,
      fanOneB4Unique410, fanOneU3Unique410] at *
    omega
  rcases hfan with hlower | hsector
  · left
    have hdiv : 3 ∣ a := by
      apply (by decide : Nat.Coprime 3 4).dvd_of_dvd_mul_right
      use b
      omega
    obtain ⟨n, hn⟩ := hdiv
    exact ⟨n, by omega⟩
  · right
    omega

/-- Polynomial form of the Newton-support connector.  No fan equation or
degree-ratio bound is assumed. -/
theorem lWall410_discriminant_fan_split
    (l beta gamma delta zeta eta theta k₂ k₁ : k) (A B U : k[X])
    (a b u : ℕ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hl : l ≠ 0) (hAne : A ≠ 0) (hBne : B ≠ 0) (hUne : U ≠ 0)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hTwo : discriminantInvariantTwoNumerator410
      l beta gamma delta zeta eta theta A B U = C k₂)
    (hOne : discriminantInvariantOneNumerator410
      l beta gamma delta zeta eta theta A B U = C k₁) :
    (∃ n, 0 < n ∧ a = 3 * n ∧ b = 4 * n) ∨
      (2 * u = a + 2 * b ∧ 4 * a ≤ 3 * b ∧ 2 * b ≤ 3 * a) := by
  apply lWall410_fan_split_of_no_unique a b u ha hb hu
  · exact fanTwoA5_not_unique410
      l beta gamma delta zeta eta theta k₂ A B U a b u ha hb hu hl hAne
        hA hB hU hTwo
  · exact fanTwoAB3_not_unique410
      l beta gamma delta zeta eta theta k₂ A B U a b u ha hb hu hAne hBne
        hA hB hU hTwo
  · exact fanTwoBU2_not_unique410
      l beta gamma delta zeta eta theta k₂ A B U a b u ha hb hu hBne hUne
        hA hB hU hTwo
  · exact fanOneA4B_not_unique410
      l beta gamma delta zeta eta theta k₁ A B U a b u ha hb hu hl hAne hBne
        hA hB hU hOne
  · exact fanOneAB2U_not_unique410
      l beta gamma delta zeta eta theta k₁ A B U a b u ha hb hu
        hAne hBne hUne hA hB hU hOne
  · exact fanOneB4_not_unique410
      l beta gamma delta zeta eta theta k₁ A B U a b u ha hb hu hBne
        hA hB hU hOne
  · exact fanOneU3_not_unique410
      l beta gamma delta zeta eta theta k₁ A B U a b u ha hb hu hUne
        hA hB hU hOne

/-! ## Elimination of the complete positive-degree wall -/

theorem lWall410_discriminant_all_positive_impossible
    (l beta gamma delta zeta eta theta k₂ k₁ terminal : k)
    (A B U : k[X]) (a b u : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hu : 0 < u) (hl : l ≠ 0)
    (hAne : A ≠ 0) (hBne : B ≠ 0) (hUne : U ≠ 0)
    (hA : A.natDegree = a) (hB : B.natDegree = b) (hU : U.natDegree = u)
    (hTwo : discriminantInvariantTwoNumerator410
      l beta gamma delta zeta eta theta A B U = C k₂)
    (hOne : discriminantInvariantOneNumerator410
      l beta gamma delta zeta eta theta A B U = C k₁)
    (hTerminal : lWallTerminalNumerator410
      l beta gamma delta zeta eta theta A B U = C terminal) : False := by
  obtain hray | hsector := lWall410_discriminant_fan_split
    l beta gamma delta zeta eta theta k₂ k₁ A B U a b u
      ha hb hu hl hAne hBne hUne hA hB hU hTwo hOne
  · obtain ⟨n, hn, haShape, hbShape⟩ := hray
    have hADegree : A.natDegree = 3 * n := hA.trans haShape
    have hBDegree : B.natDegree = 4 * n := hB.trans hbShape
    by_cases hLow : u < 5 * n
    · apply lWall410_lowU_chamber_impossible
        l beta gamma delta zeta eta theta k₂ k₁ A B U n hn
          hAne hBne hADegree hBDegree
      · omega
      · exact hTwo
      · exact hOne
    · by_cases hBoundary : u = 5 * n
      · apply lWall410_boundary_terminal_impossible
          l beta gamma delta zeta eta theta k₂ terminal A B U n hn
            hAne hBne hADegree hBDegree
        · omega
        · exact hTwo
        · exact hTerminal
      · have hHigh : 5 * n < U.natDegree := by omega
        by_cases hHalf : 2 * u = 11 * n
        · apply lWall410_halfWall_terminal_impossible
            l beta gamma delta zeta eta theta k₂ k₁ terminal
              A B U n hn hAne hBne hADegree hBDegree
          · omega
          · exact hTwo
          · exact hOne
          · exact hTerminal
        · exact lWall410_highU_offHalf_impossible
            l beta gamma delta zeta eta theta k₁ A B U n hn hAne hBne
              hADegree hBDegree hHigh (by omega) hOne
  · obtain ⟨hplane, hlower, hupper⟩ := hsector
    rcases lWall410_closed_sector_fan_split a b u hplane hlower hupper with
      hLowerRay | hStrict | hAligned
    · obtain ⟨n, haShape, hbShape⟩ := hLowerRay
      have hn : 0 < n := by omega
      apply lWall410_halfWall_terminal_impossible
        l beta gamma delta zeta eta theta k₂ k₁ terminal
          A B U n hn hAne hBne
      · omega
      · omega
      · omega
      · exact hTwo
      · exact hOne
      · exact hTerminal
    · obtain ⟨hlowerStrict, hupperStrict⟩ := hStrict
      exact lWall410_intermediate_cone_impossible
        l beta gamma delta zeta eta theta k₂ k₁ A B U a b u
          ha hb hu hAne hBne hUne hA hB hU hplane
            hlowerStrict hupperStrict hTwo hOne
    · obtain ⟨n, haShape, hbShape, huShape⟩ := hAligned
      have hn : 0 < n := by omega
      exact lWall410_aligned_cone_terminal_impossible
        l beta gamma delta zeta eta theta k₂ terminal A B U n hn
          hAne hBne hUne (by omega) (by omega) (by omega) hTwo hTerminal

/-- Source-coordinate form: every positive-degree normalized trajectory on
the `l ≠ 0` wall is excluded by the two first integrals and terminal row. -/
theorem lWall410_all_positive_original_impossible
    (l alpha beta gamma delta epsilon zeta eta theta iota
      k₂ k₁ terminal : k)
    (A B C0 : k[X]) (a b u : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hu : 0 < u) (hl : l ≠ 0)
    (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hA : A.natDegree = a) (hB : B.natDegree = b)
    (hU : (A ^ 2 - (4 : k) • C0).natDegree = u)
    (hTwo : firstIntegralTwoPolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k₂)
    (hOne : firstIntegralOnePolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k₁)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 l alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 l alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) : False := by
  have hUne : A ^ 2 - (4 : k) • C0 ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hU
    omega
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
  have hTerminalD :
      lWallTerminalNumerator410 l beta gamma delta zeta eta theta A B
          (A ^ 2 - (4 : k) • C0) = C (8192 * terminal) := by
    rw [← lowerRow410_discriminantTerminalNumerator, hLower,
      Polynomial.smul_eq_C_mul, ← Polynomial.C_mul]
  exact lWall410_discriminant_all_positive_impossible
    l beta gamma delta zeta eta theta (2048 * k₂) (2048 * k₁)
      (8192 * terminal) A B (A ^ 2 - (4 : k) • C0) a b u
        ha hb hu hl hAne hBne hUne hA hB hU hTwoD hOneD hTerminalD

end LWallFanConnector410

end Max11DegreeRoutes
