import Grok610ScaleZeroConeResidualClosureScratch

/-! # Scale-zero cone final tree for the normalized `(6,10)`, `H = 0` leaf

Continuation of `Grok610ScaleZeroConeResidualClosureScratch` on the
constant core `H = (C t)²`.  That file closed every leftover unique
face of Newton degree greater than one that the cascade still named.
This file continues the same degree / leading-term elimination on the
finite Newton tree of the free core `(A, B, C₀, D₀, E₀)` against the
degree-one primitive.

* If `L ≠ 0` and `deg B < deg A` with the other letters at most
  `deg A`, the face `A⁷ L` is unique of degree `7 deg A ≥ 7`.  In
  particular a shared maximum of `A` with `C₀`, `D₀`, or `E₀` is empty.
* Unique-`A` after the parent `A⁶` cancellation, with `D₀` nonconstant:
  the face `A⁵ D₀` is unique of degree `5 deg A + deg D₀ ≥ 6`.
* Unique-`A` after that cancellation, with `D₀` constant and combined
  `A⁵` coefficient nonzero: the face `A⁵` is unique of degree
  `5 deg A ≥ 5`.
* Unique-`B` on the remaining tie `3 deg A = 2 deg B`, with the
  three-term combination `A⁶ B`, `A³ B³`, `B⁵` of exact degree
  `5 deg B`: that face is unique of degree `5 deg B ≥ 5`.

The leaf is not closed.  Named remaining cones are recorded by
`normalized610ScaleZero_coneFinalResidual`.  No total-degree or
twice-prime theorem is used.  No finite-root shortcut is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Weaker `A`-leading cone and next-face coefficients -/

section FinalCones610

variable {k : Type*} [Field k] [CharZero k]

/-- `A` strictly outranks `B`, and is at least as high as the other
three letters.  This includes unique-`A` and every shared maximum of
`A` with `C₀`, `D₀`, or `E₀`. -/
def AStrictlyOutranksBCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  0 < A.natDegree ∧
    B.natDegree < A.natDegree ∧
    C0.natDegree ≤ A.natDegree ∧
    D0.natDegree ≤ A.natDegree ∧
    E0.natDegree ≤ A.natDegree

/-- Unique-`B` on the remaining Newton tie `3 deg A = 2 deg B`. -/
def HighBTieCone610 (A B C0 D0 E0 : k[X]) : Prop :=
  UniqueHighBCone610 A B C0 D0 E0 ∧
    3 * A.natDegree = 2 * B.natDegree

/-- Combined `A⁵` coefficient on unique-`A` after `A⁶` cancellation,
with `B` and `D₀` of degree zero. -/
def highA_l0_A5Coefficient610 (alpha delta : k) (B D0 : k[X]) : k[X] :=
  (35 / 729 * alpha : k) • B +
    (92160 / 2239488 : k) • D0 +
    C (49 / 5184 * delta : k)

/-- Three-term combination of the unique-`B` tie faces. -/
def highB_tieCombined610 (A B : k[X]) : k[X] :=
  (-(62720 / 2239488 : k)) • (A ^ 6 * B) +
    (343040 / 2239488 : k) • (A ^ 3 * B ^ 3) +
    (-(36864 / 2239488 : k)) • B ^ 5

end FinalCones610

/-! ## Splittings -/

section FinalSplittings610

variable {k : Type*} [Field k] [CharZero k]

private theorem zero_pow_two {R : Type*} [Semiring R] : (0 : R) ^ 2 = 0 :=
  zero_pow (by decide : (2 : ℕ) ≠ 0)

private theorem zero_pow_three {R : Type*} [Semiring R] : (0 : R) ^ 3 = 0 :=
  zero_pow (by decide : (3 : ℕ) ≠ 0)

private theorem zero_pow_four {R : Type*} [Semiring R] : (0 : R) ^ 4 = 0 :=
  zero_pow (by decide : (4 : ℕ) ≠ 0)

private theorem zero_pow_five {R : Type*} [Semiring R] : (0 : R) ^ 5 = 0 :=
  zero_pow (by decide : (5 : ℕ) ≠ 0)

/-- Base group at `L = 0` with `A⁶ B`, `A⁵ C₀`, and `A⁵ D₀` deleted. -/
def degreeZeroBaseGroupHighA_l0_noA6_noA5D0_Rest610
    (A B C0 D0 E0 : k[X]) : k[X] :=
  (491520 / 2239488 : k) • (A ^ 4 * B * C0) +
    (343040 / 2239488 : k) • (A ^ 3 * B ^ 3) -
    (483840 / 2239488 : k) • (A ^ 3 * B * E0) -
    (668160 / 2239488 : k) • (A ^ 3 * C0 * D0) -
    (1071360 / 2239488 : k) • (A ^ 2 * B ^ 2 * D0) -
    (1071360 / 2239488 : k) • (A ^ 2 * B * C0 ^ 2) +
    (622080 / 2239488 : k) • (A ^ 2 * D0 * E0) -
    (737280 / 2239488 : k) • (A * B ^ 3 * C0) +
    (1658880 / 2239488 : k) • (A * B * C0 * E0) +
    (1244160 / 2239488 : k) • (A * B * D0 ^ 2) +
    (1244160 / 2239488 : k) • (A * C0 ^ 2 * D0) -
    (36864 / 2239488 : k) • B ^ 5 +
    (276480 / 2239488 : k) • (B ^ 3 * E0) +
    (1244160 / 2239488 : k) • (B ^ 2 * C0 * D0) +
    (414720 / 2239488 : k) • (B * C0 ^ 3) -
    (2488320 / 2239488 : k) • (C0 * D0 * E0) -
    (829440 / 2239488 : k) • D0 ^ 3

/-- Primitive at `L = 0` with `A⁶` and `A⁵ D₀` deleted. -/
def degreeZeroPrimitiveHighA_l0_noA6_noA5D0_Rest610
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  degreeZeroBaseGroupHighA_l0_noA6_noA5D0_Rest610 A B C0 D0 E0 +
    alpha • degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0 +
    beta • degreeZeroBetaGroupNoA6Polynomial610 A B C0 D0 E0 +
    delta • degreeZeroDeltaGroupPolynomial610 A B C0 D0 +
    epsilon • degreeZeroEpsilonGroupPolynomial610 A B C0 D0 +
    zeta • degreeZeroZetaGroupPolynomial610 A B C0 D0 +
    eta • degreeZeroEtaGroupPolynomial610 A B C0 D0 +
    theta • degreeZeroThetaGroupPolynomial610 A B C0 E0

/-- Alpha group with the face `A⁵ B` deleted. -/
def degreeZeroAlphaGroupNoA5BPolynomial610 (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(51 / 729 : k)) • (A ^ 4 * D0) -
    (222 / 729 : k) • (A ^ 3 * B * C0) -
    (117 / 729 : k) • (A ^ 2 * B ^ 3) +
    (189 / 729 : k) • (A ^ 2 * B * E0) +
    (297 / 729 : k) • (A ^ 2 * C0 * D0) +
    (324 / 729 : k) • (A * B ^ 2 * D0) +
    (324 / 729 : k) • (A * B * C0 ^ 2) -
    (324 / 729 : k) • (A * D0 * E0) +
    (108 / 729 : k) • (B ^ 3 * C0) -
    (324 / 729 : k) • (B * C0 * E0) -
    (324 / 729 : k) • (B * D0 ^ 2) -
    (324 / 729 : k) • (C0 ^ 2 * D0)

/-- Primitive at `L = 0` with `A⁶` deleted and both `A⁵` faces
(the `D₀` face, the load `δ A⁵`, and `α A⁵ B`) deleted. -/
def degreeZeroPrimitiveHighA_l0_noA6_noA5_Rest610
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  degreeZeroBaseGroupHighA_l0_noA6_noA5D0_Rest610 A B C0 D0 E0 +
    alpha • degreeZeroAlphaGroupNoA5BPolynomial610 A B C0 D0 E0 +
    beta • degreeZeroBetaGroupNoA6Polynomial610 A B C0 D0 E0 +
    delta • degreeZeroDeltaGroupNoA5Polynomial610 A B C0 D0 +
    epsilon • degreeZeroEpsilonGroupPolynomial610 A B C0 D0 +
    zeta • degreeZeroZetaGroupPolynomial610 A B C0 D0 +
    eta • degreeZeroEtaGroupPolynomial610 A B C0 D0 +
    theta • degreeZeroThetaGroupPolynomial610 A B C0 E0

/-- Base group with `A⁶ B`, `A³ B³`, and `B⁵` deleted. -/
def degreeZeroBaseGroupNoHighBTieRest610
    (l : k) (A B C0 D0 E0 : k[X]) : k[X] :=
  (-(10935 / 2239488 * l : k)) • A ^ 7 +
    (113724 / 2239488 * l : k) • (A ^ 5 * C0) +
    (92160 / 2239488 : k) • (A ^ 5 * D0) +
    (301806 / 2239488 * l : k) • (A ^ 4 * B ^ 2) +
    (491520 / 2239488 : k) • (A ^ 4 * B * C0) -
    (122472 / 2239488 * l : k) • (A ^ 4 * E0) -
    (769824 / 2239488 * l : k) • (A ^ 3 * B * D0) -
    (483840 / 2239488 : k) • (A ^ 3 * B * E0) -
    (384912 / 2239488 * l : k) • (A ^ 3 * C0 ^ 2) -
    (668160 / 2239488 : k) • (A ^ 3 * C0 * D0) -
    (1224720 / 2239488 * l : k) • (A ^ 2 * B ^ 2 * C0) -
    (1071360 / 2239488 : k) • (A ^ 2 * B ^ 2 * D0) -
    (1071360 / 2239488 : k) • (A ^ 2 * B * C0 ^ 2) +
    (699840 / 2239488 * l : k) • (A ^ 2 * C0 * E0) +
    (559872 / 2239488 * l : k) • (A ^ 2 * D0 ^ 2) +
    (622080 / 2239488 : k) • (A ^ 2 * D0 * E0) -
    (209952 / 2239488 * l : k) • (A * B ^ 4) -
    (737280 / 2239488 : k) • (A * B ^ 3 * C0) +
    (839808 / 2239488 * l : k) • (A * B ^ 2 * E0) +
    (2519424 / 2239488 * l : k) • (A * B * C0 * D0) +
    (1658880 / 2239488 : k) • (A * B * C0 * E0) +
    (1244160 / 2239488 : k) • (A * B * D0 ^ 2) +
    (419904 / 2239488 * l : k) • (A * C0 ^ 3) +
    (1244160 / 2239488 : k) • (A * C0 ^ 2 * D0) +
    (419904 / 2239488 * l : k) • (B ^ 3 * D0) +
    (276480 / 2239488 : k) • (B ^ 3 * E0) +
    (629856 / 2239488 * l : k) • (B ^ 2 * C0 ^ 2) +
    (1244160 / 2239488 : k) • (B ^ 2 * C0 * D0) +
    (414720 / 2239488 : k) • (B * C0 ^ 3) -
    (1679616 / 2239488 * l : k) • (B * D0 * E0) -
    (839808 / 2239488 * l : k) • (C0 ^ 2 * E0) -
    (1679616 / 2239488 * l : k) • (C0 * D0 ^ 2) -
    (2488320 / 2239488 : k) • (C0 * D0 * E0) -
    (829440 / 2239488 : k) • D0 ^ 3

/-- Primitive with the three unique-`B` tie faces deleted. -/
def degreeZeroPrimitiveNoHighBTieRest610
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) : k[X] :=
  degreeZeroBaseGroupNoHighBTieRest610 l A B C0 D0 E0 +
    alpha • degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0 +
    beta • degreeZeroBetaGroupPolynomial610 A B C0 D0 E0 +
    delta • degreeZeroDeltaGroupPolynomial610 A B C0 D0 +
    epsilon • degreeZeroEpsilonGroupPolynomial610 A B C0 D0 +
    zeta • degreeZeroZetaGroupPolynomial610 A B C0 D0 +
    eta • degreeZeroEtaGroupPolynomial610 A B C0 D0 +
    theta • degreeZeroThetaGroupPolynomial610 A B C0 E0

set_option maxHeartbeats 16000000 in
theorem degreeZeroBaseGroupHighA_noA6B_Rest610_l0_eq_A5D0_add
    (A B C0 D0 E0 : k[X]) :
    degreeZeroBaseGroupHighA_noA6B_Rest610 0 A B C0 D0 E0 =
      (92160 / 2239488 : k) • (A ^ 5 * D0) +
        degreeZeroBaseGroupHighA_l0_noA6_noA5D0_Rest610 A B C0 D0 E0 := by
  simp only [degreeZeroBaseGroupHighA_noA6B_Rest610,
    degreeZeroBaseGroupHighA_l0_noA6_noA5D0_Rest610, zero_mul, mul_zero,
    neg_zero, zero_smul, smul_zero, zero_add, add_zero, sub_zero]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitiveHighA_l0_noA6_Rest610_eq_A5D0_add
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroPrimitiveHighA_l0_noA6_Rest610 alpha beta delta epsilon
        zeta eta theta A B C0 D0 E0 =
      (92160 / 2239488 : k) • (A ^ 5 * D0) +
        degreeZeroPrimitiveHighA_l0_noA6_noA5D0_Rest610 alpha beta delta
          epsilon zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroPrimitiveHighA_l0_noA6_Rest610,
    degreeZeroPrimitiveHighA_l0_noA6_noA5D0_Rest610,
    degreeZeroBaseGroupHighA_noA6B_Rest610_l0_eq_A5D0_add]
  module

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitiveHighA_l0_noA6_Rest610_eq_A5_faces_add
    (alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroPrimitiveHighA_l0_noA6_Rest610 alpha beta delta epsilon
        zeta eta theta A B C0 D0 E0 =
      (35 / 729 * alpha : k) • (A ^ 5 * B) +
        (92160 / 2239488 : k) • (A ^ 5 * D0) +
          ((49 / 5184 * delta : k) • A ^ 5) +
            degreeZeroPrimitiveHighA_l0_noA6_noA5_Rest610 alpha beta delta
              epsilon zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroPrimitiveHighA_l0_noA6_Rest610,
    degreeZeroPrimitiveHighA_l0_noA6_noA5_Rest610,
    degreeZeroBaseGroupHighA_noA6B_Rest610,
    degreeZeroBaseGroupHighA_l0_noA6_noA5D0_Rest610,
    degreeZeroAlphaGroupPolynomial610,
    degreeZeroAlphaGroupNoA5BPolynomial610,
    degreeZeroDeltaGroupPolynomial610,
    degreeZeroDeltaGroupNoA5Polynomial610, zero_mul, mul_zero, neg_zero,
    zero_smul, smul_zero, zero_add, add_zero, sub_zero]
  module

theorem highA_l0_A5_combined_eq
    (alpha delta : k) (A B D0 : k[X]) :
    (35 / 729 * alpha : k) • (A ^ 5 * B) +
        (92160 / 2239488 : k) • (A ^ 5 * D0) +
          ((49 / 5184 * delta : k) • A ^ 5) =
      A ^ 5 * highA_l0_A5Coefficient610 alpha delta B D0 := by
  simp only [highA_l0_A5Coefficient610, smul_eq_C_mul]
  ring

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitivePolynomial610_eq_highBTie_add_rest
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X]) :
    degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0 =
      highB_tieCombined610 A B +
        degreeZeroPrimitiveNoHighBTieRest610 l alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0 := by
  simp only [degreeZeroPrimitivePolynomial610, highB_tieCombined610,
    degreeZeroPrimitiveNoHighBTieRest610, degreeZeroBaseGroupPolynomial610,
    degreeZeroBaseGroupNoHighBTieRest610]
  module

end FinalSplittings610

/-! ## `A⁷` still unique when `C₀, D₀, E₀` may tie `A` -/

section A7WeakerCone610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitiveHighARest610_natDegree_lt_of_A_outranks_B
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 : k[X])
    (hcone : AStrictlyOutranksBCone610 A B C0 D0 E0) :
    (degreeZeroPrimitiveHighARest610 l alpha beta delta epsilon zeta eta
        theta A B C0 D0 E0).natDegree <
      7 * A.natDegree := by
  rcases hcone with ⟨hApos, hB, hC, hD, hE⟩
  have hbase :
      (degreeZeroBaseGroupHighARest610 l A B C0 D0 E0).natDegree <
        7 * A.natDegree := by
    simp only [degreeZeroBaseGroupHighARest610]
    compute_degree
    omega
  have halpha :
      (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
        7 * A.natDegree := by
    simp only [degreeZeroAlphaGroupPolynomial610]
    compute_degree
    omega
  have hbeta :
      (degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).natDegree <
        7 * A.natDegree := by
    simp only [degreeZeroBetaGroupPolynomial610]
    compute_degree
    omega
  have hdelta :
      (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
        7 * A.natDegree := by
    simp only [degreeZeroDeltaGroupPolynomial610]
    compute_degree
    omega
  have hepsilon :
      (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
        7 * A.natDegree := by
    simp only [degreeZeroEpsilonGroupPolynomial610]
    compute_degree
    omega
  have hzeta :
      (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
        7 * A.natDegree := by
    simp only [degreeZeroZetaGroupPolynomial610]
    compute_degree
    omega
  have heta :
      (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
        7 * A.natDegree := by
    simp only [degreeZeroEtaGroupPolynomial610]
    compute_degree
    omega
  have htheta :
      (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
        7 * A.natDegree := by
    simp only [degreeZeroThetaGroupPolynomial610]
    compute_degree
    omega
  simp only [degreeZeroPrimitiveHighARest610]
  exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
    (natDegree_smul_lt610 beta hbeta) (natDegree_smul_lt610 delta hdelta)
    (natDegree_smul_lt610 epsilon hepsilon) (natDegree_smul_lt610 zeta hzeta)
    (natDegree_smul_lt610 eta heta) (natDegree_smul_lt610 theta htheta)

theorem a7_leads_impossible_of_l_ne
    (l alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hl : l ≠ 0) (hj : j ≠ 0)
    (hcone : AStrictlyOutranksBCone610 A B C0 D0 E0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hc : (-(10935 / 2239488 * l : k)) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hl)
  have hlead :
      ((-(10935 / 2239488 * l : k)) • A ^ 7).natDegree =
        7 * A.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroPrimitiveHighARest610_natDegree_lt_of_A_outranks_B l alpha
      beta delta epsilon zeta eta theta A B C0 D0 E0 hcone
  rw [degreeZeroPrimitivePolynomial610_eq_A7_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

end A7WeakerCone610

/-! ## Unique-`A` after `A⁶` cancellation -/

section HighAFinal610

variable {k : Type*} [Field k] [CharZero k]

theorem highA_l0_A5Coefficient610_natDegree_eq_zero
    (alpha delta : k) {B D0 : k[X]}
    (hB : B.natDegree = 0) (hD : D0.natDegree = 0) :
    (highA_l0_A5Coefficient610 alpha delta B D0).natDegree = 0 := by
  have hB' : ((35 / 729 * alpha : k) • B).natDegree ≤ 0 :=
    (natDegree_smul_le610 _ B).trans hB.le
  have hD' : ((92160 / 2239488 : k) • D0).natDegree ≤ 0 :=
    (natDegree_smul_le610 _ D0).trans hD.le
  have hc : (C (49 / 5184 * delta : k) : k[X]).natDegree = 0 :=
    natDegree_C _
  change ((35 / 729 * alpha : k) • B + (92160 / 2239488 : k) • D0 +
      C (49 / 5184 * delta : k)).natDegree = 0
  exact natDegree_eq_zero_of_le_zero <|
    (natDegree_add_le _ _).trans <| max_le
      ((natDegree_add_le _ _).trans (max_le hB' hD')) hc.le

set_option maxHeartbeats 16000000 in
theorem uniqueHighA_impossible_of_A6cancel_D0_pos
    (alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hcone : UniqueHighACone610 A B C0 D0 E0)
    (hB : B.natDegree = 0)
    (hK6 : highA_l0_constB_A6Coefficient610 beta B = 0)
    (hDpos : 0 < D0.natDegree)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 0 alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 0 alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hDne : D0 ≠ 0 := by
    intro hD0
    simp [hD0] at hDpos
  have hc : (92160 / 2239488 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead :
      ((92160 / 2239488 : k) • (A ^ 5 * D0)).natDegree =
        5 * A.natDegree + D0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 5 hA) hDne,
      natDegree_pow]
  have hrest :
      (degreeZeroPrimitiveHighA_l0_noA6_noA5D0_Rest610 alpha beta delta
          epsilon zeta eta theta A B C0 D0 E0).natDegree <
        5 * A.natDegree + D0.natDegree := by
    rcases hcone with ⟨hApos, hBlt, hC, hDlt, hE⟩
    have hbase :
        (degreeZeroBaseGroupHighA_l0_noA6_noA5D0_Rest610 A B C0 D0
            E0).natDegree <
          5 * A.natDegree + D0.natDegree := by
      simp only [degreeZeroBaseGroupHighA_l0_noA6_noA5D0_Rest610, zero_mul,
        mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
        zero_pow_four, zero_pow_five]
      compute_degree
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
          5 * A.natDegree + D0.natDegree := by
      simp only [degreeZeroAlphaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hbetaG :
        (degreeZeroBetaGroupNoA6Polynomial610 A B C0 D0 E0).natDegree <
          5 * A.natDegree + D0.natDegree := by
      simp only [degreeZeroBetaGroupNoA6Polynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
          5 * A.natDegree + D0.natDegree := by
      simp only [degreeZeroDeltaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
          5 * A.natDegree + D0.natDegree := by
      simp only [degreeZeroEpsilonGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
          5 * A.natDegree + D0.natDegree := by
      simp only [degreeZeroZetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
          5 * A.natDegree + D0.natDegree := by
      simp only [degreeZeroEtaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
          5 * A.natDegree + D0.natDegree := by
      simp only [degreeZeroThetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    simp only [degreeZeroPrimitiveHighA_l0_noA6_noA5D0_Rest610]
    exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
      (natDegree_smul_lt610 beta hbetaG) (natDegree_smul_lt610 delta hdelta)
      (natDegree_smul_lt610 epsilon hepsilon)
      (natDegree_smul_lt610 zeta hzeta) (natDegree_smul_lt610 eta heta)
      (natDegree_smul_lt610 theta htheta)
  rw [degreeZeroPrimitivePolynomial610_eq_A6_combined_add_rest,
    highA_l0_constB_A6_combined_eq, hK6, mul_zero, zero_add,
    degreeZeroPrimitiveHighA_l0_noA6_Rest610_eq_A5D0_add,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

set_option maxHeartbeats 16000000 in
theorem uniqueHighA_impossible_of_A6cancel_A5_ne
    (alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hcone : UniqueHighACone610 A B C0 D0 E0)
    (hB : B.natDegree = 0) (hD : D0.natDegree = 0)
    (hK6 : highA_l0_constB_A6Coefficient610 beta B = 0)
    (hK5 : highA_l0_A5Coefficient610 alpha delta B D0 ≠ 0)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 0 alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 0 alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hK5deg :
      (highA_l0_A5Coefficient610 alpha delta B D0).natDegree = 0 :=
    highA_l0_A5Coefficient610_natDegree_eq_zero alpha delta hB hD
  have hlead :
      (A ^ 5 * highA_l0_A5Coefficient610 alpha delta B D0).natDegree =
        5 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 5 hA) hK5, natDegree_pow, hK5deg,
      add_zero]
  have hrest :
      (degreeZeroPrimitiveHighA_l0_noA6_noA5_Rest610 alpha beta delta
          epsilon zeta eta theta A B C0 D0 E0).natDegree <
        5 * A.natDegree := by
    rcases hcone with ⟨hApos, hBlt, hC, hDlt, hE⟩
    have hbase :
        (degreeZeroBaseGroupHighA_l0_noA6_noA5D0_Rest610 A B C0 D0
            E0).natDegree <
          5 * A.natDegree := by
      simp only [degreeZeroBaseGroupHighA_l0_noA6_noA5D0_Rest610, zero_mul,
        mul_zero, zero_smul, smul_zero, zero_pow_two, zero_pow_three,
        zero_pow_four, zero_pow_five]
      compute_degree
      omega
    have halpha :
        (degreeZeroAlphaGroupNoA5BPolynomial610 A B C0 D0 E0).natDegree <
          5 * A.natDegree := by
      simp only [degreeZeroAlphaGroupNoA5BPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hbetaG :
        (degreeZeroBetaGroupNoA6Polynomial610 A B C0 D0 E0).natDegree <
          5 * A.natDegree := by
      simp only [degreeZeroBetaGroupNoA6Polynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hdelta :
        (degreeZeroDeltaGroupNoA5Polynomial610 A B C0 D0).natDegree <
          5 * A.natDegree := by
      simp only [degreeZeroDeltaGroupNoA5Polynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
          5 * A.natDegree := by
      simp only [degreeZeroEpsilonGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
          5 * A.natDegree := by
      simp only [degreeZeroZetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
          5 * A.natDegree := by
      simp only [degreeZeroEtaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
          5 * A.natDegree := by
      simp only [degreeZeroThetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    simp only [degreeZeroPrimitiveHighA_l0_noA6_noA5_Rest610]
    exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
      (natDegree_smul_lt610 beta hbetaG) (natDegree_smul_lt610 delta hdelta)
      (natDegree_smul_lt610 epsilon hepsilon)
      (natDegree_smul_lt610 zeta hzeta) (natDegree_smul_lt610 eta heta)
      (natDegree_smul_lt610 theta htheta)
  rw [degreeZeroPrimitivePolynomial610_eq_A6_combined_add_rest,
    highA_l0_constB_A6_combined_eq, hK6, mul_zero, zero_add,
    degreeZeroPrimitiveHighA_l0_noA6_Rest610_eq_A5_faces_add,
    highA_l0_A5_combined_eq,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega

end HighAFinal610

/-! ## Unique-`B` tie `3 deg A = 2 deg B` -/

section HighBTie610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem uniqueHighB_tie_impossible_of_combined_degree
    (l alpha beta delta epsilon zeta eta theta j : k)
    (A B C0 D0 E0 : k[X]) (hj : j ≠ 0)
    (hcone : HighBTieCone610 A B C0 D0 E0)
    (hcomb :
      (highB_tieCombined610 A B).natDegree = 5 * B.natDegree)
    (hder :
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C j) :
    False := by
  have hdeg :
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610 _ j hj hder
  rcases hcone with ⟨⟨hBpos, hA, hC, hD, hE⟩, htie⟩
  have hrest :
      (degreeZeroPrimitiveNoHighBTieRest610 l alpha beta delta epsilon
          zeta eta theta A B C0 D0 E0).natDegree <
        5 * B.natDegree := by
    have hbase :
        (degreeZeroBaseGroupNoHighBTieRest610 l A B C0 D0 E0).natDegree <
          5 * B.natDegree := by
      simp only [degreeZeroBaseGroupNoHighBTieRest610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have halpha :
        (degreeZeroAlphaGroupPolynomial610 A B C0 D0 E0).natDegree <
          5 * B.natDegree := by
      simp only [degreeZeroAlphaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hbetaG :
        (degreeZeroBetaGroupPolynomial610 A B C0 D0 E0).natDegree <
          5 * B.natDegree := by
      simp only [degreeZeroBetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hdelta :
        (degreeZeroDeltaGroupPolynomial610 A B C0 D0).natDegree <
          5 * B.natDegree := by
      simp only [degreeZeroDeltaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hepsilon :
        (degreeZeroEpsilonGroupPolynomial610 A B C0 D0).natDegree <
          5 * B.natDegree := by
      simp only [degreeZeroEpsilonGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have hzeta :
        (degreeZeroZetaGroupPolynomial610 A B C0 D0).natDegree <
          5 * B.natDegree := by
      simp only [degreeZeroZetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have heta :
        (degreeZeroEtaGroupPolynomial610 A B C0 D0).natDegree <
          5 * B.natDegree := by
      simp only [degreeZeroEtaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    have htheta :
        (degreeZeroThetaGroupPolynomial610 A B C0 E0).natDegree <
          5 * B.natDegree := by
      simp only [degreeZeroThetaGroupPolynomial610, zero_mul, mul_zero,
        zero_smul, smul_zero, zero_pow_two, zero_pow_three, zero_pow_four,
        zero_pow_five]
      compute_degree
      omega
    simp only [degreeZeroPrimitiveNoHighBTieRest610]
    exact natDegree_add8_lt610 hbase (natDegree_smul_lt610 alpha halpha)
      (natDegree_smul_lt610 beta hbetaG) (natDegree_smul_lt610 delta hdelta)
      (natDegree_smul_lt610 epsilon hepsilon)
      (natDegree_smul_lt610 zeta hzeta) (natDegree_smul_lt610 eta heta)
      (natDegree_smul_lt610 theta htheta)
  rw [degreeZeroPrimitivePolynomial610_eq_highBTie_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hcomb]), hcomb] at hdeg
  omega

end HighBTie610

/-! ## Honest residual -/

section ConeFinalResidual610

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 16000000

/-- Exact residual after the next unique-face layer of the scale-zero
cone tree.

The free core has polynomial representatives and the integrated primitive
has Newton degree one.  In addition to the parent residual-closure, a
core in which `A` strictly outranks `B` with `L ≠ 0` is empty (including
every shared maximum of `A` with `C₀`, `D₀`, or `E₀`), and the
unique-`B` tie `3 deg A = 2 deg B` is empty unless the three-term
combination has degree strictly below `5 deg B`.  Standalone lemmas
also empty unique-`A` after `A⁶` cancellation when `D₀` is nonconstant,
or when `D₀` is constant and the combined `A⁵` coefficient is nonzero.

Remaining named cones: unique-`A` after both `A⁶` and `A⁵` cancellation;
unique nonconstant `C₀` with vanishing cubic; unique nonconstant `E₀`
of degree one with `β = 0` and nonzero linear coefficient; the
unique-`B` tie with dropped three-term combination; unique-high `C₀`,
`D₀`, or `E₀` with another letter nonconstant; and every remaining
shared-maximum cone in which `A` does not strictly outrank `B`.  The
already-constant first integrals `κ, λ, μ` and the weight-seventy
residual `ο` are not consumed. -/
theorem normalized610ScaleZero_coneFinalResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron l alpha beta gamma delta epsilon zeta eta theta
        iota : k) (A B C0 D0 E0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon
            zeta eta theta A B C0 D0 E0) =
        C (j / t) ∧
      (degreeZeroPrimitivePolynomial610 l alpha beta delta epsilon zeta
          eta theta A B C0 D0 E0).natDegree =
        1 ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0) ∧
      (UniqueHighACone610 A B C0 D0 E0 →
        l = 0 ∧ B.natDegree = 0 ∧ (B = 0 → beta = 0) ∧
          (B ≠ 0 → highA_l0_constB_A6Coefficient610 beta B = 0) ∧
          (B = 0 →
            D0.natDegree = 0 ∧ D0 ≠ 0 ∧
              highA_l0_B0_beta0_A5Coefficient610 delta D0 = 0)) ∧
      (AStrictlyOutranksBCone610 A B C0 D0 E0 → l = 0) ∧
      ¬ ExtremeHighBCone610 A B C0 D0 E0 ∧
      ¬ A6BLeadsHighBCone610 A B C0 D0 E0 ∧
      ¬ (HighBTieCone610 A B C0 D0 E0 ∧
          (highB_tieCombined610 A B).natDegree = 5 * B.natDegree) ∧
      ¬ (A.natDegree = 0 ∧ 0 < B.natDegree ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          0 < D0.natDegree ∧ E0.natDegree = 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ 0 < E0.natDegree ∧ beta ≠ 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ 0 < C0.natDegree ∧
          D0.natDegree = 0 ∧ E0.natDegree = 0 ∧
          uniqueC0_cubicCoefficient610 l beta A B ≠ 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          D0.natDegree = 0 ∧ 1 < E0.natDegree ∧ beta = 0) ∧
      ¬ (A.natDegree = 0 ∧ B.natDegree = 0 ∧ C0.natDegree = 0 ∧
          0 < D0.natDegree ∧ E0.natDegree < 2 * D0.natDegree ∧
          beta = 0) := by
  obtain ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
      zeta, eta, theta, iota, A, B, C0, D0, E0, ht, hj, hjdiv, hHsq,
      hder, hdeg, hnonconst, hHighA, hExtB, hA6B, hBonly, hDonly, hEonly,
      hCcubic, hEge2, hDmix⟩ :=
    normalized610ScaleZero_coneResidualClosureResidual hsource
  refine ⟨t, j, lambda, omicron, l, alpha, beta, gamma, delta, epsilon,
    zeta, eta, theta, iota, A, B, C0, D0, E0, ht, hj, hjdiv, hHsq, hder,
    hdeg, hnonconst, hHighA, ?_, hExtB, hA6B, ?_, hBonly, hDonly, hEonly,
    hCcubic, hEge2, hDmix⟩
  · intro hcone
    by_contra hlne
    exact a7_leads_impossible_of_l_ne l alpha beta delta epsilon zeta eta
      theta (j / t) A B C0 D0 E0 hlne hjdiv hcone hder
  · intro htie
    exact uniqueHighB_tie_impossible_of_combined_degree l alpha beta delta
      epsilon zeta eta theta (j / t) A B C0 D0 E0 hjdiv htie.1 htie.2 hder

end ConeFinalResidual610

#print axioms AStrictlyOutranksBCone610
#print axioms HighBTieCone610
#print axioms highA_l0_A5Coefficient610
#print axioms highB_tieCombined610
#print axioms a7_leads_impossible_of_l_ne
#print axioms uniqueHighA_impossible_of_A6cancel_D0_pos
#print axioms uniqueHighA_impossible_of_A6cancel_A5_ne
#print axioms uniqueHighB_tie_impossible_of_combined_degree
#print axioms normalized610ScaleZero_coneFinalResidual

end Max11DegreeRoutes
