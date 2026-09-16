import Grok68VanishingAOrder4CompanionSplitPart101Scratch

/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 9 of 26, so that no single
module retains all the reflective bridge proof terms at once.
Statements unchanged. -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
/-- The fourth clean coefficient split, with shared degree bounds. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_clean_fourth_split68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let i0 := 4 * N - 5
    let i2 := 2 * N - 5
    let W0 := FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68
      gamma epsilon A B c d e
    let W2 := FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68
      gamma epsilon B c d
    (N = 7 ∧ S = 9 ∧
      W0.coeff i0 =
        -(21 : k) * gamma * A.coeff (2 * N) * B.coeff (D - 3) * c.coeff Cc -
        (39 / 2 : k) * gamma * A.coeff (2 * N - 1) * B.coeff (D - 2) *
          c.coeff Cc -
        (18 : k) * gamma * A.coeff (2 * N - 2) * B.coeff (D - 1) * c.coeff Cc -
        (33 / 2 : k) * gamma * A.coeff (2 * N - 3) * B.coeff D * c.coeff Cc -
        (21 : k) * gamma * A.coeff (2 * N) * B.coeff (D - 2) * c.coeff (Cc - 1) -
        (39 / 2 : k) * gamma * A.coeff (2 * N - 1) * B.coeff (D - 1) *
          c.coeff (Cc - 1) -
        (18 : k) * gamma * A.coeff (2 * N - 2) * B.coeff D * c.coeff (Cc - 1) -
        (21 : k) * gamma * A.coeff (2 * N) * B.coeff (D - 1) * c.coeff (Cc - 2) -
        (39 / 2 : k) * gamma * A.coeff (2 * N - 1) * B.coeff D *
          c.coeff (Cc - 2) -
        (21 : k) * gamma * A.coeff (2 * N) * B.coeff D * c.coeff (Cc - 3) ∧
      W2.coeff i2 = (90 : k) * gamma *
        (B.coeff (D - 3) * c.coeff Cc + B.coeff (D - 2) * c.coeff (Cc - 1) +
          B.coeff (D - 1) * c.coeff (Cc - 2) + B.coeff D * c.coeff (Cc - 3))) ∨
    (N = 14 ∧ S = 18 ∧
      W0.coeff i0 =
        -(42 : k) * gamma * A.coeff (2 * N) * B.coeff (D - 2) * c.coeff Cc -
        (81 / 2 : k) * gamma * A.coeff (2 * N - 1) * B.coeff (D - 1) *
          c.coeff Cc -
        (39 : k) * gamma * A.coeff (2 * N - 2) * B.coeff D * c.coeff Cc -
        (42 : k) * gamma * A.coeff (2 * N) * B.coeff (D - 1) * c.coeff (Cc - 1) -
        (81 / 2 : k) * gamma * A.coeff (2 * N - 1) * B.coeff D *
          c.coeff (Cc - 1) -
        (42 : k) * gamma * A.coeff (2 * N) * B.coeff D * c.coeff (Cc - 2) ∧
      W2.coeff i2 = (216 : k) * gamma *
        (B.coeff (D - 2) * c.coeff Cc + B.coeff (D - 1) * c.coeff (Cc - 1) +
          B.coeff D * c.coeff (Cc - 2))) ∨
    (N = 21 ∧ S = 27 ∧
      W0.coeff i0 =
        -(63 : k) * gamma * A.coeff (2 * N) * B.coeff (D - 1) * c.coeff Cc -
        (123 / 2 : k) * gamma * A.coeff (2 * N - 1) * B.coeff D * c.coeff Cc -
        (63 : k) * gamma * A.coeff (2 * N) * B.coeff D * c.coeff (Cc - 1) ∧
      W2.coeff i2 = (342 : k) * gamma *
        (B.coeff (D - 1) * c.coeff Cc + B.coeff D * c.coeff (Cc - 1))) ∨
    (N = 28 ∧ S = 36 ∧
      W0.coeff i0 = -(84 : k) * gamma * A.coeff (2 * N) * B.coeff D * c.coeff Cc ∧
      W2.coeff i2 = (468 : k) * gamma * B.coeff D * c.coeff Cc) ∨
    (35 ≤ N ∧ W0.coeff i0 = 0 ∧ W2.coeff i2 = 0) := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  let i0 := 4 * N - 5
  let i2 := 2 * N - 5
  let W0 := FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68
    gamma epsilon A B c d e
  let W2 := FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68
    gamma epsilon B c d
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS, hGamma, hsource⟩
  have hp := hsource
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS, hSR, hd, he, hp, hrest⟩
  rcases hp with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  rcases hs.1 with ⟨hsupport, hrows⟩
  rcases hsupport with ⟨hstop, hTD⟩
  have hEq : 9 * N = 7 * S := by
    clear * - hTD hq
    dsimp only at hTD
    omega
  have hB' : B.natDegree ≤ D := by simpa [D, hGS] using hB
  have hc' : c.natDegree ≤ Cc := by simpa [Cc, hGS] using hc
  have hd' : d.natDegree ≤ V := by
    dsimp only [V]
    rw [hGS] at hd
    clear * - hd
    omega
  have he' : e.natDegree ≤ E := by
    dsimp only [E]
    rw [hGS] at he
    clear * - he
    omega
  clear * - D Cc V E i0 i2 W0 W2 hEq hN hA hB' hc' hd' he'
  have harith : (N = 7 ∧ S = 9) ∨ (N = 14 ∧ S = 18) ∨ (N = 21 ∧ S = 27) ∨
      (N = 28 ∧ S = 36) ∨ 35 ≤ N := by
    clear * - hEq hN
    omega
  have hdecomp0 :
      FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68
          gamma epsilon A B c d e =
        -(3 / 2 * gamma : k) • (B * derivative A * c) +
          ((3 : k) • (B * d * derivative d) + (3 : k) • (derivative B * d ^ 2) -
            (9 / 2 * gamma : k) • (B * derivative e) +
            (9 / 2 * gamma : k) • (d * derivative c) +
            (9 / 4 * epsilon : k) • (d * derivative A)) := by
    dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportCleanRowZeroRemainder68]
    module
  have hdecomp2 :
      FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68
          gamma epsilon B c d =
        (9 * gamma : k) • derivative (B * c) -
          (27 / 2 * epsilon : k) • derivative d := by
    dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportCleanRowTwoRemainder68]
    rw [derivative_mul, mul_comm (derivative B) c]
    module
  -- Bound each derivative and product once, before specialising N and S.
  have hderA : (derivative A).natDegree ≤ 2 * N - 1 :=
    (natDegree_derivative_le A).trans (Nat.sub_le_sub_right hA 1)
  have hderB : (derivative B).natDegree ≤ D - 1 :=
    (natDegree_derivative_le B).trans (Nat.sub_le_sub_right hB' 1)
  have hderc : (derivative c).natDegree ≤ Cc - 1 :=
    (natDegree_derivative_le c).trans (Nat.sub_le_sub_right hc' 1)
  have hderd : (derivative d).natDegree ≤ V - 1 :=
    (natDegree_derivative_le d).trans (Nat.sub_le_sub_right hd' 1)
  have hdere : (derivative e).natDegree ≤ E - 1 :=
    (natDegree_derivative_le e).trans (Nat.sub_le_sub_right he' 1)
  have hdegBdd := (natDegree_smul_le (3 : k) (B * d * derivative d)).trans
    (natDegree_mul_le_of_le (natDegree_mul_le_of_le hB' hd') hderd)
  have hdegdBdd := (natDegree_smul_le (3 : k) (derivative B * d ^ 2)).trans
    (natDegree_mul_le_of_le hderB (natDegree_pow_le_of_le 2 hd'))
  have hdegBe := (natDegree_smul_le (9 / 2 * gamma : k) (B * derivative e)).trans
    (natDegree_mul_le_of_le hB' hdere)
  have hdegdc := (natDegree_smul_le (9 / 2 * gamma : k) (d * derivative c)).trans
    (natDegree_mul_le_of_le hd' hderc)
  have hdegdA := (natDegree_smul_le (9 / 4 * epsilon : k) (d * derivative A)).trans
    (natDegree_mul_le_of_le hd' hderA)
  have hlow0 : ((3 : k) • (B * d * derivative d) +
          (3 : k) • (derivative B * d ^ 2) -
          (9 / 2 * gamma : k) • (B * derivative e) +
          (9 / 2 * gamma : k) • (d * derivative c) +
          (9 / 4 * epsilon : k) • (d * derivative A)).natDegree < i0 := by
    have hdeg := natDegree_add_le_of_le
      (natDegree_add_le_of_le
        (natDegree_sub_le_of_le (natDegree_add_le_of_le hdegBdd hdegdBdd) hdegBe)
        hdegdc) hdegdA
    dsimp only [D, Cc, V, E, i0] at hdeg ⊢
    clear * - hEq hN hdeg
    omega
  have hlow2 : ((27 / 2 * epsilon : k) • derivative d).natDegree < i2 := by
    have hdeg := (natDegree_smul_le (27 / 2 * epsilon : k) (derivative d)).trans hderd
    dsimp only [V, i2] at hdeg ⊢
    clear * - hEq hN hdeg
    omega
  have hmain0 :=
    (natDegree_smul_le (-(3 / 2 * gamma : k)) (B * derivative A * c)).trans
      (natDegree_mul_le_of_le (natDegree_mul_le_of_le hB' hderA) hc')
  have hmain2 :=
    (natDegree_smul_le (9 * gamma : k) (derivative (B * c))).trans
      ((natDegree_derivative_le (B * c)).trans
        (Nat.sub_le_sub_right (natDegree_mul_le_of_le hB' hc') 1))
  rcases harith with h7 | h14 | h21 | h28 | hlarge
  · left
    rcases h7 with ⟨hN7, hS9⟩
    subst N; subst S
    simp only [i0, i2, Nat.reduceMul, Nat.reduceSub] at hlow0 hlow2
    dsimp only [D, Cc, V, E] at hB' hc' hd' he'
    have hdA : (derivative A).natDegree ≤ 13 := by
      exact (natDegree_derivative_le A).trans (Nat.sub_le_sub_right hA 1)
    have hBAc := coeff_mul_mul_three_below_bounds68 B (derivative A) c
      3 13 10 (by decide) (by decide) (by decide) hB' hdA hc'
    norm_num only [coeff_derivative] at hBAc
    have hBc := coeff_mul_three_below_bounds68 B c 3 10
      (by decide) (by decide) hB' hc'
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simp only [hdecomp0, coeff_add, coeff_smul, hBAc,
        coeff_eq_zero_of_natDegree_lt hlow0, smul_eq_mul, add_zero]
      norm_num only [D, Cc, i0]
      ring
    · simp only [hdecomp2, coeff_sub, coeff_smul, coeff_derivative, hBc,
        coeff_eq_zero_of_natDegree_lt hlow2, smul_eq_mul, sub_zero]
      norm_num only [D, Cc, i2]
      ring
  · right; left
    rcases h14 with ⟨hN14, hS18⟩
    subst N; subst S
    simp only [i0, i2, Nat.reduceMul, Nat.reduceSub] at hlow0 hlow2
    dsimp only [D, Cc, V, E] at hB' hc' hd' he'
    have hdA : (derivative A).natDegree ≤ 27 := by
      exact (natDegree_derivative_le A).trans (Nat.sub_le_sub_right hA 1)
    have hBAc := coeff_mul_mul_two_below_bounds68 B (derivative A) c
      6 27 20 (by decide) (by decide) (by decide) hB' hdA hc'
    norm_num only [coeff_derivative] at hBAc
    have hBc := coeff_mul_two_below_bounds68 B c 6 20
      (by decide) (by decide) hB' hc'
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simp only [hdecomp0, coeff_add, coeff_smul, hBAc,
        coeff_eq_zero_of_natDegree_lt hlow0, smul_eq_mul, add_zero]
      norm_num only [D, Cc, i0]
      ring
    · simp only [hdecomp2, coeff_sub, coeff_smul, coeff_derivative, hBc,
        coeff_eq_zero_of_natDegree_lt hlow2, smul_eq_mul, sub_zero]
      norm_num only [D, Cc, i2]
      ring
  · right; right; left
    rcases h21 with ⟨hN21, hS27⟩
    subst N; subst S
    simp only [i0, i2, Nat.reduceMul, Nat.reduceSub] at hlow0 hlow2
    dsimp only [D, Cc, V, E] at hB' hc' hd' he'
    have hdA : (derivative A).natDegree ≤ 41 := by
      exact (natDegree_derivative_le A).trans (Nat.sub_le_sub_right hA 1)
    have hBAc := coeff_mul_mul_one_below_bounds68 B (derivative A) c
      9 41 30 (by decide) (by decide) (by decide) hB' hdA hc'
    norm_num only [coeff_derivative] at hBAc
    have hBc := coeff_mul_one_below_bounds68 B c 9 30
      (by decide) (by decide) hB' hc'
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simp only [hdecomp0, coeff_add, coeff_smul, hBAc,
        coeff_eq_zero_of_natDegree_lt hlow0, smul_eq_mul, add_zero]
      norm_num only [D, Cc, i0]
      ring
    · simp only [hdecomp2, coeff_sub, coeff_smul, coeff_derivative, hBc,
        coeff_eq_zero_of_natDegree_lt hlow2, smul_eq_mul, sub_zero]
      norm_num only [D, Cc, i2]
      ring
  · right; right; right; left
    rcases h28 with ⟨hN28, hS36⟩
    subst N; subst S
    simp only [i0, i2, Nat.reduceMul, Nat.reduceSub] at hlow0 hlow2
    dsimp only [D, Cc, V, E] at hB' hc' hd' he'
    have hBAc := coeff_mul_mul_derivative_at_bounds68 B c A 12 40 56
      (by decide) hB' hc' hA
    norm_num at hBAc
    have hBAc' : (B * derivative A * c).coeff 107 =
        B.coeff 12 * A.coeff 56 * c.coeff 40 * (56 : k) := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hBAc
    have hBc := coeff_mul_at_bounds68 B c 12 40 hB' hc'
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simp only [hdecomp0, coeff_add, coeff_smul, hBAc',
        coeff_eq_zero_of_natDegree_lt hlow0, smul_eq_mul, add_zero]
      norm_num only [D, Cc, i0]
      ring
    · simp only [hdecomp2, coeff_sub, coeff_smul, coeff_derivative, hBc,
        coeff_eq_zero_of_natDegree_lt hlow2, smul_eq_mul, sub_zero]
      norm_num only [D, Cc, i2]
      ring
  · right; right; right; right
    refine ⟨hlarge, ?_, ?_⟩
    · apply coeff_eq_zero_of_natDegree_lt
      change W0.natDegree < i0
      dsimp only [W0]
      rw [hdecomp0]
      apply lt_of_le_of_lt (natDegree_add_le _ _)
      apply max_lt
      · apply lt_of_le_of_lt hmain0
        dsimp only [D, Cc, i0]
        clear * - hEq hlarge
        omega
      · exact hlow0
    · apply coeff_eq_zero_of_natDegree_lt
      change W2.natDegree < i2
      dsimp only [W2]
      rw [hdecomp2]
      apply lt_of_le_of_lt (natDegree_sub_le _ _)
      apply max_lt
      · apply lt_of_le_of_lt hmain2
        dsimp only [D, Cc, i2]
        clear * - hEq hlarge
        omega
      · exact hlow2


#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_clean_fourth_split68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
