import Grok68VanishingAOrder4CompanionSplitPart12Scratch

/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 13 of 26, so that no single
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
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 8000000

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_fourth_load_source68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0) :
    let p := 2 * N
    let D := 3 * N - 2 * S
    let V := 5 * N - 3 * S
    let L0 := FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
    let L2 := FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
    (6 : k) * ((p - 4 : ℕ) : k) ^ 2 * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) *
        ((p - 1 : ℕ) : k) * A.coeff (p - 4) * B.coeff D ^ 2 * d.coeff V +
      (6 : k) * ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) *
        ((p - 1 : ℕ) : k) * L0.coeff (2 * p - 5) +
      ((p : ℕ) : k) * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) *
        ((p - 1 : ℕ) : k) * A.coeff p * L2.coeff (p - 5) +
      ((p - 4 : ℕ) : k) * ((p - 2 : ℕ) : k) * ((p - 1 : ℕ) : k) ^ 2 *
        A.coeff (p - 1) * L2.coeff (p - 4) +
      ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) * ((p - 2 : ℕ) : k) *
        ((p - 1 : ℕ) : k) * A.coeff (p - 2) * L2.coeff (p - 3) +
      ((p - 4 : ℕ) : k) * ((p - 3 : ℕ) : k) ^ 2 * ((p - 2 : ℕ) : k) *
        A.coeff (p - 3) * L2.coeff (p - 2) = 0 := by
  -- The identity is the order-four load algebra after the four disc/I4 jets
  -- and the four row-two load expansions.  The row-zero load is identified
  -- with `RowZeroLoadJetFour` by reducing the defining polynomial against
  -- the same jets; that identification is discharged by the algebra
  -- certificate after substituting the source expansions of `L2` and the
  -- cusp/I4 rows, together with the defining expansion of `L0` as
  -- `A*(B^2 d' + B B' d) - 3 B c e' + 3 c c' d`.
  let p := 2 * N
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let E := 6 * N - 3 * S
  let L0 := FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68 A B c d e
  let L2 := FiveToSixCuspZetaFirstB3EqualitySupportRowTwoLoad68 B d
  let b4 : k := if 4 ≤ D then B.coeff (D - 4) else 0
  change _ = 0
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS, hGamma, hsource⟩
  have hp0 := hsource
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp0
  rcases hp0 with ⟨hS, hSR, hd, he, hpacket, hrest⟩
  rcases hpacket with ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  rcases hcusp with ⟨hBtop, hctop, hdtop, hetop, hcuspEq⟩
  have hnxt := fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68] at hnxt
  have hEq : 9 * N = 7 * S := hnxt.1.1
  have hb0 : B.coeff D ≠ 0 := by simpa [D, hGS] using hBtop
  have hD0 : A.coeff p * B.coeff D ^ 2 + 3 * c.coeff Cc ^ 2 = 0 := by
    simpa [p, D, Cc, hGS] using hcuspEq
  have hD1 := fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hD2 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_next_two68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hD3 := fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_third68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hD4 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_discriminant_fourth68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hI40 :=
    (fiveToSix_zetaFirst_B3_equality_support_qZero_top_resultant68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq).1
  have hI41 := fiveToSix_zetaFirst_B3_equality_support_qZero_top_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hI42 := fiveToSix_zetaFirst_B3_equality_support_qZero_I4_next_two68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hI43 := fiveToSix_zetaFirst_B3_equality_support_qZero_I4_third68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hI44 := fiveToSix_zetaFirst_B3_equality_support_qZero_I4_fourth68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hD1 hD2 hD3 hD4 hI40 hI41 hI42 hI43 hI44
  have hL21 := fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hL22 := fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hL23 := fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load_third68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  have hL24 :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_rowTwo_load_fourth68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only at hL21 hL22 hL23 hL24
  have hL0 := fiveToSix_zetaFirst_B3_equality_support_qZero_rowZero_load_third68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  -- Identify `L0` at `2p-5` with the order-four jet by the same generating
  -- function as the third jet, shifted one step.  The algebra certificate
  -- only needs that identification after the `L2` expansions.
  have halg :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_fourth_load_algebra68
      ((p : ℕ) : k)
      (A.coeff p) (A.coeff (p - 1)) (A.coeff (p - 2)) (A.coeff (p - 3))
      (A.coeff (p - 4))
      (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3)) b4
      (c.coeff Cc) (c.coeff (Cc - 1)) (c.coeff (Cc - 2)) (c.coeff (Cc - 3))
      (c.coeff (Cc - 4))
      (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3))
      (d.coeff (V - 4))
      (e.coeff E) (e.coeff (E - 1)) (e.coeff (E - 2)) (e.coeff (E - 3))
      (e.coeff (E - 4))
      hb0 hD0 hD1 hD2 hD3 (by
        dsimp only [b4] at *
        simpa [p, D, Cc] using hD4) hI40 hI41 hI42 hI43 (by
        dsimp only [b4] at *
        simpa [D, Cc, V, E] using hI44)
  have hp1 : ((p - 1 : ℕ) : k) = ((p : ℕ) : k) - 1 := by
    rw [Nat.cast_sub (by dsimp only [p]; omega)]; norm_num
  have hp2 : ((p - 2 : ℕ) : k) = ((p : ℕ) : k) - 2 := by
    rw [Nat.cast_sub (by dsimp only [p]; omega)]; norm_num
  have hp3 : ((p - 3 : ℕ) : k) = ((p : ℕ) : k) - 3 := by
    rw [Nat.cast_sub (by dsimp only [p]; omega)]; norm_num
  have hp4 : ((p - 4 : ℕ) : k) = ((p : ℕ) : k) - 4 := by
    rw [Nat.cast_sub (by dsimp only [p]; omega)]; norm_num
  -- `L0.coeff (2p-5)` is the order-four row-zero load jet: this is the
  -- defining expansion of `L0` against `B^2 d`, `B c e'`, and `c c' d`.
  -- It is supplied by evaluating the same Cauchy products as
  -- `rowZero_load_third` one index lower; the algebra identity then
  -- cancels every non-`Fce` term.
  have hL0four :
      L0.coeff (2 * p - 5) =
        FiveToSixQZeroRowZeroLoadJetFour68 ((p : ℕ) : k)
          (A.coeff p) (A.coeff (p - 1)) (A.coeff (p - 2)) (A.coeff (p - 3))
          (A.coeff (p - 4))
          (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3)) b4
          (c.coeff Cc) (c.coeff (Cc - 1)) (c.coeff (Cc - 2)) (c.coeff (Cc - 3))
          (c.coeff (Cc - 4))
          (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3))
          (d.coeff (V - 4))
          (e.coeff E) (e.coeff (E - 1)) (e.coeff (E - 2)) (e.coeff (E - 3))
          (e.coeff (E - 4)) := by
    -- Arithmetic subgoals below keep only the source degree data: letting
    -- omega preprocess the accumulated coefficient identities dominates RSS.
    -- The coefficient expansion uses only the source degree bounds.
    -- Keep the independent scalar certificate out of the nested jet proofs.
    clear halg hD0 hD1 hD2 hD3 hD4 hI40 hI41 hI42 hI43 hI44
      hL21 hL22 hL23 hL24 hL0 hb0
    -- Direct expansion of `L0 = A*(B^2*d'+B*B'*d)-3*B*c*e'+3*c*c'*d`.
    -- The Cauchy products are the order-four jets by construction of those
    -- `def`s; we close by the polynomial ring.
    have hA' : A.natDegree ≤ p := by simpa [p] using hA
    have hB' : B.natDegree ≤ D := by simpa [D, hGS] using hB
    have hc' : c.natDegree ≤ Cc := by simpa [Cc, hGS] using hc
    have hd' : d.natDegree ≤ V := by dsimp only [V]; rw [hGS] at hd; clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega
    have he' : e.natDegree ≤ E := by dsimp only [E]; rw [hGS] at he; clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega
    have hpEq : p = 2 * D + V := by dsimp only [p, D, V]; clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega
    have htwopEq : 2 * p = D + Cc + E := by dsimp only [p, D, Cc, E]; clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega
    have htwopEq' : 2 * p = 2 * Cc + V := by dsimp only [p, Cc, V]; clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega
    have hVcast : ((V : ℕ) : k) = (4 / 7 : k) * ((p : ℕ) : k) := by
      have hnat : 7 * V = 4 * p := by dsimp only [p, V]; clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega
      have h := congrArg (fun n : ℕ => (n : k)) hnat
      push_cast at h; linear_combination h / 7
    have hEcast : ((E : ℕ) : k) = (15 / 14 : k) * ((p : ℕ) : k) := by
      have hnat : 14 * E = 15 * p := by dsimp only [p, E]; clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega
      have h := congrArg (fun n : ℕ => (n : k)) hnat
      push_cast at h; linear_combination h / 14
    have hCcast : ((Cc : ℕ) : k) = (5 / 7 : k) * ((p : ℕ) : k) := by
      have hnat : 7 * Cc = 5 * p := by dsimp only [p, Cc]; clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega
      have h := congrArg (fun n : ℕ => (n : k)) hnat
      push_cast at h; linear_combination h / 7
    let Q := B ^ 2 * d
    let R := B ^ 2 * derivative d
    let T := B ^ 2 * derivative d + B * derivative B * d
    -- Share primitive degree facts and compose the bounds without reflection.
    have h2D4 : 4 ≤ 2 * D := by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega
    have hV4 : 4 ≤ V := by dsimp only [V]; clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega
    have hB2deg : (B ^ 2).natDegree ≤ 2 * D :=
      natDegree_pow_le_of_le 2 hB'
    have hdder : (derivative d).natDegree ≤ V - 1 :=
      (natDegree_derivative_le d).trans (Nat.sub_le_sub_right hd' 1)
    have hBder : (derivative B).natDegree ≤ D - 1 :=
      (natDegree_derivative_le B).trans (Nat.sub_le_sub_right hB' 1)
    have hQdeg : Q.natDegree ≤ p := by
      exact (natDegree_mul_le_of_le hB2deg hd').trans (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
    have hTdeg : T.natDegree ≤ p - 1 := by
      dsimp only [T]
      apply natDegree_add_le_of_degree_le
      · exact (natDegree_mul_le_of_le hB2deg hdder).trans (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
      · exact (natDegree_mul_le_of_le
          (natDegree_mul_le_of_le hB' hBder) hd').trans (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
    have hV1 : 4 ≤ V - 1 := by dsimp only [V]; clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega
    -- Reuse all five B-squared coefficient identities for Q and R.
    have hB20 : (B ^ 2).coeff (2 * D) = B.coeff D ^ 2 := by
      have h' := coeff_mul_at_bounds68 B B D D hB' hB'
      rw [← two_mul] at h'
      simpa [pow_two] using h'
    have hB21 : (B ^ 2).coeff (2 * D - 1) =
        (2 : k) * B.coeff D * B.coeff (D - 1) := by
      have h' := coeff_mul_one_below_bounds68 B B D D
        (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) hB' hB'
      rw [← two_mul] at h'
      simp only [pow_two] at h' ⊢; rw [h'] <;> ring
    have hB22 : (B ^ 2).coeff (2 * D - 2) =
        (2 : k) * B.coeff D * B.coeff (D - 2) + B.coeff (D - 1) ^ 2 := by
      have h' := coeff_mul_two_below_bounds68 B B D D
        (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) hB' hB'
      rw [← two_mul] at h'
      simp only [pow_two] at h' ⊢; rw [h'] <;> ring
    have hB23 : (B ^ 2).coeff (2 * D - 3) =
        (2 : k) * B.coeff D * B.coeff (D - 3) +
          (2 : k) * B.coeff (D - 1) * B.coeff (D - 2) := by
      have h' := coeff_mul_three_below_bounds68 B B D D
        (by dsimp only [D]; clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) (by dsimp only [D]; clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) hB' hB'
      rw [← two_mul] at h'
      simp only [pow_two] at h' ⊢; rw [h'] <;> ring
    have hB24 := coeff_sq_sub_four68 B D (by dsimp only [D]; clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) hB'
    have hQ4 : Q.coeff (p - 4) =
        FiveToSixQZeroBBDJetFour68
          (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3)) b4
          (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3))
          (d.coeff (V - 4)) := by
      have h := coeff_mul_four_below_bounds68 (B ^ 2) d (2 * D) V
        h2D4 hV4 hB2deg hd'
      have hpQ : p - 4 = 2 * D + V - 4 := by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega
      dsimp only [Q, FiveToSixQZeroBBDJetFour68, b4]
      rw [hpQ, h, hB20, hB21, hB22, hB23, hB24]
      ring
    have hdt := coeff_derivative_at_bound68 d V (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
    have hd1 := coeff_derivative_at_bound68 d (V - 1) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
    have hd2 := coeff_derivative_at_bound68 d (V - 2) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
    have hd3 := coeff_derivative_at_bound68 d (V - 3) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
    have hd4 := coeff_derivative_at_bound68 d (V - 4) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
    have hcastV1 : (((V - 1 : ℕ) : k)) = ((V : ℕ) : k) - 1 := by
      rw [Nat.cast_sub (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega), Nat.cast_one]
    have hcastV2 : (((V - 2 : ℕ) : k)) = ((V : ℕ) : k) - 2 := by
      rw [Nat.cast_sub (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)]; norm_num
    have hcastV3 : (((V - 3 : ℕ) : k)) = ((V : ℕ) : k) - 3 := by
      rw [Nat.cast_sub (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)]; norm_num
    have hcastV4 : (((V - 4 : ℕ) : k)) = ((V : ℕ) : k) - 4 := by
      rw [Nat.cast_sub (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)]; norm_num
    have hR4 : R.coeff (p - 5) =
        FiveToSixQZeroBBDerivativeJetFour68 ((p : ℕ) : k)
          (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3)) b4
          (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3))
          (d.coeff (V - 4)) := by
      have h := coeff_mul_four_below_bounds68 (B ^ 2) (derivative d)
        (2 * D) (V - 1) h2D4 hV1 hB2deg hdder
      have hpR : 2 * D + (V - 1) - 4 = p - 5 := by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega
      rw [hpR, hB20, hB21, hB22, hB23, hB24] at h
      rw [show V - 1 - 2 = V - 2 - 1 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega,
        show V - 1 - 3 = V - 3 - 1 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega,
        show V - 1 - 4 = V - 4 - 1 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega] at h
      rw [hdt, hd1, hd2, hd3, hd4, hcastV1, hcastV2, hcastV3, hcastV4] at h
      dsimp only [R, FiveToSixQZeroBBDerivativeJetFour68, b4]
      rw [hVcast] at h
      simp only [pow_two] at h ⊢
      rw [h] <;> ring
    have hTpoly : T = (1 / 2 : k) • (derivative Q + R) := by
      dsimp only [T, Q, R]
      have hder : derivative (B ^ 2 * d) =
          derivative (B ^ 2) * d + B ^ 2 * derivative d := by
        rw [derivative_mul]
      have hsq : derivative (B ^ 2) = (2 : k) • (B * derivative B) := by
        rw [show B ^ 2 = B * B by ring, derivative_mul]
        simp only [two_smul]; ring
      rw [hder, hsq, smul_mul_assoc, add_assoc]
      have htwice : B ^ 2 * derivative d + B ^ 2 * derivative d =
          (2 : k) • (B ^ 2 * derivative d) := by simp only [two_smul]
      rw [htwice, ← smul_add, smul_smul]
      norm_num
      ring
    -- Remaining `T` jets `k=0,1,2,3` are the third-file identities shifted
    -- by the same `Q,R` expansion; they are recovered from
    -- `rowZero_load_third` after subtracting the new `A_(p-4)` slot.
    have hT4 : T.coeff (p - 5) = (1 / 2 : k) * (((p : ℕ) : k) - 4) *
        FiveToSixQZeroBBDJetFour68
          (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3)) b4
          (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3))
          (d.coeff (V - 4)) +
        (1 / 2 : k) * FiveToSixQZeroBBDerivativeJetFour68 ((p : ℕ) : k)
          (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3)) b4
          (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3))
          (d.coeff (V - 4)) := by
      rw [hTpoly, coeff_smul, coeff_add, coeff_derivative,
        show p - 5 + 1 = p - 4 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega, hQ4, hR4]
      have hcast : (((p - 5 : ℕ) : k) + 1) = ((p : ℕ) : k) - 4 := by
        calc
          ((p - 5 : ℕ) : k) + 1 = ((p - 4 : ℕ) : k) := by
            exact_mod_cast (show p - 5 + 1 = p - 4 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
          _ = ((p : ℕ) : k) - 4 := by
            rw [Nat.cast_sub (by dsimp only [p]; clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)]; norm_num
      rw [hcast]
      simp only [smul_eq_mul]
      ring
    have hQ0 : Q.coeff p = FiveToSixQZeroBBDJetZero68 (B.coeff D) (d.coeff V) := by
      have h := coeff_mul_mul_at_bounds68 B B d D D V hB' hB' hd'
      rw [show D + D + V = p by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega] at h
      dsimp only [Q, FiveToSixQZeroBBDJetZero68]
      simpa only [pow_two] using h
    have hQ1 : Q.coeff (p - 1) = FiveToSixQZeroBBDJetOne68
        (B.coeff D) (B.coeff (D - 1)) (d.coeff V) (d.coeff (V - 1)) := by
      have h := coeff_mul_mul_one_below_bounds68 B B d D D V
        (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) hB' hB' hd'
      rw [show D + D + V - 1 = p - 1 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega] at h
      dsimp only [Q, FiveToSixQZeroBBDJetOne68]
      simp only [pow_two, mul_assoc, mul_comm, mul_left_comm] at h ⊢
      rw [h] <;> ring
    have hQ2 : Q.coeff (p - 2) = FiveToSixQZeroBBDJetTwo68
        (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2))
        (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) := by
      have h := coeff_mul_mul_two_below_bounds68 B B d D D V
        (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) hB' hB' hd'
      rw [show D + D + V - 2 = p - 2 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega] at h
      dsimp only [Q, FiveToSixQZeroBBDJetTwo68]
      simp only [pow_two, mul_assoc, mul_comm, mul_left_comm] at h ⊢
      rw [h] <;> ring
    have hQ3 : Q.coeff (p - 3) = FiveToSixQZeroBBDJetThree68
        (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3))
        (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3)) := by
      have h := coeff_mul_mul_three_below_bounds68 B B d D D V
        (by dsimp only [D]; clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) (by dsimp only [D]; clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
        hB' hB' hd'
      rw [show D + D + V - 3 = p - 3 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega] at h
      dsimp only [Q, FiveToSixQZeroBBDJetThree68]
      simp only [pow_two, mul_assoc, mul_comm, mul_left_comm] at h ⊢
      rw [h] <;> ring
    have hR0 : R.coeff (p - 1) = FiveToSixQZeroBBDerivativeJetZero68
        ((p : ℕ) : k) (B.coeff D) (d.coeff V) := by
      have h := coeff_mul_mul_at_bounds68 B B (derivative d)
        D D (V - 1) hB' hB' hdder
      rw [show D + D + (V - 1) = p - 1 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega, hdt] at h
      dsimp only [R, FiveToSixQZeroBBDerivativeJetZero68]
      rw [← hVcast]
      simp only [pow_two, mul_assoc, mul_comm, mul_left_comm] at h ⊢
      rw [h] <;> ring
    have hR1 : R.coeff (p - 2) = FiveToSixQZeroBBDerivativeJetOne68
        ((p : ℕ) : k) (B.coeff D) (B.coeff (D - 1))
        (d.coeff V) (d.coeff (V - 1)) := by
      have h := coeff_mul_mul_one_below_bounds68 B B (derivative d)
        D D (V - 1) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) hB' hB' hdder
      rw [show D + D + (V - 1) - 1 = p - 2 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega, hdt, hd1, hcastV1] at h
      dsimp only [R, FiveToSixQZeroBBDerivativeJetOne68]
      rw [← hVcast]
      simp only [pow_two, mul_assoc, mul_comm, mul_left_comm] at h ⊢
      rw [h] <;> ring
    have hR2 : R.coeff (p - 3) = FiveToSixQZeroBBDerivativeJetTwo68
        ((p : ℕ) : k) (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2))
        (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) := by
      have h := coeff_mul_mul_two_below_bounds68 B B (derivative d)
        D D (V - 1) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) hB' hB' hdder
      rw [show D + D + (V - 1) - 2 = p - 3 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega,
        show V - 1 - 2 = V - 2 - 1 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega, hdt, hd1, hd2, hcastV1, hcastV2] at h
      dsimp only [R, FiveToSixQZeroBBDerivativeJetTwo68]
      rw [← hVcast]
      simp only [pow_two, mul_assoc, mul_comm, mul_left_comm] at h ⊢
      rw [h] <;> ring
    have hR3 : R.coeff (p - 4) = FiveToSixQZeroBBDerivativeJetThree68
        ((p : ℕ) : k) (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2))
        (B.coeff (D - 3)) (d.coeff V) (d.coeff (V - 1))
        (d.coeff (V - 2)) (d.coeff (V - 3)) := by
      have h := coeff_mul_mul_three_below_bounds68 B B (derivative d)
        D D (V - 1) (by dsimp only [D]; clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) (by dsimp only [D]; clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
        (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) hB' hB' hdder
      rw [show D + D + (V - 1) - 3 = p - 4 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega,
        show V - 1 - 2 = V - 2 - 1 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega, show V - 1 - 3 = V - 3 - 1 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega,
        hdt, hd1, hd2, hd3, hcastV1, hcastV2, hcastV3] at h
      dsimp only [R, FiveToSixQZeroBBDerivativeJetThree68]
      rw [← hVcast]
      simp only [pow_two, mul_assoc, mul_comm, mul_left_comm] at h ⊢
      rw [h] <;> ring
    have hT0 : T.coeff (p - 1) = (1 / 2 : k) * (p *
        FiveToSixQZeroBBDJetZero68 (B.coeff D) (d.coeff V) +
        FiveToSixQZeroBBDerivativeJetZero68 ((p : ℕ) : k)
          (B.coeff D) (d.coeff V)) := by
      rw [hTpoly, coeff_smul, coeff_add, coeff_derivative,
        show p - 1 + 1 = p by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega, hQ0, hR0]
      have hcast : (((p - 1 : ℕ) : k) + 1) = ((p : ℕ) : k) := by
        exact_mod_cast (show p - 1 + 1 = p by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
      rw [hcast]; simp only [smul_eq_mul]; ring
    have hT1 : T.coeff (p - 2) = (1 / 2 : k) * (((p : ℕ) : k) - 1) *
        FiveToSixQZeroBBDJetOne68 (B.coeff D) (B.coeff (D - 1))
          (d.coeff V) (d.coeff (V - 1)) +
        (1 / 2 : k) * FiveToSixQZeroBBDerivativeJetOne68 ((p : ℕ) : k)
          (B.coeff D) (B.coeff (D - 1)) (d.coeff V) (d.coeff (V - 1)) := by
      rw [hTpoly, coeff_smul, coeff_add, coeff_derivative,
        show p - 2 + 1 = p - 1 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega, hQ1, hR1]
      have hcast : (((p - 2 : ℕ) : k) + 1) = ((p : ℕ) : k) - 1 := by
        calc
          ((p - 2 : ℕ) : k) + 1 = ((p - 1 : ℕ) : k) := by
            exact_mod_cast (show p - 2 + 1 = p - 1 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
          _ = ((p : ℕ) : k) - 1 := by rw [Nat.cast_sub (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)]; norm_num
      rw [hcast]; ring
    have hT2 : T.coeff (p - 3) = (1 / 2 : k) * (((p : ℕ) : k) - 2) *
        FiveToSixQZeroBBDJetTwo68 (B.coeff D) (B.coeff (D - 1))
          (B.coeff (D - 2)) (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) +
        (1 / 2 : k) * FiveToSixQZeroBBDerivativeJetTwo68 ((p : ℕ) : k)
          (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2))
          (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) := by
      rw [hTpoly, coeff_smul, coeff_add, coeff_derivative,
        show p - 3 + 1 = p - 2 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega, hQ2, hR2]
      have hcast : (((p - 3 : ℕ) : k) + 1) = ((p : ℕ) : k) - 2 := by
        calc
          ((p - 3 : ℕ) : k) + 1 = ((p - 2 : ℕ) : k) := by
            exact_mod_cast (show p - 3 + 1 = p - 2 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
          _ = ((p : ℕ) : k) - 2 := by rw [Nat.cast_sub (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)]; norm_num
      rw [hcast]; ring
    have hT3 : T.coeff (p - 4) = (1 / 2 : k) * (((p : ℕ) : k) - 3) *
        FiveToSixQZeroBBDJetThree68
          (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3))
          (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3)) +
        (1 / 2 : k) * FiveToSixQZeroBBDerivativeJetThree68 ((p : ℕ) : k)
          (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3))
          (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3)) := by
      rw [hTpoly, coeff_smul, coeff_add, coeff_derivative,
        show p - 4 + 1 = p - 3 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega, hQ3, hR3]
      have hcast : (((p - 4 : ℕ) : k) + 1) = ((p : ℕ) : k) - 3 := by
        calc
          ((p - 4 : ℕ) : k) + 1 = ((p - 3 : ℕ) : k) := by
            exact_mod_cast (show p - 4 + 1 = p - 3 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
          _ = ((p : ℕ) : k) - 3 := by rw [Nat.cast_sub (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)]; norm_num
      rw [hcast]; ring
    have hATraw := coeff_mul_four_below_bounds68 A T p (p - 1)
      (by dsimp only [p]; clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) (by dsimp only [p]; clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) hA' hTdeg
    rw [show p + (p - 1) - 4 = 2 * p - 5 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega,
      show p - 1 - 1 = p - 2 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega, show p - 1 - 2 = p - 3 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega,
      show p - 1 - 3 = p - 4 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega, show p - 1 - 4 = p - 5 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega,
      hT0, hT1, hT2, hT3, hT4] at hATraw
    have hAT : (A * T).coeff (2 * p - 5) =
        (1 / 2 : k) * A.coeff p * (((p : ℕ) : k) - 4) *
            FiveToSixQZeroBBDJetFour68
              (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3))
              b4 (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2))
              (d.coeff (V - 3)) (d.coeff (V - 4)) +
          (1 / 2 : k) * A.coeff p * FiveToSixQZeroBBDerivativeJetFour68
            ((p : ℕ) : k) (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2))
            (B.coeff (D - 3)) b4 (d.coeff V) (d.coeff (V - 1))
            (d.coeff (V - 2)) (d.coeff (V - 3)) (d.coeff (V - 4)) +
          (1 / 2 : k) * A.coeff (p - 1) * (((p : ℕ) : k) - 3) *
            FiveToSixQZeroBBDJetThree68
              (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3))
              (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3)) +
          (1 / 2 : k) * A.coeff (p - 1) * FiveToSixQZeroBBDerivativeJetThree68
            ((p : ℕ) : k) (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2))
            (B.coeff (D - 3)) (d.coeff V) (d.coeff (V - 1))
            (d.coeff (V - 2)) (d.coeff (V - 3)) +
          (1 / 2 : k) * A.coeff (p - 2) * (((p : ℕ) : k) - 2) *
            FiveToSixQZeroBBDJetTwo68
              (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2))
              (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) +
          (1 / 2 : k) * A.coeff (p - 2) * FiveToSixQZeroBBDerivativeJetTwo68
            ((p : ℕ) : k) (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2))
            (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) +
          (1 / 2 : k) * A.coeff (p - 3) * (((p : ℕ) : k) - 1) *
            FiveToSixQZeroBBDJetOne68
              (B.coeff D) (B.coeff (D - 1)) (d.coeff V) (d.coeff (V - 1)) +
          (1 / 2 : k) * A.coeff (p - 3) * FiveToSixQZeroBBDerivativeJetOne68
            ((p : ℕ) : k) (B.coeff D) (B.coeff (D - 1))
            (d.coeff V) (d.coeff (V - 1)) +
          (1 / 2 : k) * A.coeff (p - 4) * ((p : ℕ) : k) *
            FiveToSixQZeroBBDJetZero68 (B.coeff D) (d.coeff V) +
          (1 / 2 : k) * A.coeff (p - 4) * FiveToSixQZeroBBDerivativeJetZero68
            ((p : ℕ) : k) (B.coeff D) (d.coeff V) := by
      rw [hATraw] <;> ring
    have hde' : (derivative e).natDegree ≤ E - 1 :=
      (natDegree_derivative_le e).trans (Nat.sub_le_sub_right he' 1)
    have het := coeff_derivative_at_bound68 e E (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
    have he1 := coeff_derivative_at_bound68 e (E - 1) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
    have he2 := coeff_derivative_at_bound68 e (E - 2) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
    have he3 := coeff_derivative_at_bound68 e (E - 3) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
    have he4 := coeff_derivative_at_bound68 e (E - 4) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
    have hcastE1 : (((E - 1 : ℕ) : k)) = ((E : ℕ) : k) - 1 := by
      rw [Nat.cast_sub (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega), Nat.cast_one]
    have hcastE2 : (((E - 2 : ℕ) : k)) = ((E : ℕ) : k) - 2 := by
      rw [Nat.cast_sub (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)]; norm_num
    have hcastE3 : (((E - 3 : ℕ) : k)) = ((E : ℕ) : k) - 3 := by
      rw [Nat.cast_sub (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)]; norm_num
    have hcastE4 : (((E - 4 : ℕ) : k)) = ((E : ℕ) : k) - 4 := by
      rw [Nat.cast_sub (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)]; norm_num
    have hBcdeg : (B * c).natDegree ≤ D + Cc :=
      natDegree_mul_le_of_le hB' hc'
    have h3raw := coeff_mul_four_below_bounds68 (B * c) (derivative e)
      (D + Cc) (E - 1) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) hBcdeg hde'
    have hBc0 := coeff_mul_at_bounds68 B c D Cc hB' hc'
    have hBc1 := coeff_mul_one_below_bounds68 B c D Cc
      (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) hB' hc'
    have hBc2 := coeff_mul_two_below_bounds68 B c D Cc
      (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) hB' hc'
    have hBc3 := coeff_mul_three_below_bounds68 B c D Cc
      (by dsimp only [D]; clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) hB' hc'
    have hBc4 := coeff_mul_sub_four_left_ge_three68 B c D Cc
      (by dsimp only [D]; clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) hB' hc'
    have hpBCE : D + Cc + (E - 1) - 4 = 2 * p - 5 := by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega
    rw [hpBCE, hBc0, hBc1, hBc2, hBc3, hBc4] at h3raw
    rw [show E - 1 - 2 = E - 2 - 1 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega,
      show E - 1 - 3 = E - 3 - 1 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega,
      show E - 1 - 4 = E - 4 - 1 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega] at h3raw
    rw [het, he1, he2, he3, he4, hcastE1, hcastE2, hcastE3, hcastE4] at h3raw
    have h3 : (B * c * derivative e).coeff (2 * p - 5) =
        FiveToSixQZeroBCEDerivativeJetFour68 ((p : ℕ) : k)
          (B.coeff D) (B.coeff (D - 1)) (B.coeff (D - 2)) (B.coeff (D - 3)) b4
          (c.coeff Cc) (c.coeff (Cc - 1)) (c.coeff (Cc - 2)) (c.coeff (Cc - 3))
          (c.coeff (Cc - 4))
          (e.coeff E) (e.coeff (E - 1)) (e.coeff (E - 2)) (e.coeff (E - 3))
          (e.coeff (E - 4)) := by
      dsimp only [FiveToSixQZeroBCEDerivativeJetFour68, b4]
      rw [hEcast] at h3raw
      split_ifs at h3raw ⊢ <;> rw [h3raw] <;> ring
    have hdc' : (derivative c).natDegree ≤ Cc - 1 :=
      (natDegree_derivative_le c).trans (Nat.sub_le_sub_right hc' 1)
    have hct := coeff_derivative_at_bound68 c Cc (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
    have hc1 := coeff_derivative_at_bound68 c (Cc - 1) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
    have hc2 := coeff_derivative_at_bound68 c (Cc - 2) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
    have hc3 := coeff_derivative_at_bound68 c (Cc - 3) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
    have hc4 := coeff_derivative_at_bound68 c (Cc - 4) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)
    have hcastC1 : (((Cc - 1 : ℕ) : k)) = ((Cc : ℕ) : k) - 1 := by
      rw [Nat.cast_sub (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega), Nat.cast_one]
    have hcastC2 : (((Cc - 2 : ℕ) : k)) = ((Cc : ℕ) : k) - 2 := by
      rw [Nat.cast_sub (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)]; norm_num
    have hcastC3 : (((Cc - 3 : ℕ) : k)) = ((Cc : ℕ) : k) - 3 := by
      rw [Nat.cast_sub (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)]; norm_num
    have hcastC4 : (((Cc - 4 : ℕ) : k)) = ((Cc : ℕ) : k) - 4 := by
      rw [Nat.cast_sub (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega)]; norm_num
    have h4raw := coeff_mul_mul_four_below_bounds68 c (derivative c) d
      Cc (Cc - 1) V (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) (by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega) hc' hdc' hd'
    rw [show Cc + (Cc - 1) + V - 4 = 2 * p - 5 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega] at h4raw
    rw [show Cc - 1 - 2 = Cc - 2 - 1 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega,
      show Cc - 1 - 3 = Cc - 3 - 1 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega,
      show Cc - 1 - 4 = Cc - 4 - 1 by clear * - N G S p D Cc V E hN hEq hGS hA hB hc hd he; omega] at h4raw
    rw [hct, hc1, hc2, hc3, hc4, hcastC1, hcastC2, hcastC3, hcastC4] at h4raw
    have h4 : (c * derivative c * d).coeff (2 * p - 5) =
        FiveToSixQZeroCCDerivativeDJetFour68 ((p : ℕ) : k)
          (c.coeff Cc) (c.coeff (Cc - 1)) (c.coeff (Cc - 2)) (c.coeff (Cc - 3))
          (c.coeff (Cc - 4))
          (d.coeff V) (d.coeff (V - 1)) (d.coeff (V - 2)) (d.coeff (V - 3))
          (d.coeff (V - 4)) := by
      dsimp only [FiveToSixQZeroCCDerivativeDJetFour68]
      rw [hCcast] at h4raw
      rw [h4raw] <;> ring
    have hloadpoly : L0 = A * T - (3 : k) • (B * c * derivative e) +
        (3 : k) • (c * derivative c * d) := by
      dsimp only [L0, T, FiveToSixCuspZetaFirstB3EqualitySupportRowZeroLoad68]
      ring
    rw [hloadpoly]
    simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, hAT, h3, h4]
    dsimp only [FiveToSixQZeroRowZeroLoadJetFour68]
    ring
  rw [hL0four, hL21, hL22, hL23, hL24, hp1, hp2, hp3, hp4]
  -- Keep the load and higher jets as atoms.  Only the second row-two jet
  -- uses a distributed sum, so the imported certificate applies directly.
  simpa only [FiveToSixQZeroBBDJetOne68, FiveToSixQZeroBBDJetTwo68, add_mul, add_assoc] using halg

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_fourth_load_source68


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
