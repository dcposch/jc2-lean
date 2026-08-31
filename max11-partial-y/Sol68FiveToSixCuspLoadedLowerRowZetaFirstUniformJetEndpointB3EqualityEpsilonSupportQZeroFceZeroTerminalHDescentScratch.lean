import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalQuotientScratch

/-! # A second divisor after the nonzero-terminal quotient normal form -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalHDescent68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- After `2c+3γ=Bv`, the compensated `I3` identity has a factor `B`
on its nonconstant side. -/
theorem fiveToSix_qZero_Fce_zero_terminal_H_descent_algebra68
    (gamma epsilon i3 : k) (A B c d e v : k[X])
    (hv : (2 : k) • c + C (3 * gamma) = B * v)
    (he : e = (1 / 9 : k) • B ^ 2 - (1 / 2 : k) • (v * d) -
      C (3 / 4 * epsilon))
    (hRce : (-(A * B * d) + (3 : k) • (c * e)) - B ^ 2 * c +
      (3 / 2 : k) • d ^ 2 + (9 / 2 * gamma : k) • e +
      (9 / 4 * epsilon : k) • c =
      (3 / 4 * gamma : k) • B ^ 2 + (9 / 8 : k) • C i3) :
    let H := FiveToSixQZeroFceZeroH68 B c d
    let W := (4 : k) • A + (3 : k) • v ^ 2
    (2 : k) • (B * ((3 : k) • (W * d) +
        (8 : k) • (B ^ 2 * v) - (21 * gamma : k) • B)) =
      (4 : k) • H - C (81 * epsilon * gamma + 27 * i3) := by
  let H := FiveToSixQZeroFceZeroH68 B c d
  let W := (4 : k) • A + (3 : k) • v ^ 2
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  have hv' := congrArg (algebraMap k[X] (RatFunc k)) hv
  have he' := congrArg (algebraMap k[X] (RatFunc k)) he
  have hR' := congrArg (algebraMap k[X] (RatFunc k)) hRce
  dsimp only [H, W, FiveToSixQZeroFceZeroH68] at hv' he' hR' ⊢
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
    map_neg, RatFunc.algebraMap_C] at hv' he' hR' ⊢
  simp only [map_div₀, map_ofNat, map_one] at hv' he' hR' ⊢
  ring_nf at hv' he' hR' ⊢
  linear_combination (-24 : RatFunc k) * hR' +
    (36 : RatFunc k) *
      (2 * algebraMap k[X] (RatFunc k) c + 3 * RatFunc.C gamma) * he' +
    (-2 : RatFunc k) *
      (8 * (algebraMap k[X] (RatFunc k) B) ^ 2 +
        9 * algebraMap k[X] (RatFunc k) d *
          algebraMap k[X] (RatFunc k) v) * hv'

/-- The reduced `I3` identity therefore makes `B` divide `4H` minus a
constant. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_H_divisor68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hf : (((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B).coeff 0 = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let Cg := (2 : k) • c + C (3 * gamma)
    let H := FiveToSixQZeroFceZeroH68 B c d
    ∃ i3 : k, ∃ v : k[X],
      Cg = B * v ∧ v.natDegree = Cc - D ∧
      B ∣ ((4 : k) • H - C (81 * epsilon * gamma + 27 * i3)) := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let Cg := (2 : k) • c + C (3 * gamma)
  let H := FiveToSixQZeroFceZeroH68 B c d
  change ∃ i3 : k, ∃ v : k[X], Cg = B * v ∧
    v.natDegree = Cc - D ∧
    B ∣ ((4 : k) • H - C (81 * epsilon * gamma + 27 * i3))
  obtain ⟨v, hv, hvdeg, he, hH, hDelta⟩ :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_quotient68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq hf
  have hglobal :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_global68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq hf
  rcases hglobal with ⟨i3, hFzero, hRce, hK⟩
  have halg := fiveToSix_qZero_Fce_zero_terminal_H_descent_algebra68
    gamma epsilon i3 A B c d e v hv he hRce
  let W := (4 : k) • A + (3 : k) • v ^ 2
  change (2 : k) • (B * ((3 : k) • (W * d) +
      (8 : k) • (B ^ 2 * v) - (21 * gamma : k) • B)) =
    (4 : k) • H - C (81 * epsilon * gamma + 27 * i3) at halg
  refine ⟨i3, v, hv, hvdeg, ?_⟩
  refine ⟨(2 : k) • ((3 : k) • (W * d) +
    (8 : k) • (B ^ 2 * v) - (21 * gamma : k) • B), ?_⟩
  rw [← halg]
  simp only [Polynomial.smul_eq_C_mul]
  ring

/-- The divisor has an explicit quotient of exact degree `N-D` (equivalently
`4N/7` on the `9N=7S` wall). -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_H_quotient68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hf : (((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B).coeff 0 = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let Cg := (2 : k) • c + C (3 * gamma)
    let H := FiveToSixQZeroFceZeroH68 B c d
    ∃ i3 : k, ∃ v T : k[X],
      Cg = B * v ∧ v.natDegree = Cc - D ∧
      T = (2 : k) • ((3 : k) • (((4 : k) • A +
          (3 : k) • v ^ 2) * d) +
        (8 : k) • (B ^ 2 * v) - (21 * gamma : k) • B) ∧
      (4 : k) • H - C (81 * epsilon * gamma + 27 * i3) = B * T ∧
      T.natDegree = N - D := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let Cg := (2 : k) • c + C (3 * gamma)
  let H := FiveToSixQZeroFceZeroH68 B c d
  change ∃ i3 : k, ∃ v T : k[X], Cg = B * v ∧
    v.natDegree = Cc - D ∧
    T = (2 : k) • ((3 : k) • (((4 : k) • A +
        (3 : k) • v ^ 2) * d) +
      (8 : k) • (B ^ 2 * v) - (21 * gamma : k) • B) ∧
    (4 : k) • H - C (81 * epsilon * gamma + 27 * i3) = B * T ∧
    T.natDegree = N - D
  obtain ⟨v, hv, hvdeg, he, hHnorm, hDnorm⟩ :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_quotient68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq hf
  have hglobal :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_global68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq hf
  rcases hglobal with ⟨i3, hFzero, hRce, hK⟩
  have halg := fiveToSix_qZero_Fce_zero_terminal_H_descent_algebra68
    gamma epsilon i3 A B c d e v hv he hRce
  let W := (4 : k) • A + (3 : k) • v ^ 2
  let T := (2 : k) • ((3 : k) • (W * d) +
    (8 : k) • (B ^ 2 * v) - (21 * gamma : k) • B)
  change (2 : k) • (B * ((3 : k) • (W * d) +
      (8 : k) • (B ^ 2 * v) - (21 * gamma : k) • B)) =
    (4 : k) • H - C (81 * epsilon * gamma + 27 * i3) at halg
  have hBT : (4 : k) • H - C (81 * epsilon * gamma + 27 * i3) =
      B * T := by
    dsimp only [T]
    rw [← halg]
    simp only [Polynomial.smul_eq_C_mul]
    ring
  have hloaded := hs.1
  rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
    ⟨hGS, hGamma, hsource⟩
  have hp := hsource
  change 0 < S ∧ S < 7 * N - 2 * G ∧ d.natDegree ≤ 5 * N - G - S ∧
      e.natDegree ≤ 6 * N - G - S ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S ∧ _ at hp
  rcases hp with ⟨hS, hSR, hd, hedeg, hpacket, hrest⟩
  rcases hpacket with
    ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
  rcases hcusp with ⟨hBtop, hctop, hdtop, hetop, hcuspEq⟩
  have hnxt := fiveToSix_zetaFirst_B3_equality_support_qZero_next68
    alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
  dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
    at hnxt
  have hEq : 9 * N = 7 * S := hnxt.1.1
  have hB' : B.natDegree ≤ D := by dsimp only [D]; omega
  have hbidx : D = 3 * N - G := by dsimp only [D]; omega
  have hbcoeff : B.coeff D ≠ 0 := by rw [hbidx]; exact hBtop
  have hBdeg : B.natDegree = D :=
    natDegree_eq_of_le_of_coeff_ne_zero hB' hbcoeff
  have hBne : B ≠ 0 := by
    intro hz
    apply hbcoeff
    rw [hz, coeff_zero]
  have hHtop :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_H_top68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq hf
  change _ ∧ H.natDegree = D + 2 * N - Cc at hHtop
  have hQeq : D + 2 * N - Cc = N := by dsimp only [D, Cc]; omega
  have hHdeg : H.natDegree = N := by rw [hHtop.2, hQeq]
  let P := (4 : k) • H - C (81 * epsilon * gamma + 27 * i3)
  have h4Hdeg : ((4 : k) • H).natDegree = N := by
    rw [natDegree_smul H (by norm_num : (4 : k) ≠ 0), hHdeg]
  have hconstlt : (C (81 * epsilon * gamma + 27 * i3) : k[X]).natDegree <
      ((4 : k) • H).natDegree := by
    rw [h4Hdeg]
    compute_degree
    omega
  have hPdeg : P.natDegree = N := by
    dsimp only [P]
    rw [natDegree_sub_eq_left_of_natDegree_lt hconstlt, h4Hdeg]
  have hPne : P ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hPdeg
    omega
  have hTne : T ≠ 0 := by
    intro hz
    apply hPne
    change P = 0
    rw [show P = B * T by exact hBT, hz, mul_zero]
  have hmuldeg := natDegree_mul hBne hTne
  have hTdeg : T.natDegree = N - D := by
    rw [← hBT, hPdeg, hBdeg] at hmuldeg
    omega
  refine ⟨i3, v, T, hv, hvdeg, ?_, hBT, hTdeg⟩
  rfl

#print axioms fiveToSix_qZero_Fce_zero_terminal_H_descent_algebra68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_H_divisor68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_H_quotient68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalHDescent68

end Max11DegreeRoutes
