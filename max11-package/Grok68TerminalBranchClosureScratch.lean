import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalUProfileScratch

/-! # Terminal-branch closure by an exact polynomial identity

On the wall `9N = 7S`, the H-quotient and U-profile assemble the identity
`3 d (B W - 12 d) + B U - 18 γ B² + C(C0) = 0`.  Both the vanishing and
nonvanishing cases of `Z := B W - 12 d` contradict the exact degrees
`deg B = D`, `deg U = N-D`, `deg d = V`.  The comparison is a coefficient
at a single degree, not an evaluation at roots of `B`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalBranchClosure68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Ring identities -/

/-- `BU - 4(9d² + 2 B³ v) = 3 d (B W - 12 d)` is an identity of
polynomials, given the definitions of `U` and `W`. -/
theorem fiveToSix_qZero_terminal_BU_minus_four_F_algebra68
    (B d v W U : k[X])
    (hU : U = (3 : k) • (W * d) + (8 : k) • (B ^ 2 * v)) :
    B * U - (4 : k) • ((9 : k) • d ^ 2 + (2 : k) • (B ^ 3 * v)) =
      (3 : k) • (d * (B * W - (12 : k) • d)) := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  have hU' := congrArg (algebraMap k[X] (RatFunc k)) hU
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
    map_neg, RatFunc.algebraMap_C] at hU' ⊢
  simp only [map_div₀, map_ofNat, map_one] at hU' ⊢
  ring_nf at hU' ⊢
  linear_combination algebraMap k[X] (RatFunc k) B * hU'

/-- After `2c + C(3γ) = B v`, the Jacobian fibre rewrites as
`H = 2 B³ v - 6 γ B² + 9 d²`. -/
theorem fiveToSix_qZero_terminal_H_from_Cg_algebra68
    (gamma : k) (B c d v : k[X])
    (hv : (2 : k) • c + C (3 * gamma) = B * v) :
    FiveToSixQZeroFceZeroH68 B c d =
      (2 : k) • (B ^ 3 * v) - (6 * gamma : k) • B ^ 2 +
        (9 : k) • d ^ 2 := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  have hv' := congrArg (algebraMap k[X] (RatFunc k)) hv
  dsimp only [FiveToSixQZeroFceZeroH68] at hv' ⊢
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
    map_neg, RatFunc.algebraMap_C] at hv' ⊢
  simp only [map_div₀, map_ofNat, map_one] at hv' ⊢
  ring_nf at hv' ⊢
  linear_combination (2 : RatFunc k) *
    (algebraMap k[X] (RatFunc k) B) ^ 2 * hv'

/-- The H-quotient formula for `T` is `2(U - 21 γ B)` after inserting
`U` and `W = 4A + 3v²`. -/
theorem fiveToSix_qZero_terminal_T_from_U_algebra68
    (gamma : k) (A B d v W U T : k[X])
    (hW : W = (4 : k) • A + (3 : k) • v ^ 2)
    (hU : U = (3 : k) • (W * d) + (8 : k) • (B ^ 2 * v))
    (hT : T = (2 : k) • ((3 : k) • (((4 : k) • A +
        (3 : k) • v ^ 2) * d) +
      (8 : k) • (B ^ 2 * v) - (21 * gamma : k) • B)) :
    T = (2 : k) • (U - (21 * gamma : k) • B) := by
  rw [hT, hU, hW]

/-- Combining `4H - C(C0) = B T`, `T = 2(U - 21 γ B)`, and
`H = 2 B³ v - 6 γ B² + 9 d²` with the ring identity for `BU - 4F`
yields `3 d Z + B U - 18 γ B² + C(C0) = 0`. -/
theorem fiveToSix_qZero_terminal_dZ_sum_algebra68
    (gamma C0 : k) (B d v W U H T : k[X])
    (hU : U = (3 : k) • (W * d) + (8 : k) • (B ^ 2 * v))
    (hT : T = (2 : k) • (U - (21 * gamma : k) • B))
    (hBT : (4 : k) • H - C C0 = B * T)
    (hH : H = (2 : k) • (B ^ 3 * v) - (6 * gamma : k) • B ^ 2 +
      (9 : k) • d ^ 2) :
    (3 : k) • (d * (B * W - (12 : k) • d)) + B * U -
      (18 * gamma : k) • B ^ 2 + C C0 = 0 := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  have hU' := congrArg (algebraMap k[X] (RatFunc k)) hU
  have hT' := congrArg (algebraMap k[X] (RatFunc k)) hT
  have hBT' := congrArg (algebraMap k[X] (RatFunc k)) hBT
  have hH' := congrArg (algebraMap k[X] (RatFunc k)) hH
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
    map_neg, RatFunc.algebraMap_C] at hU' hT' hBT' hH' ⊢
  simp only [map_div₀, map_ofNat, map_one, map_zero] at hU' hT' hBT' hH' ⊢
  ring_nf at hU' hT' hBT' hH' ⊢
  linear_combination
    -hBT' -
      algebraMap k[X] (RatFunc k) B * hT' +
        (4 : RatFunc k) * hH' -
          algebraMap k[X] (RatFunc k) B * hU'

/-! ## Wall arithmetic `9N = 7S` -/

/-- Degree dictionary on the wall: `deg B = D`, `deg U = N-D`,
`deg d = V` satisfy `deg(BU) = N < V ≤ deg(d Z)` (any `Z ≠ 0`) and
`deg(B²) = 2D < N`. -/
theorem fiveToSix_qZero_terminal_wall_degree_arith68
    (N S : ℕ) (hN : 0 < N) (hEq : 9 * N = 7 * S) :
    let D := 3 * N - 2 * S
    let V := 5 * N - 3 * S
    0 < S ∧ 2 * S ≤ 3 * N ∧ N ≤ S ∧ 3 * S ≤ 5 * N ∧
      4 * S ≤ 6 * N ∧ 0 < D ∧ D ≤ N ∧ 0 < N - D ∧
      D + (N - D) = N ∧ 2 * D < N ∧ N < V := by
  let D := 3 * N - 2 * S
  let V := 5 * N - 3 * S
  change 0 < S ∧ 2 * S ≤ 3 * N ∧ N ≤ S ∧ 3 * S ≤ 5 * N ∧
    4 * S ≤ 6 * N ∧ 0 < D ∧ D ≤ N ∧ 0 < N - D ∧
    D + (N - D) = N ∧ 2 * D < N ∧ N < V
  have h7 : 7 ∣ 9 * N := by
    rw [hEq]
    exact dvd_mul_right 7 S
  have hcop : Nat.Coprime 7 9 := by decide
  have hN7 : 7 ∣ N := hcop.dvd_of_dvd_mul_left h7
  obtain ⟨m, hm⟩ := hN7
  have hmpos : 0 < m := by
    rw [hm] at hN
    omega
  have hSm : S = 9 * m := by
    have hmul : 7 * S = 9 * (7 * m) := by
      rw [← hEq, hm]
    have : 7 * S = 7 * (9 * m) := by
      rw [hmul]
      ring
    exact Nat.mul_left_cancel (by norm_num : 0 < 7) this
  subst hm
  subst hSm
  dsimp only [D, V]
  omega

/-! ## Degree comparison of the identity -/

/-- If `Z ≠ 0`, the term `3 d Z` strictly dominates `BU` and
`18 γ B²` at degree `deg d + deg Z ≥ V > N`. -/
theorem fiveToSix_qZero_terminal_dZ_nonzero_coeff_impossible_algebra68
    (gamma C0 : k) (B d U Z : k[X]) (N D V : ℕ)
    (hBdeg : B.natDegree = D)
    (hUdeg : U.natDegree = N - D)
    (hddeg : d.natDegree = V)
    (hBne : B ≠ 0)
    (hUne : U ≠ 0)
    (hdne : d ≠ 0)
    (hZne : Z ≠ 0)
    (hDsum : D + (N - D) = N)
    (hNltV : N < V)
    (h2Dlt : 2 * D < N)
    (hident : (3 : k) • (d * Z) + B * U -
      (18 * gamma : k) • B ^ 2 + C C0 = 0) :
    False := by
  let n := d.natDegree + Z.natDegree
  have hBUdeg : (B * U).natDegree = N := by
    rw [natDegree_mul hBne hUne, hBdeg, hUdeg, hDsum]
  have hnV : V ≤ n := by
    dsimp only [n]
    rw [hddeg]
    exact Nat.le_add_right _ _
  have hNltn : N < n := lt_of_lt_of_le hNltV hnV
  have h2Dltn : 2 * D < n := lt_trans h2Dlt hNltn
  have hBUlt : (B * U).natDegree < n := by
    rw [hBUdeg]
    exact hNltn
  have hB2le : ((18 * gamma : k) • B ^ 2).natDegree ≤ 2 * D :=
    (natDegree_smul_le (18 * gamma : k) (B ^ 2)).trans (by
      rw [natDegree_pow, hBdeg])
  have hB2lt : ((18 * gamma : k) • B ^ 2).natDegree < n :=
    lt_of_le_of_lt hB2le h2Dltn
  have hClt : (C C0 : k[X]).natDegree < n := by
    rw [natDegree_C]
    exact lt_of_le_of_lt (Nat.zero_le N) hNltn
  have h3dZ : ((3 : k) • (d * Z)).coeff n ≠ 0 := by
    have hnZ : n = (d * Z).natDegree := by
      dsimp only [n]
      exact (natDegree_mul hdne hZne).symm
    rw [coeff_smul, smul_eq_mul, hnZ, coeff_natDegree, leadingCoeff_mul]
    exact mul_ne_zero (by norm_num : (3 : k) ≠ 0)
      (mul_ne_zero (leadingCoeff_ne_zero.mpr hdne)
        (leadingCoeff_ne_zero.mpr hZne))
  have hsumcoeff :
      ((3 : k) • (d * Z) + B * U - (18 * gamma : k) • B ^ 2 +
          C C0).coeff n =
        ((3 : k) • (d * Z)).coeff n := by
    simp only [coeff_add, coeff_sub,
      coeff_eq_zero_of_natDegree_lt hBUlt,
      coeff_eq_zero_of_natDegree_lt hB2lt,
      coeff_eq_zero_of_natDegree_lt hClt, add_zero, sub_zero]
  have hzero : ((3 : k) • (d * Z) + B * U -
      (18 * gamma : k) • B ^ 2 + C C0).coeff n = 0 := by
    rw [hident, coeff_zero]
  exact h3dZ (hsumcoeff ▸ hzero)

/-- If `Z = 0`, the identity collapses to `BU = 18 γ B² - C(C0)`,
whose sides have degrees `N` and at most `2D < N`. -/
theorem fiveToSix_qZero_terminal_dZ_zero_coeff_impossible_algebra68
    (gamma C0 : k) (B d U : k[X]) (N D : ℕ)
    (hBdeg : B.natDegree = D)
    (hUdeg : U.natDegree = N - D)
    (hBne : B ≠ 0)
    (hUne : U ≠ 0)
    (hDsum : D + (N - D) = N)
    (h2Dlt : 2 * D < N)
    (hNpos : 0 < N)
    (hident : (3 : k) • (d * (0 : k[X])) + B * U -
      (18 * gamma : k) • B ^ 2 + C C0 = 0) :
    False := by
  have hcollapse : B * U - (18 * gamma : k) • B ^ 2 + C C0 = 0 := by
    simpa using hident
  have hEQ : B * U = (18 * gamma : k) • B ^ 2 - C C0 := by
    linear_combination hcollapse
  have hBUdeg : (B * U).natDegree = N := by
    rw [natDegree_mul hBne hUne, hBdeg, hUdeg, hDsum]
  have hBUcoeff : (B * U).coeff N ≠ 0 := by
    have hn : N = (B * U).natDegree := hBUdeg.symm
    rw [hn, coeff_natDegree, leadingCoeff_mul]
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr hBne)
      (leadingCoeff_ne_zero.mpr hUne)
  have hRdeg :
      (((18 * gamma : k) • B ^ 2) - C C0).natDegree < N := by
    have hle :=
      natDegree_sub_le ((18 * gamma : k) • B ^ 2) (C C0)
    have hmax :
        max (((18 * gamma : k) • B ^ 2).natDegree)
          (C C0 : k[X]).natDegree < N := by
      refine max_lt ?_ ?_
      · exact lt_of_le_of_lt
          ((natDegree_smul_le (18 * gamma : k) (B ^ 2)).trans (by
            rw [natDegree_pow, hBdeg])) h2Dlt
      · rw [natDegree_C]
        exact hNpos
    exact lt_of_le_of_lt hle hmax
  have hRcoeff : (((18 * gamma : k) • B ^ 2) - C C0).coeff N = 0 :=
    coeff_eq_zero_of_natDegree_lt hRdeg
  have : (B * U).coeff N = 0 := by
    rw [hEQ, hRcoeff]
  exact hBUcoeff this

/-! ## Source-facing assembly -/

/-- The terminal H-quotient / U-profile packet on `9N = 7S` is
inconsistent. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_impossible68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hterminal : terminal ≠ 0)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hf : (((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B).coeff 0 = 0) :
    False := by
  let D := 3 * N - 2 * S
  let V := 5 * N - 3 * S
  let H := FiveToSixQZeroFceZeroH68 B c d
  obtain ⟨i3, v, T, hv, hvdeg0, hTdef, hBT, hTdeg⟩ :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_H_quotient68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq hf
  obtain ⟨v', W, U, hv', hv'deg, hWdef, hWdeg, hUdef, hUdeg, _, _, _⟩ :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_U_profile68
      alpha gamma epsilon zeta eta terminal A B c d e N G S
      hterminal hs hq hf
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
  have hvuniq : v' = v := by
    apply mul_left_cancel₀ hBne
    rw [← hv', ← hv]
  subst v'
  have hd' : d.natDegree ≤ V := by dsimp only [V]; omega
  have hdidx : V = 5 * N - G - S := by dsimp only [V]; omega
  have hdcoeff : d.coeff V ≠ 0 := by rw [hdidx]; exact hdtop
  have hddeg : d.natDegree = V :=
    natDegree_eq_of_le_of_coeff_ne_zero hd' hdcoeff
  have hdne : d ≠ 0 := by
    intro hz
    apply hdcoeff
    rw [hz, coeff_zero]
  have harith :=
    fiveToSix_qZero_terminal_wall_degree_arith68 N S hN hEq
  rcases harith with
    ⟨_, _, _, _, _, _, _, hNDpos, hDsum, h2Dlt, hNltV⟩
  have hUne : U ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hUdeg
    exact hNDpos.ne hUdeg
  have hTform :
      T = (2 : k) • (U - (21 * gamma : k) • B) :=
    fiveToSix_qZero_terminal_T_from_U_algebra68
      gamma A B d v W U T hWdef hUdef hTdef
  have hH : H =
      (2 : k) • (B ^ 3 * v) - (6 * gamma : k) • B ^ 2 +
        (9 : k) • d ^ 2 :=
    fiveToSix_qZero_terminal_H_from_Cg_algebra68 gamma B c d v hv
  let C0 := 81 * epsilon * gamma + 27 * i3
  let Z := B * W - (12 : k) • d
  have hident :
      (3 : k) • (d * Z) + B * U - (18 * gamma : k) • B ^ 2 +
        C C0 = 0 := by
    simpa only [Z, H] using
      fiveToSix_qZero_terminal_dZ_sum_algebra68
        gamma C0 B d v W U H T hUdef hTform hBT hH
  by_cases hZ : Z = 0
  · rw [hZ] at hident
    exact fiveToSix_qZero_terminal_dZ_zero_coeff_impossible_algebra68
      gamma C0 B d U N D hBdeg hUdeg hBne hUne hDsum h2Dlt hN hident
  · exact fiveToSix_qZero_terminal_dZ_nonzero_coeff_impossible_algebra68
      gamma C0 B d U Z N D V hBdeg hUdeg hddeg hBne hUne hdne hZ
      hDsum hNltV h2Dlt hident

#print axioms fiveToSix_qZero_terminal_BU_minus_four_F_algebra68
#print axioms fiveToSix_qZero_terminal_H_from_Cg_algebra68
#print axioms fiveToSix_qZero_terminal_T_from_U_algebra68
#print axioms fiveToSix_qZero_terminal_dZ_sum_algebra68
#print axioms fiveToSix_qZero_terminal_wall_degree_arith68
#print axioms fiveToSix_qZero_terminal_dZ_nonzero_coeff_impossible_algebra68
#print axioms fiveToSix_qZero_terminal_dZ_zero_coeff_impossible_algebra68
#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_terminal_impossible68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroTerminalBranchClosure68

end Max11DegreeRoutes
