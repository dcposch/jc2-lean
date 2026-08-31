import Sol68FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroDivisibilityScratch

/-! # Source consequences of the zero-`Fce` divisibility split -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroDivisibilitySource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The noncoprime branch has a literal common root.  In the coprime branch
the original cusp divides by `B²`, leaving the finite reduced cusp
`R=4c+9u²` with exact degrees `deg u=V-D` and `deg R=Q-2D`. -/
theorem fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_divisibility_source68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hs : FiveToSixCuspZetaFirstB3EqualitySupportRowOnePacket68 alpha gamma
      epsilon zeta eta terminal A B c d e N G S)
    (hq : 9 * N - 7 * S = 0)
    (hf : (((B * e + c * d) - (1 / 9 : k) • B ^ 3) +
      (3 / 2 * gamma : k) • d + (3 / 4 * epsilon : k) • B).coeff 0 = 0) :
    let D := 3 * N - 2 * S
    let Cc := 4 * N - 2 * S
    let V := 5 * N - 3 * S
    let Q := D + 2 * N - Cc
    let Cg := (2 : k) • c + C (3 * gamma)
    let H := FiveToSixQZeroFceZeroH68 B c d
    (∃ x : k, B.eval x = 0 ∧ Cg.eval x = 0) ∨
      ∃ u R : k[X],
        d = B * u ∧ H = B ^ 2 * R ∧
        R = (4 : k) • c + (9 : k) • u ^ 2 ∧
        u.natDegree = V - D ∧ R.natDegree = Q - 2 * D := by
  let D := 3 * N - 2 * S
  let Cc := 4 * N - 2 * S
  let V := 5 * N - 3 * S
  let p := 2 * N
  let Q := D + p - Cc
  let Cg := (2 : k) • c + C (3 * gamma)
  let H := FiveToSixQZeroFceZeroH68 B c d
  change (∃ x : k, B.eval x = 0 ∧ Cg.eval x = 0) ∨
    ∃ u R : k[X], d = B * u ∧ H = B ^ 2 * R ∧
      R = (4 : k) • c + (9 : k) • u ^ 2 ∧
      u.natDegree = V - D ∧ R.natDegree = Q - 2 * D
  have hglobal :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_global68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq hf
  rcases hglobal with ⟨i3, hFzero, hRce, hK⟩
  obtain ⟨kappa, hP⟩ :=
    fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_rowTwo_integral68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq hf
  have hsplit := fiveToSix_qZero_Fce_zero_coprime_or_commonFactor68
    gamma epsilon kappa A B c d e hFzero hP
  change ¬ IsCoprime B Cg ∨ (B ∣ d ∧ B ∣ H) at hsplit
  rcases hsplit with hcommon | hcoprimeDiv
  · left
    have hnot : ¬ (∀ x : k, aeval x B ≠ 0 ∨ aeval x Cg ≠ 0) := by
      intro hall
      exact hcommon
        ((Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
          (k := k) k B Cg).2 hall)
    push Not at hnot
    obtain ⟨x, hBx, hCx⟩ := hnot
    exact ⟨x, by simpa [aeval_def] using hBx,
      by simpa [aeval_def] using hCx⟩
  · right
    obtain ⟨u, hdu⟩ := hcoprimeDiv.1
    let R := (4 : k) • c + (9 : k) • u ^ 2
    have hHfac : H = B ^ 2 * R := by
      dsimp only [H, FiveToSixQZeroFceZeroH68, R]
      rw [hdu]
      apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
      simp only [pow_two, Polynomial.smul_eq_C_mul, map_add, map_mul,
        RatFunc.algebraMap_C]
      ring
    have hloaded := hs.1
    rcases fiveToSix_zetaFirst_B3_equality_supportLoaded_source68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hloaded with
      ⟨hGS, hGamma, hsource⟩
    have hp0 := hsource
    change 0 < S ∧ S < 7 * N - 2 * G ∧
        d.natDegree ≤ 5 * N - G - S ∧
        e.natDegree ≤ 6 * N - G - S ∧
        FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
          A B c d e N G S ∧ _ at hp0
    rcases hp0 with ⟨hS, hSR, hd, he, hpacket, hrest⟩
    rcases hpacket with
      ⟨hN, hgt, hle, hA, hB, hc, hd0, he0, hatop, hcusp, had⟩
    rcases hcusp with ⟨hBtop, hctop, hdtop, hetop, hcuspEq⟩
    have hnxt := fiveToSix_zetaFirst_B3_equality_support_qZero_next68
      alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq
    dsimp only [FiveToSixCuspZetaFirstB3EqualitySupportQZeroNextScalar68]
      at hnxt
    have hEq : 9 * N = 7 * S := hnxt.1.1
    have hB' : B.natDegree ≤ D := by dsimp only [D]; omega
    have hd' : d.natDegree ≤ V := by dsimp only [V]; omega
    have hbidx : D = 3 * N - G := by dsimp only [D]; omega
    have hdidx : V = 5 * N - G - S := by dsimp only [V]; omega
    have hbcoeff : B.coeff D ≠ 0 := by rw [hbidx]; exact hBtop
    have hdcoeff : d.coeff V ≠ 0 := by rw [hdidx]; exact hdtop
    have hBdeg : B.natDegree = D :=
      natDegree_eq_of_le_of_coeff_ne_zero hB' hbcoeff
    have hddeg : d.natDegree = V :=
      natDegree_eq_of_le_of_coeff_ne_zero hd' hdcoeff
    have hHtop :=
      fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_H_top68
        alpha gamma epsilon zeta eta terminal A B c d e N G S hs hq hf
    change c.coeff Cc * H.coeff Q = -(B.coeff D ^ 3 * d.coeff V) ∧
      H.natDegree = Q at hHtop
    have hBne : B ≠ 0 := by
      intro hz
      apply hbcoeff
      rw [hz, coeff_zero]
    have hdne : d ≠ 0 := by
      intro hz
      apply hdcoeff
      rw [hz, coeff_zero]
    have hune : u ≠ 0 := by
      intro hz
      apply hdne
      rw [hdu, hz, mul_zero]
    have hHne : H ≠ 0 := by
      intro hz
      rw [hz, natDegree_zero] at hHtop
      dsimp only [D, Cc, V, p, Q] at hHtop
      omega
    have hRne : R ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hHfac
      exact hHne hHfac
    have hudeg : u.natDegree = V - D := by
      have hdeg := natDegree_mul hBne hune
      rw [← hdu, hBdeg, hddeg] at hdeg
      omega
    have hRdeg : R.natDegree = Q - 2 * D := by
      have hBRne : B * R ≠ 0 := mul_ne_zero hBne hRne
      have hdegBR := natDegree_mul hBne hRne
      have hdegH := natDegree_mul hBne hBRne
      have hHfac' : H = B * (B * R) := by rw [hHfac]; ring
      rw [← hHfac', hHtop.2, hBdeg, hdegBR, hBdeg] at hdegH
      omega
    exact ⟨u, R, hdu, hHfac, rfl, hudeg, hRdeg⟩

#print axioms fiveToSix_zetaFirst_B3_equality_support_qZero_Fce_zero_divisibility_source68

end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroFceZeroDivisibilitySource68

end Max11DegreeRoutes
