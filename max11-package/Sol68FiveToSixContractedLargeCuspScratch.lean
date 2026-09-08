import Sol68FiveToSixCuspConsumerScratch

/-! # Exact contraction of the large five-to-six cusp residual

Every surviving cusp is aligned on the expansion lattice.  This file
contracts its exact radius, gap, and edge witness by `60`, transports the
degree bounds and cusp equation to the original polynomials, and attaches
the complete source interface: both first integrals, both zero RHS lower
rows, and every positive coefficient of the constant-RHS row zero.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixContractedLargeCusp68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Contracted source packet at an arbitrary aligned cusp edge.  The `d,e`
bounds are the common source bounds at the first stride; terminal callers
retain their stronger terminal bounds separately. -/
def FiveToSixContractedCuspPacket68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ) : Prop :=
  0 < N ∧ 5 * N < 2 * G ∧ 2 * G ≤ 6 * N ∧
    A.natDegree ≤ 2 * N ∧ B.natDegree ≤ 3 * N - G ∧
    c.natDegree ≤ 4 * N - G ∧ d.natDegree ≤ 5 * N - G - 1 ∧
    e.natDegree ≤ 6 * N - G - 1 ∧ A.coeff (2 * N) ≠ 0 ∧
    FiveToSixCuspEdge68 A B c d e N G S ∧
    FiveToSixTerminalRHSAdapter68 alpha gamma epsilon zeta eta terminal
      A B c d e

/-- Exact contracted form of the large residual. -/
def FiveToSixContractedLargeCuspResidual68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (n g : ℕ) : Prop :=
  (∃ N G S, n = 60 * N ∧ g = 60 * G ∧ 2 < N ∧
      0 < S ∧ S < 7 * N - 2 * G ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G S) ∨
    (∃ N G, n = 60 * N ∧ g = 60 * G ∧ 2 < N ∧
      d.natDegree ≤ G - 2 * N ∧ e.natDegree ≤ G - N ∧ zeta = 0 ∧
      FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
        A B c d e N G (7 * N - 2 * G) ∧
      SecondaryResidualBetweenFace68
        (A.coeff (2 * N)) (B.coeff (3 * N - G))
        (c.coeff (4 * N - G)) (d.coeff (G - 2 * N))
        (e.coeff (G - N)))

/-- Source-backed contraction of one exact aligned cusp. -/
theorem integratedPolynomialLowerSystem68_fiveToSix_contract_cusp68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (N G S : ℕ)
    (hradius :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n = 60 * N ∧ g = 60 * G)
    (hcusp :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      FiveToSixCuspEdge68 Ae Be ce d ee n g (60 * S)) :
    FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B (cubicCDefectPolynomial68 A C0)
      (secondaryDDefectPolynomial68 A B D)
      (cubicEDefectPolynomial68 A C0 E) N G S := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  let cu := cubicCDefectPolynomial68 A C0
  let du := secondaryDDefectPolynomial68 A B D
  let eu := cubicEDefectPolynomial68 A C0 E
  change n = 60 * N ∧ g = 60 * G at hradius
  change FiveToSixCuspEdge68 Ae Be ce d ee n g (60 * S) at hcusp
  have hinventory := integratedPolynomialLowerSystem68_global_terminalLoad_inventory
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change FiveToSixGlobalResidual68 zeta Ae Be ce De ee d n g ∧ _ at hinventory
  rcases hinventory.1 with
    ⟨hgt5, hle6, _hfour, _hthree, _hn30, _hg30, _hnBig, _hvanish,
      hd60, he60, _hpost, _hnot120, _hcases⟩
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n := ⟨hgt5, hle6⟩
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hsource :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_offsetNinety_with_terminalRHS68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          (show 3 * n ≤ 2 * g by omega))
  change _ ∧ FiveToSixTerminalRHSAdapter68 alpha gamma epsilon zeta eta
    terminal A B cu du eu at hsource
  have hcexpand : ce = expand k 60 cu := by
    simpa only [ce, Ae, Ce, cu] using
      expand_cubicCDefectPolynomial68 60 A C0
  have hdexpand : d = expand k 60 du := by
    simpa only [d, Ae, Be, De, du] using
      secondaryDDefectPolynomial68_expand 60 A B D
  have heexpand : ee = expand k 60 eu := by
    simpa only [ee, Ae, Ce, Ee, eu] using
      expand_cubicEDefectPolynomial68 60 A C0 E
  have hA : A.natDegree ≤ 2 * N := by
    have h := data.hA
    simp only [Ae, natDegree_expand, hradius.1] at h
    omega
  have hB : B.natDegree ≤ 3 * N - G := by
    have h := data.hB
    simp only [Be, natDegree_expand, hradius.1, hradius.2] at h
    omega
  have hc : cu.natDegree ≤ 4 * N - G := by
    have h := data.hc
    rw [hcexpand, natDegree_expand, hradius.1, hradius.2] at h
    omega
  have hd : du.natDegree ≤ 5 * N - G - 1 := by
    have h : (expand k 60 du).natDegree ≤ 5 * n - g - 60 := by
      rw [← hdexpand]
      exact hd60
    rw [natDegree_expand, hradius.1, hradius.2] at h
    omega
  have he : eu.natDegree ≤ 6 * N - G - 1 := by
    have h : (expand k 60 eu).natDegree ≤ 6 * n - g - 60 := by
      rw [← heexpand]
      exact he60
    rw [natDegree_expand, hradius.1, hradius.2] at h
    omega
  have ha : A.coeff (2 * N) ≠ 0 := by
    have h := data.ha
    have hAidx : 2 * n = 60 * (2 * N) := by omega
    simpa [Ae, hAidx, coeff_expand] using h
  have hAidx : 2 * n = 60 * (2 * N) := by omega
  have hBidx : 3 * n - g = 60 * (3 * N - G) := by omega
  have hcidx : 4 * n - g = 60 * (4 * N - G) := by omega
  have hdidx : 5 * n - g - 60 * S = 60 * (5 * N - G - S) := by omega
  have heidx : 6 * n - g - 60 * S = 60 * (6 * N - G - S) := by omega
  have hcuspContracted : FiveToSixCuspEdge68 A B cu du eu N G S := by
    change _ ≠ 0 ∧ _ ≠ 0 ∧ _ ≠ 0 ∧ _ ≠ 0 ∧ _ = 0
    change _ ≠ 0 ∧ _ ≠ 0 ∧ _ ≠ 0 ∧ _ ≠ 0 ∧ _ = 0 at hcusp
    simpa [Ae, Be, hcexpand, hdexpand, heexpand, hAidx, hBidx, hcidx,
      hdidx, heidx, coeff_expand] using hcusp
  exact ⟨by omega, by omega, by omega, hA, hB, hc, hd, he, ha,
    hcuspContracted, hsource.2⟩

/-- Uniform contracted first-jet consumer.  Once the sharp support bounds
at the witnessed edge are available, the exact contracted I4/I3 rows give
both singular face equations.  This isolates the precise datum not retained
by the earlier-cusp projection of the complete stride theorem. -/
theorem fiveToSix_contractedCusp_firstJet68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G S : ℕ)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G S)
    (hS : 0 < S) (hload : S < 7 * N - 2 * G)
    (hdSharp : d.natDegree ≤ 5 * N - G - S)
    (heSharp : e.natDegree ≤ 6 * N - G - S) :
    SecondaryResidualBetweenFace68
        (A.coeff (2 * N)) (B.coeff (3 * N - G))
        (c.coeff (4 * N - G)) (d.coeff (5 * N - G - S))
        (e.coeff (6 * N - G - S)) ∧
      A.coeff (2 * N) * B.coeff (3 * N - G) ^ 2 +
        3 * c.coeff (4 * N - G) ^ 2 = 0 := by
  rcases hpacket with
    ⟨hN, hgt5, hle6, hA, hB, hc, _hd, _he, _ha, hcusp, hadapter⟩
  rcases hadapter with
    ⟨i4, i3, hi4, hi3, _hrow0, _hrow1, _hrow2, _hrow0pos, _hiff⟩
  constructor
  · exact polynomialSecondaryResidualUniformFace68_fiveToSix
      gamma epsilon zeta i4 i3 A B c d e N G S hN hS
      ⟨hgt5, hle6⟩ hload hA hB hc hdSharp heSharp hi4 hi3
  · exact hcusp.2.2.2.2

/-- At the contracted terminal wall the literal zeta load is zero, so the
terminal I4/I3 coefficients give the same two face equations exactly. -/
theorem fiveToSix_contractedCusp_terminalFace68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) (N G : ℕ)
    (hpacket : FiveToSixContractedCuspPacket68
      alpha gamma epsilon zeta eta terminal A B c d e N G
        (7 * N - 2 * G))
    (hdTerminal : d.natDegree ≤ G - 2 * N)
    (heTerminal : e.natDegree ≤ G - N) (hzeta : zeta = 0) :
    SecondaryResidualBetweenFace68
      (A.coeff (2 * N)) (B.coeff (3 * N - G))
      (c.coeff (4 * N - G)) (d.coeff (G - 2 * N))
      (e.coeff (G - N)) := by
  rcases hpacket with
    ⟨hN, hgt5, hle6, hA, hB, hc, _hd, _he, _ha, _hcusp, hadapter⟩
  rcases hadapter with
    ⟨i4, i3, hi4, hi3, _hrow0, _hrow1, _hrow2, _hrow0pos, _hiff⟩
  have hcoeff4 := congrArg (fun p : k[X] => p.coeff (2 * N)) hi4
  rw [cubicFirstIntegralFourPolynomial68_coeff_terminalLoad_fiveToSix
    gamma epsilon zeta A B c d e N G hN ⟨hgt5, hle6⟩
    hA hB hc hdTerminal heTerminal] at hcoeff4
  simp only [coeff_C, if_neg (by omega : 2 * N ≠ 0)] at hcoeff4
  have hfour : B.coeff (3 * N - G) * e.coeff (G - N) +
      c.coeff (4 * N - G) * d.coeff (G - 2 * N) = 0 := by
    rw [hzeta, zero_mul, add_zero] at hcoeff4
    exact (mul_eq_zero.mp hcoeff4).resolve_left (by norm_num)
  have hcoeff3 := congrArg (fun p : k[X] => p.coeff (3 * N)) hi3
  rw [cubicFirstIntegralThreePolynomial68_coeff_terminalLoad_fiveToSix
    gamma epsilon zeta A B c d e N G hN ⟨hgt5, hle6⟩
    hA hB hc hdTerminal heTerminal] at hcoeff3
  simp only [coeff_C, if_neg (by omega : 3 * N ≠ 0)] at hcoeff3
  have hthree : -A.coeff (2 * N) * B.coeff (3 * N - G) *
        d.coeff (G - 2 * N) +
      3 * c.coeff (4 * N - G) * e.coeff (G - N) = 0 := by
    have hz := (mul_eq_zero.mp hcoeff3).resolve_left (by norm_num)
    linear_combination hz
  exact ⟨hfour, hthree⟩

/-- Complete source consumer through exact contraction.  The zero terminal
edge is unchanged; every cusp residual is returned in original polynomial
coordinates with its exact contracted witness and source equations. -/
theorem integratedPolynomialLowerSystem68_fiveToSix_contracted_consumer68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    let d := secondaryDDefectPolynomial68 Ae Be De
    FiveToSixTerminalZeroPacket68 zeta d ee n g ∨
      FiveToSixContractedLargeCuspResidual68 alpha gamma epsilon zeta eta
        terminal A B (cubicCDefectPolynomial68 A C0)
        (secondaryDDefectPolynomial68 A B D)
        (cubicEDefectPolynomial68 A C0 E) n g := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  let cu := cubicCDefectPolynomial68 A C0
  let du := secondaryDDefectPolynomial68 A B D
  let eu := cubicEDefectPolynomial68 A C0 E
  have hconsumer := integratedPolynomialLowerSystem68_fiveToSix_consume_cusps68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change FiveToSixTerminalZeroPacket68 zeta d ee n g ∨
    FiveToSixLargeCuspResidual68 zeta Ae Be ce d ee n g at hconsumer
  rcases hconsumer with hzero | hlarge
  · exact Or.inl hzero
  · right
    rcases hlarge with hearly | hterminalCusp
    · rcases hearly with
        ⟨s, hnBig, hn60, hg60, hs60, hs, hsr, hcusp⟩
      obtain ⟨N, hN⟩ := hn60
      obtain ⟨G, hG⟩ := hg60
      obtain ⟨S, hS⟩ := hs60
      have hpacket :=
        integratedPolynomialLowerSystem68_fiveToSix_contract_cusp68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
          hterminal hsys N G S
          (by
            simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
              ⟨hN, hG⟩)
          (by
            rw [hS] at hcusp
            simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hcusp)
      left
      exact ⟨N, G, S, hN, hG, by omega, by omega, by omega, hpacket⟩
    · rcases hterminalCusp with
        ⟨hnBig, hn60, hg60, hdTerminal, heTerminal, hzeta, hcusp⟩
      obtain ⟨N, hN⟩ := hn60
      obtain ⟨G, hG⟩ := hg60
      have hr : 7 * n - 2 * g = 60 * (7 * N - 2 * G) := by omega
      have hpacket :=
        integratedPolynomialLowerSystem68_fiveToSix_contract_cusp68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
          hterminal hsys N G (7 * N - 2 * G)
          (by
            simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
              ⟨hN, hG⟩)
          (by
            rw [hr] at hcusp
            simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hcusp)
      have hdexpand : d = expand k 60 du := by
        simpa only [d, Ae, Be, De, du] using
          secondaryDDefectPolynomial68_expand 60 A B D
      have heexpand : ee = expand k 60 eu := by
        simpa only [ee, Ae, Ce, Ee, eu] using
          expand_cubicEDefectPolynomial68 60 A C0 E
      have hdContracted : du.natDegree ≤ G - 2 * N := by
        have h : (expand k 60 du).natDegree ≤ g - 2 * n := by
          rw [← hdexpand]
          exact hdTerminal
        rw [natDegree_expand, hN, hG] at h
        omega
      have heContracted : eu.natDegree ≤ G - N := by
        have h : (expand k 60 eu).natDegree ≤ g - n := by
          rw [← heexpand]
          exact heTerminal
        rw [natDegree_expand, hN, hG] at h
        omega
      have hface := fiveToSix_contractedCusp_terminalFace68
        alpha gamma epsilon zeta eta terminal A B cu du eu N G hpacket
        hdContracted heContracted hzeta
      right
      exact ⟨N, G, hN, hG, by omega, hdContracted, heContracted,
        hzeta, hpacket, hface⟩

#print axioms integratedPolynomialLowerSystem68_fiveToSix_contract_cusp68
#print axioms integratedPolynomialLowerSystem68_fiveToSix_contracted_consumer68

end FiveToSixContractedLargeCusp68

end Max11DegreeRoutes
