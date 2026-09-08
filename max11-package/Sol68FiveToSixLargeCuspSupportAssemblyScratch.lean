import Sol68FiveToSixContractedLargeCuspScratch
import Fable68FiveToSixUniformCuspResultantScratch

/-! # Sharp support and second jet on the large five-to-six cusp

The complete stride conclusion remembers an earlier cusp but projects away
the support bounds at that edge.  They are recovered without replaying the
induction: choose the least aligned cusp and invoke the existing aligned
iterator only up to its index.  Minimality deletes the iterator's earlier
cusp alternative, leaving the sharp support at the same witness.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixLargeCuspSupportAssembly68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Exact earlier cusp packet with the contemporaneous support bounds. -/
def FiveToSixSupportedEarlierCusp68
    (A B c d e : k[X]) (n g : ℕ) : Prop :=
  ∃ s, 120 < n ∧ 60 ∣ n ∧ 60 ∣ g ∧ 60 ∣ s ∧
    0 < s ∧ s < 7 * n - 2 * g ∧
    d.natDegree ≤ 5 * n - g - s ∧
    e.natDegree ≤ 6 * n - g - s ∧
    FiveToSixCuspEdge68 A B c d e n g s

/-- Singular second-jet output at an exact supported earlier edge. -/
def FiveToSixCuspSecondJetResidual68
    (zeta : k) (A B c d e : k[X]) (n g s : ℕ) : Prop :=
  SecondaryResidualBetweenFace68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - g - s))
      (e.coeff (6 * n - g - s)) ∧
    (2 * A.coeff (2 * n) * B.coeff (3 * n - g) *
        (B.coeff (3 * n - g) * c.coeff (4 * n - g - 60) -
          c.coeff (4 * n - g) * uniformCuspSecondJetB68 B n g) -
      A.coeff (2 * n - 60) * B.coeff (3 * n - g) ^ 2 *
        c.coeff (4 * n - g)) * d.coeff (5 * n - g - s) +
      (3 / 8 : k) * zeta * A.coeff (2 * n) *
        B.coeff (3 * n - g) ^ 2 *
        A.coeff (9 * n - 2 * g - s - 60) +
      (3 / 2 : k) * B.coeff (3 * n - g) * c.coeff (4 * n - g) *
        (d ^ 2).coeff (10 * n - 2 * g - s - 60) = 0

/-- The exact conjunction of contracted source data, sharp contracted
support, and the verified expanded singular second-jet recurrence. -/
def FiveToSixContractedEarlierSecondJetAssembly68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e Ae Be ce de ee : k[X]) (n g : ℕ) : Prop :=
  ∃ s N G S, n = 60 * N ∧ g = 60 * G ∧ s = 60 * S ∧
    2 < N ∧ 0 < S ∧ S < 7 * N - 2 * G ∧
    d.natDegree ≤ 5 * N - G - S ∧ e.natDegree ≤ 6 * N - G - S ∧
    FiveToSixContractedCuspPacket68 alpha gamma epsilon zeta eta terminal
      A B c d e N G S ∧
    FiveToSixCuspSecondJetResidual68 zeta Ae Be ce de ee n g s

/-- Strengthened honest large residual, with terminal kept separate. -/
def FiveToSixSupportedLargeCuspResidual68
    (zeta : k) (A B c d e : k[X]) (n g : ℕ) : Prop :=
  FiveToSixSupportedEarlierCusp68 A B c d e n g ∨
    (120 < n ∧ 60 ∣ n ∧ 60 ∣ g ∧
      d.natDegree ≤ g - 2 * n ∧ e.natDegree ≤ g - n ∧ zeta = 0 ∧
      FiveToSixCuspEdge68 A B c d e n g (7 * n - 2 * g))

/-- Least-cusp wrapper around the verified aligned iterator. -/
theorem integratedPolynomialLowerSystem68_fiveToSix_leastCusp_support68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (s : ℕ) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hbig : 120 < weightedRadius68 A B C0 D E)
    (hn60 : 60 ∣ weightedRadius68 A B C0 D E)
    (hg60 :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      60 ∣ g)
    (hs60 : 60 ∣ s) (hs : 0 < s)
    (hsr :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      s < 7 * n - 2 * g)
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
      FiveToSixCuspEdge68 Ae Be ce d ee n g s) :
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
    ∃ t, 0 < t ∧ t ≤ s ∧ t < 7 * n - 2 * g ∧ 60 ∣ t ∧
      d.natDegree ≤ 5 * n - g - t ∧
      ee.natDegree ≤ 6 * n - g - t ∧
      FiveToSixCuspEdge68 Ae Be ce d ee n g t := by
  classical
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
  change 120 < n at hbig
  change 60 ∣ n at hn60
  change 60 ∣ g at hg60
  change s < 7 * n - 2 * g at hsr
  change FiveToSixCuspEdge68 Ae Be ce d ee n g s at hcusp
  have hinventory := integratedPolynomialLowerSystem68_global_terminalLoad_inventory
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change FiveToSixGlobalResidual68 zeta Ae Be ce De ee d n g ∧ _ at hinventory
  rcases hinventory.1 with
    ⟨hgt5, hle6, _hfour, _hthree, _hn30, _hg30, _hnBig, _hvanish,
      hd60, he60, _hpost, _hnot120, _hcases⟩
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n := ⟨hgt5, hle6⟩
  obtain ⟨N, hN⟩ := hn60
  obtain ⟨G, hG⟩ := hg60
  obtain ⟨S, hS⟩ := hs60
  have hSpos : 0 < S := by omega
  let P : ℕ → Prop := fun j =>
    FiveToSixCuspEdge68 Ae Be ce d ee n g (60 + 60 * j)
  have hPcandidate : P (S - 1) := by
    have hedge : 60 + 60 * (S - 1) = s := by omega
    simpa only [P, hedge] using hcusp
  have hex : ∃ j, P j := ⟨S - 1, hPcandidate⟩
  let j0 := Nat.find hex
  have hP0 : P j0 := Nat.find_spec hex
  have hj0le : j0 ≤ S - 1 := Nat.find_min' hex hPcandidate
  have htLe : 60 + 60 * j0 ≤ s := by omega
  have htLoad : 60 + 60 * j0 < 7 * n - 2 * g := by omega
  have hdphase : 60 ∣ 5 * n - g - 60 := by
    refine ⟨5 * N - G - 1, ?_⟩
    omega
  have hephase : 60 ∣ 6 * n - g - 60 := by
    refine ⟨6 * N - G - 1, ?_⟩
    omega
  have hiter :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_aligned_iterate68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      60 j0 hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
      (by norm_num)
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          (⟨hdphase, hephase⟩ :
            60 ∣ 5 * n - g - 60 ∧ 60 ∣ 6 * n - g - 60))
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using
          (⟨hd60, he60⟩ :
            d.natDegree ≤ 5 * n - g - 60 ∧
              ee.natDegree ≤ 6 * n - g - 60))
      (by
        simp only [n, Ae, Be, Ce, ce, De, Ee, ee, g]
        intro j hj
        exact lt_of_lt_of_le (by omega : 60 + 60 * j < 60 + 60 * j0)
          (Nat.le_of_lt htLoad))
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          (show 60 + 60 * j0 ≤ 5 * n - g ∧
              60 + 60 * j0 ≤ 6 * n - g by constructor <;> omega))
  change (∃ j, j < j0 ∧ P j) ∨
    (d.natDegree ≤ 5 * n - g - (60 + 60 * j0) ∧
      ee.natDegree ≤ 6 * n - g - (60 + 60 * j0)) at hiter
  have hdrop := hiter.resolve_left (by
    rintro ⟨j, hj, hPj⟩
    exact (Nat.not_lt_of_ge (Nat.find_min' hex hPj)) hj)
  exact ⟨60 + 60 * j0, by omega, htLe, htLoad, ⟨j0 + 1, by omega⟩,
    hdrop.1, hdrop.2, hP0⟩

/-- Repackage the complete consumer so its earlier alternative carries
sharp support at the retained least exact cusp witness. -/
theorem integratedPolynomialLowerSystem68_fiveToSix_supported_consumer68
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
      FiveToSixSupportedLargeCuspResidual68 zeta Ae Be ce d ee n g := by
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
      have hsupported :=
        integratedPolynomialLowerSystem68_fiveToSix_leastCusp_support68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E s
          hterminal hsys (by simpa only [n] using hnBig)
          (by simpa only [n] using hn60)
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hg60)
          hs60 hs
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsr)
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hcusp)
      change ∃ t, 0 < t ∧ t ≤ s ∧ t < 7 * n - 2 * g ∧ 60 ∣ t ∧
        d.natDegree ≤ 5 * n - g - t ∧
        ee.natDegree ≤ 6 * n - g - t ∧
        FiveToSixCuspEdge68 Ae Be ce d ee n g t at hsupported
      left
      rcases hsupported with ⟨t, ht, _hts, htr, ht60, hd, he, hcuspT⟩
      exact ⟨t, hnBig, hn60, hg60, ht60, ht, htr, hd, he, hcuspT⟩
    · exact Or.inr hterminalCusp

/-- Feed a supported earlier cusp simultaneously into the exact contraction
and the independently verified singular second-jet recurrence. -/
theorem integratedPolynomialLowerSystem68_fiveToSix_supported_secondJet68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hsupported :
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
      FiveToSixSupportedEarlierCusp68 Ae Be ce d ee n g) :
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
    FiveToSixContractedEarlierSecondJetAssembly68
      alpha gamma epsilon zeta eta terminal
      A B (cubicCDefectPolynomial68 A C0)
      (secondaryDDefectPolynomial68 A B D)
      (cubicEDefectPolynomial68 A C0 E)
      Ae Be ce d ee n g := by
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
  change FiveToSixSupportedEarlierCusp68 Ae Be ce d ee n g at hsupported
  rcases hsupported with
    ⟨s, hnBig, hn60, hg60, hs60, hs, hsr, hdSharp, heSharp, hcusp⟩
  have hinventory := integratedPolynomialLowerSystem68_global_terminalLoad_inventory
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change FiveToSixGlobalResidual68 zeta Ae Be ce De ee d n g ∧ _ at hinventory
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n :=
    ⟨hinventory.1.1, hinventory.1.2.1⟩
  have hresult :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_uniformCusp_resultant68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E s
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
      hs
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsr)
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using
          (⟨hdSharp, heSharp⟩ :
            d.natDegree ≤ 5 * n - g - s ∧
              ee.natDegree ≤ 6 * n - g - s))
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d,
          FiveToSixCuspEdge68] using hcusp)
  change 60 ∣ n ∧ 60 ∣ g ∧ 60 ∣ s ∧ 120 ≤ n ∧
    s + 60 ≤ 7 * n - 2 * g ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hresult
  rcases hresult with
    ⟨_hn60, _hg60, _hs60, _hn120, _hload2, hface, _hwall,
      hcompat, _hdeep, _hfirst⟩
  obtain ⟨N, hN⟩ := hn60
  obtain ⟨G, hG⟩ := hg60
  obtain ⟨S, hS⟩ := hs60
  have hpacket :=
    integratedPolynomialLowerSystem68_fiveToSix_contract_cusp68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys N G S
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using ⟨hN, hG⟩)
      (by
        rw [hS] at hcusp
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hcusp)
  have hdexpand : d = expand k 60 du := by
    simpa only [d, Ae, Be, De, du] using
      secondaryDDefectPolynomial68_expand 60 A B D
  have heexpand : ee = expand k 60 eu := by
    simpa only [ee, Ae, Ce, Ee, eu] using
      expand_cubicEDefectPolynomial68 60 A C0 E
  have hdContracted : du.natDegree ≤ 5 * N - G - S := by
    have h : (expand k 60 du).natDegree ≤ 5 * n - g - s := by
      rw [← hdexpand]
      exact hdSharp
    rw [natDegree_expand, hN, hG, hS] at h
    omega
  have heContracted : eu.natDegree ≤ 6 * N - G - S := by
    have h : (expand k 60 eu).natDegree ≤ 6 * n - g - s := by
      rw [← heexpand]
      exact heSharp
    rw [natDegree_expand, hN, hG, hS] at h
    omega
  exact ⟨s, N, G, S, hN, hG, hS, by omega, by omega, by omega,
    hdContracted, heContracted, hpacket, hface, hcompat⟩

/-- Full source assembly: terminal zero, supported/contracted earlier cusp
with its singular second jet, or the separate terminal all-nonzero cusp. -/
theorem integratedPolynomialLowerSystem68_fiveToSix_support_secondJet_assembly68
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
      FiveToSixContractedEarlierSecondJetAssembly68
        alpha gamma epsilon zeta eta terminal
        A B (cubicCDefectPolynomial68 A C0)
        (secondaryDDefectPolynomial68 A B D)
        (cubicEDefectPolynomial68 A C0 E)
        Ae Be ce d ee n g ∨
      (120 < n ∧ 60 ∣ n ∧ 60 ∣ g ∧
        d.natDegree ≤ g - 2 * n ∧ ee.natDegree ≤ g - n ∧ zeta = 0 ∧
        FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g)) := by
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
  have hsupported :=
    integratedPolynomialLowerSystem68_fiveToSix_supported_consumer68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change FiveToSixTerminalZeroPacket68 zeta d ee n g ∨
    FiveToSixSupportedLargeCuspResidual68 zeta Ae Be ce d ee n g at hsupported
  rcases hsupported with hzero | hearlier | hterminalCusp
  · exact Or.inl hzero
  · right; left
    exact integratedPolynomialLowerSystem68_fiveToSix_supported_secondJet68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hearlier)
  · right; right
    exact hterminalCusp

#print axioms integratedPolynomialLowerSystem68_fiveToSix_leastCusp_support68
#print axioms integratedPolynomialLowerSystem68_fiveToSix_supported_consumer68
#print axioms integratedPolynomialLowerSystem68_fiveToSix_supported_secondJet68
#print axioms integratedPolynomialLowerSystem68_fiveToSix_support_secondJet_assembly68

end FiveToSixLargeCuspSupportAssembly68

end Max11DegreeRoutes
