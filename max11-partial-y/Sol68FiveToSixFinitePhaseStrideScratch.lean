import Sol68FiveToSixTerminalLoadStrideScratch

/-! # Finite phase completion for the five-to-six stride

The three finite global radius packets either reach the symbolic terminal
load, or expose the already classified all-nonzero cusp.  For the remaining
large family we record the exact obstruction to a common `60`-phase: when
`n` is `30 mod 60`, the two expanded support boundaries cannot align at the
same offset.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixFinitePhaseStride68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def FiveToSixCuspEdge68 (A B c d e : k[X]) (n g s : ℕ) : Prop :=
  B.coeff (3 * n - g) ≠ 0 ∧
    c.coeff (4 * n - g) ≠ 0 ∧
    d.coeff (5 * n - g - s) ≠ 0 ∧
    e.coeff (6 * n - g - s) ≠ 0 ∧
    A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      3 * c.coeff (4 * n - g) ^ 2 = 0

def FiveToSixTerminalPacket68
    (zeta : k) (A B c d e : k[X]) (n g : ℕ) : Prop :=
  d.natDegree ≤ g - 2 * n ∧ e.natDegree ≤ g - n ∧ zeta = 0 ∧
    ((d.coeff (g - 2 * n) = 0 ∧ e.coeff (g - n) = 0) ∨
      FiveToSixCuspEdge68 A B c d e n g (7 * n - 2 * g))

/-- Two expanded boundaries separated by a non-`60`-divisible radius can
never lie on the same `60`-lattice phase. -/
theorem fiveToSix_no_simultaneous_expansion_phase68
    (n g s : ℕ) (hn : ¬ 60 ∣ n) (hgs : g + s ≤ 5 * n) :
    ¬ (60 ∣ 5 * n - g - s ∧ 60 ∣ 6 * n - g - s) := by
  rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  apply hn
  have hdiff : 6 * n - g - s = (5 * n - g - s) + n := by omega
  have huv : u ≤ v := by omega
  refine ⟨v - u, ?_⟩
  omega

/-- Source wrapper for a support pair which has reached the symbolic load. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_terminalPacket68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hnLower : 10 < weightedRadius68 A B C0 D E)
    (hwindow :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hdrop :
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
      d.natDegree ≤ g - 2 * n ∧ ee.natDegree ≤ g - n) :
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
    FiveToSixTerminalPacket68 zeta Ae Be ce d ee n g := by
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
  change 5 * n < 2 * g ∧ 2 * g ≤ 6 * n at hwindow
  change d.natDegree ≤ g - 2 * n ∧ ee.natDegree ≤ g - n at hdrop
  have hterminalFace :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_terminalLoad68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hnLower hwindow hdrop
  change zeta = 0 ∧
    ((d.coeff (g - 2 * n) = 0 ∧ ee.coeff (g - n) = 0) ∨
      (Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
        d.coeff (g - 2 * n) ≠ 0 ∧ ee.coeff (g - n) ≠ 0 ∧
        Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
          3 * ce.coeff (4 * n - g) ^ 2 = 0)) at hterminalFace
  refine ⟨hdrop.1, hdrop.2, hterminalFace.1, ?_⟩
  rcases hterminalFace.2 with hzero | hcusp
  · exact Or.inl hzero
  · right
    change FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g)
    have hdidx : 5 * n - g - (7 * n - 2 * g) = g - 2 * n := by omega
    have heidx : 6 * n - g - (7 * n - 2 * g) = g - n := by omega
    simpa only [FiveToSixCuspEdge68, hdidx, heidx] using hcusp

/-- Exact finite completion and the honest large-family phase obstruction. -/
theorem integratedPolynomialLowerSystem68_fiveToSix_finitePhase_or_large68
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
    (120 < n ∧ 30 ∣ n ∧ 30 ∣ g ∧
        (60 ∣ n ∨
          (n % 60 = 30 ∧ ∀ s, g + s ≤ 5 * n →
            ¬ (60 ∣ 5 * n - g - s ∧ 60 ∣ 6 * n - g - s)))) ∨
      (∃ s, 0 < s ∧ s < 7 * n - 2 * g ∧
        FiveToSixCuspEdge68 Ae Be ce d ee n g s) ∨
      FiveToSixTerminalPacket68 zeta Ae Be ce d ee n g := by
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
  have hinventory :=
    integratedPolynomialLowerSystem68_global_terminalLoad_inventory
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change FiveToSixGlobalResidual68 zeta Ae Be ce De ee d n g ∧
    ((n = 60 ∧ g = 180 ∧ 7 * n - 2 * g = 60) ∨
      (n = 90 ∧ g = 240 ∧ 7 * n - 2 * g = 150) ∨
      (n = 90 ∧ g = 270 ∧ 7 * n - 2 * g = 90) ∨ 120 < n) at hinventory
  rcases hinventory with ⟨hglobal, hcases⟩
  rcases hglobal with
    ⟨hgt5, hle6, hfour, hthree, hn30, hg30, hnLarge, hvanish,
      hd60, he60, hpost, hnot120, holdCases⟩
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n := ⟨hgt5, hle6⟩
  have hnLower : 10 < weightedRadius68 A B C0 D E := by
    change 10 < n
    omega
  rcases hcases with h60 | h90240 | h90270 | hbig
  · right; right
    rcases h60 with ⟨hn60, hg180, hr60⟩
    have hdropTerminal : d.natDegree ≤ g - 2 * n ∧
        ee.natDegree ≤ g - n := by
      constructor <;> omega
    apply maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_terminalPacket68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hnLower
    · simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow
    · simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdropTerminal
  · rcases h90240 with ⟨hn90, hg240, hr150⟩
    have hzero120 := hpost.2.resolve_right (fun hcusp => by
      have hdiv : 60 ∣ n := hcusp.1
      rw [hn90] at hdiv
      norm_num at hdiv)
    have hdrop120 : d.natDegree ≤ 5 * n - g - 120 ∧
        ee.natDegree ≤ 6 * n - g - 120 :=
      ⟨hzero120.2.2.1, hzero120.2.2.2.1⟩
    have hload120 : 120 < 7 * n - 2 * g := by omega
    have hedge :=
      maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_uniformEdge68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E 120
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
        (by norm_num)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hload120)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdrop120)
    change (d.coeff (5 * n - g - 120) = 0 ∧
        ee.coeff (6 * n - g - 120) = 0) ∨
      FiveToSixCuspEdge68 Ae Be ce d ee n g 120 at hedge
    rcases hedge with hedge | hcusp
    · right; right
      have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
        simpa only [d, Ae, Be, De] using secondaryDDefectPolynomial68_expand 60 A B D
      have heexpand : ee = expand k 60 (cubicEDefectPolynomial68 A C0 E) := by
        simpa only [ee, Ae, Ce, Ee] using expand_cubicEDefectPolynomial68 60 A C0 E
      have hdTerminal : d.natDegree ≤ g - 2 * n := by
        rw [hdexpand, natDegree_expand] at hdrop120 ⊢
        omega
      have heTerminal : ee.natDegree ≤ g - n := by
        rw [heexpand]
        have hnext := natDegree_expand_le_sub_next_sixty68
          (cubicEDefectPolynomial68 A C0 E) 300 120 (by norm_num)
          (by norm_num) (by simpa only [heexpand, hn90, hg240] using hdrop120.2)
          (by simpa only [heexpand, hn90, hg240] using hedge.2)
        exact hnext.trans (by omega)
      apply maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_terminalPacket68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys hnLower
      · simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow
      · simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using
          (⟨hdTerminal, heTerminal⟩ :
            d.natDegree ≤ g - 2 * n ∧ ee.natDegree ≤ g - n)
    · right; left
      exact ⟨120, by norm_num, by omega, hcusp⟩
  · right; right
    rcases h90270 with ⟨hn90, hg270, hr90⟩
    have hzero120 := hpost.2.resolve_right (fun hcusp => by
      have hdiv : 60 ∣ n := hcusp.1
      rw [hn90] at hdiv
      norm_num at hdiv)
    have hdropTerminal : d.natDegree ≤ g - 2 * n ∧
        ee.natDegree ≤ g - n := by
      constructor
      · exact hzero120.2.2.1.trans (by omega)
      · exact hzero120.2.2.2.1.trans (by omega)
    apply maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_terminalPacket68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hnLower
    · simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow
    · simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdropTerminal
  · left
    refine ⟨hbig, hn30, hg30, ?_⟩
    by_cases hn60 : 60 ∣ n
    · exact Or.inl hn60
    · right
      refine ⟨?_, ?_⟩
      · omega
      · intro s hs
        exact fiveToSix_no_simultaneous_expansion_phase68 n g s hn60 hs

#print axioms fiveToSix_no_simultaneous_expansion_phase68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_terminalPacket68
#print axioms integratedPolynomialLowerSystem68_fiveToSix_finitePhase_or_large68

end FiveToSixFinitePhaseStride68

end Max11DegreeRoutes
