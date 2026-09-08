import Sol68FiveToSixLargeCuspSupportAssemblyScratch
import Fable68FiveToSixLargeTerminalZeroConsumerScratch

/-! # Unified source inventory for the large five-to-six H0 family

The supported-cusp assembly and terminal-zero successor use the same
deterministic expanded coordinates.  This file strengthens the terminal-zero
limb in place while preserving the contracted singular cusp and terminal
all-nonzero cusp exactly.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixHZeroInventory68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 12000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Unified exact residual: the terminal-zero limb remembers its conditional
beyond-wall successor; the supported singular cusp retains its contraction
and second-jet compatibility; the terminal all-nonzero cusp is unchanged. -/
def FiveToSixHZeroSourceInventory68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B C0 D E Ae Be ce d ee : k[X]) (n g : ℕ) : Prop :=
  (FiveToSixTerminalZeroPacket68 zeta d ee n g ∧
      (120 < n → 60 ∣ n → 60 ∣ g →
        FiveToSixLargeTerminalZeroSuccessor68 zeta Ae Be ce d ee n g)) ∨
    FiveToSixContractedEarlierSecondJetAssembly68
      alpha gamma epsilon zeta eta terminal
      A B (cubicCDefectPolynomial68 A C0)
      (secondaryDDefectPolynomial68 A B D)
      (cubicEDefectPolynomial68 A C0 E)
      Ae Be ce d ee n g ∨
    (120 < n ∧ 60 ∣ n ∧ 60 ∣ g ∧
      d.natDegree ≤ g - 2 * n ∧ ee.natDegree ≤ g - n ∧ zeta = 0 ∧
      FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g))

/-- Source-honest unified H0 inventory.  No branch is reselected: all
expanded coordinates are the canonical `expand 60` outputs from `hsys`. -/
theorem integratedPolynomialLowerSystem68_fiveToSix_HZero_inventory68
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
    FiveToSixHZeroSourceInventory68 alpha gamma epsilon zeta eta terminal
      A B C0 D E Ae Be ce d ee n g := by
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
  have hbase :=
    integratedPolynomialLowerSystem68_fiveToSix_support_secondJet_assembly68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change FiveToSixTerminalZeroPacket68 zeta d ee n g ∨
      FiveToSixContractedEarlierSecondJetAssembly68
        alpha gamma epsilon zeta eta terminal
        A B (cubicCDefectPolynomial68 A C0)
        (secondaryDDefectPolynomial68 A B D)
        (cubicEDefectPolynomial68 A C0 E)
        Ae Be ce d ee n g ∨
      (120 < n ∧ 60 ∣ n ∧ 60 ∣ g ∧
        d.natDegree ≤ g - 2 * n ∧ ee.natDegree ≤ g - n ∧ zeta = 0 ∧
        FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g)) at hbase
  change FiveToSixHZeroSourceInventory68 alpha gamma epsilon zeta eta
    terminal A B C0 D E Ae Be ce d ee n g
  rcases hbase with hzero | hsingular | hterminalCusp
  · left
    refine ⟨hzero, fun hbig hn60 hg60 => ?_⟩
    have hstep :=
      maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_largeAligned_beyondWallEdge68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n] using hbig)
        (by simpa only [n] using hn60)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hg60)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hzero)
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hstep
  · exact Or.inr (Or.inl hsingular)
  · exact Or.inr (Or.inr hterminalCusp)

end FiveToSixHZeroInventory68

end Max11DegreeRoutes
