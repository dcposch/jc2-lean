import Sol68LaterDeepLowerParentFiveToSixOffsetOneTwentyOrdinaryClosureAssemblyScratch
import Sol68LaterDeepLowerParentFiveToSixOffsetNinetyScratch

/-! # Terminal-RHS adapter at the five-to-six parent

The normalized ordinary selector is stated with all three residual/load
rows equal to zero.  An `IntegratedPolynomialLowerSystem68` supplies exactly
that equation for rows two and one, but supplies `C terminal` for row zero.
This file records the precise source interface: every positive row-zero
coefficient vanishes, and the full row-zero polynomial vanishes if and only
if `terminal = 0`.  It then pairs this packet with the global offset-`90`
classification.  Thus no source coefficient used above degree zero is
missing; only the constant terminal RHS prevents direct application of the
existing full-polynomial-zero selector.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixTerminalRHSAdapter68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Exact normalized source data carried by a constant-terminal lower
system.  The last field identifies the sole mismatch with the existing
ordinary selector's full-polynomial-zero API. -/
def FiveToSixTerminalRHSAdapter68
    (alpha gamma epsilon zeta eta terminal : k)
    (A B c d e : k[X]) : Prop :=
  ∃ i4 i3 : k,
    cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
        A B c ((1 / 3 : k) • (A * B) + d) e = C i4 ∧
    cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
        A B c ((1 / 3 : k) • (A * B) + d) e = C i3 ∧
    secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e = C terminal ∧
    secondaryResidualRowOnePolynomial68 A B c d e +
        cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e = 0 ∧
    secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e = 0 ∧
    (∀ j, 0 < j →
      (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff j = 0) ∧
    ((secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e = 0) ↔ terminal = 0)

/-- Minimal coefficient adapter: an exact constant RHS kills every positive
coefficient, while polynomial zero is equivalent to zero terminal. -/
theorem fiveToSix_rowZero_terminalRHS_coeff_adapter68
    (alpha gamma epsilon zeta eta terminal : k) (A B c d e : k[X])
    (hrow : secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = C terminal) :
    (∀ j, 0 < j →
      (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff j = 0) ∧
    ((secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e = 0) ↔ terminal = 0) := by
  constructor
  · intro j hj
    have hcoeff := congrArg (fun p : k[X] => p.coeff j) hrow
    simpa [coeff_C, Nat.ne_of_gt hj] using hcoeff
  · constructor
    · intro hzero
      have hcoeff := congrArg (fun p : k[X] => p.coeff 0) hrow
      rw [hzero] at hcoeff
      simpa [coeff_C] using hcoeff.symm
    · intro ht
      rw [hrow, ht]
      simp

/-- Pull the exact first integrals and all three residual/load rows out of
an unexpanded lower system after the standard five-to-six parameter
vanishing. -/
theorem integratedPolynomialLowerSystem68_fiveToSix_terminalRHS_adapter68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X])
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hl : l = 0) (hbeta : beta = 0) (hdelta : delta = 0) :
    FiveToSixTerminalRHSAdapter68 alpha gamma epsilon zeta eta terminal
      A B (cubicCDefectPolynomial68 A C0)
      (secondaryDDefectPolynomial68 A B D)
      (cubicEDefectPolynomial68 A C0 E) := by
  let c := cubicCDefectPolynomial68 A C0
  let d := secondaryDDefectPolynomial68 A B D
  let e := cubicEDefectPolynomial68 A C0 E
  have hCrec : C0 = (1 / 3 : k) • A ^ 2 + c := by
    simpa only [c] using cubicCDefectPolynomial68_reconstruct A C0
  have hDrec : D = (1 / 3 : k) • (A * B) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct A B D
  have hErec : E = (1 / 27 : k) • A ^ 3 +
      (1 / 3 : k) • (A * c) + e := by
    simpa only [c, e] using
      cubicEDefectPolynomial68_eq_cubicCoordinates A C0 E
  obtain ⟨i4, hi4raw⟩ := hsys.firstFour
  obtain ⟨i3, hi3raw⟩ := hsys.firstThree
  have hi4 := hi4raw
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec, hl, hbeta, hdelta] at hi4
  have hi3 := hi3raw
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hDrec, hl, hbeta, hdelta] at hi3
  have hrow1 := integratedPolynomialLowerSystem68_residualRowOne
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E c d e
    hCrec hDrec hErec hsys
  rw [hl, hbeta, hdelta] at hrow1
  have hrow2 := integratedPolynomialLowerSystem68_residualRowTwo
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E c d e
    hCrec hDrec hErec hsys
  rw [hl, hbeta, hdelta] at hrow2
  have hrow0 := hsys.rowZero
  rw [hCrec, hDrec, hErec,
    cubicRowZeroPolynomial68_residualSplit, hl, hbeta, hdelta] at hrow0
  have hadapt := fiveToSix_rowZero_terminalRHS_coeff_adapter68
    alpha gamma epsilon zeta eta terminal A B c d e hrow0
  exact ⟨i4, i3, hi4, hi3, hrow0, hrow1, hrow2, hadapt.1, hadapt.2⟩

set_option maxHeartbeats 30000000 in
/-- Global offset-`90` packet paired with the exact terminal-safe normalized
source interface.  This is the furthest direct backwire possible without
replacing the ordinary selector's row-zero polynomial equality by its
positive-coefficient consequences. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_offsetNinety_with_terminalRHS68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hlater :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n ≤ 2 * g) :
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
    (((n = 60 ∧ g = 180 ∧ zeta = 0) ∨ 60 < n) ∧
      ((d.coeff (5 * n - g - 60) = 0 ∧
          ee.coeff (6 * n - g - 60) = 0 ∧
          d.natDegree ≤ 5 * n - g - 120 ∧
          ee.natDegree ≤ 6 * n - g - 120 ∧
          (n = 90 ∧ g = 270 → zeta = 0)) ∨
        (60 ∣ n ∧ 60 ∣ g ∧
          Be.coeff (3 * n - g) ≠ 0 ∧
          ce.coeff (4 * n - g) ≠ 0 ∧
          d.coeff (5 * n - g - 60) ≠ 0 ∧
          ee.coeff (6 * n - g - 60) ≠ 0 ∧
          Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
            3 * ce.coeff (4 * n - g) ^ 2 = 0 ∧
          d.coeff (5 * n - g - 90) = 0 ∧
          ee.coeff (6 * n - g - 90) = 0))) ∧
      FiveToSixTerminalRHSAdapter68 alpha gamma epsilon zeta eta terminal
        A B (cubicCDefectPolynomial68 A C0)
        (secondaryDDefectPolynomial68 A B D)
        (cubicEDefectPolynomial68 A C0 E) := by
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
  change 3 * n ≤ 2 * g at hlater
  change (((_ ∧ _ ∧ _) ∨ _) ∧
      ((_ ∧ _ ∧ _ ∧ _ ∧ _) ∨
        (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))) ∧ _
  have hoffset :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_offsetNinetyPacket68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlater)
  change (((_ ∧ _ ∧ _) ∨ _) ∧
      ((_ ∧ _ ∧ _ ∧ _ ∧ _) ∨
        (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))) at hoffset
  have hparent :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_forces_fiveToSixStride68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlater)
  change 5 * n < 2 * g ∧ 2 * g ≤ 6 * n ∧ _ at hparent
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n :=
    ⟨hparent.1, hparent.2.1⟩
  have hlbeta :=
    maximalExpandedIntegratedPolynomialLowerSystem_l_beta_eq_zero_of_threeRadius_lt_twoGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          (show 3 * n < 2 * g by omega))
  have hl : l = 0 := hlbeta.1
  have hbeta : beta = 0 := hlbeta.2
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  obtain ⟨i4, hI4raw⟩ := data.invariant
  have hI4 := hI4raw
  rw [hl, hbeta] at hI4
  have hdelta :=
    cubicFirstIntegralFourPolynomial68_forces_delta_eq_zero_of_l_beta
      gamma delta epsilon zeta i4 Ae Be ce De ee n g data.hn data.hg
      hwindow.1 data.hA data.hB data.hc data.hD data.he data.ha hI4
  have hadapter :=
    integratedPolynomialLowerSystem68_fiveToSix_terminalRHS_adapter68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
      hl hbeta hdelta
  exact ⟨hoffset, hadapter⟩

#print axioms fiveToSix_rowZero_terminalRHS_coeff_adapter68
#print axioms integratedPolynomialLowerSystem68_fiveToSix_terminalRHS_adapter68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_offsetNinety_with_terminalRHS68

end LaterDeepLowerParentFiveToSixTerminalRHSAdapter68

end Max11DegreeRoutes
