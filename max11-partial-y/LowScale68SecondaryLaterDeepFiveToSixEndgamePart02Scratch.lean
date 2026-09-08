import LowScale68SecondaryLaterDeepFiveToSixEndgamePart01Scratch

/-! # The remaining later-deep five-to-six window

The two invariant faces are already available.  Here the terminal lower row
is shown to retain its ordinary first-secondary scalar throughout
`5n < 2g ≤ 6n`, despite the deeper load chamber.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveToSix68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 14000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 18000000 in
/-- Sharp source-level classification supplied by I4, I3, and the terminal
row in `5n < 2g ≤ 6n`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_topClassification68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
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
      5 * n < 2 * g ∧ 2 * g ≤ 6 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    let a := Ae.coeff (2 * n)
    let b := Be.coeff (3 * n - g)
    let c := ce.coeff (4 * n - g)
    let d := De.coeff (5 * n - g)
    let e := ee.coeff (6 * n - g)
    (e = 0 ∧ a * b = 3 * d) ∨
      (e = 0 ∧ c = 0 ∧ a * b = d) ∨
      (b = 0 ∧ c = 0 ∧ d = 0) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let a := Ae.coeff (2 * n)
  let b := Be.coeff (3 * n - g)
  let c := ce.coeff (4 * n - g)
  let d := De.coeff (5 * n - g)
  let e := ee.coeff (6 * n - g)
  change 5 * n < 2 * g ∧ 2 * g ≤ 6 * n at hwindow
  change (e = 0 ∧ a * b = 3 * d) ∨
    (e = 0 ∧ c = 0 ∧ a * b = d) ∨
    (b = 0 ∧ c = 0 ∧ d = 0)
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hn : 0 < n := data.hn
  have hinv :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_invariantFaces68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change firstSecondaryFour68 a b c d e = 0 ∧
    firstSecondaryThree68 a b c d e = 0 at hinv
  have hgt3 : 3 * n < 2 * g := by omega
  have hlbeta :=
    maximalExpandedIntegratedPolynomialLowerSystem_l_beta_eq_zero_of_threeRadius_lt_twoGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgt3)
  have hl : l = 0 := hlbeta.1
  have hbeta : beta = 0 := hlbeta.2
  obtain ⟨i4, hI4raw⟩ := data.invariant
  have hI4 := hI4raw
  rw [hl, hbeta] at hI4
  have hdelta :=
    cubicFirstIntegralFourPolynomial68_forces_delta_eq_zero_of_l_beta
      gamma delta epsilon zeta i4 Ae Be ce De ee n g hn data.hg
      hwindow.1 data.hA data.hB data.hc data.hD data.he data.ha hI4
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using cubicEDefectPolynomial68_eq_cubicCoordinates
      Ae Ce Ee
  have hrowZero : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee =
      C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowZeroPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have hnTen : 10 ≤ n := by
    simpa only [n] using weightedRadius68_ge_ten A B C0 D E hn
  have hidx : 59 < 13 * n - 2 * g - 1 := by omega
  have hzeroCoeff :=
    expand_lowerRowZeroPolynomial68_coeff_eq_zero_of_index_gt
      terminal
      (integratedUPolynomial68 l alpha beta gamma delta zeta
        Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee (13 * n - 2 * g - 1) hrowZero hidx
  rw [hl, hbeta, hdelta, hCrec, hErec] at hzeroCoeff
  have hzero :=
    lowerRowZeroPolynomial68_fiveToSix_forces_firstSecondaryZero
      alpha gamma epsilon zeta eta Ae Be ce De ee n g hn hwindow
      data.hA data.ha data.hB data.hc data.hD data.he hzeroCoeff
  change firstSecondaryZero68 a b c d e = 0 at hzero
  exact firstSecondaryFourThreeZero68_classify
    a b c d e data.ha hinv.1 hinv.2 hzero

end LaterDeepFiveToSix68
end Max11DegreeRoutes
