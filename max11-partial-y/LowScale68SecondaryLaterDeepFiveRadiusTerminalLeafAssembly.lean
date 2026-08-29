import LowScale68SecondaryLaterDeepFiveRadiusTerminalLeafAlgebra

/-! # Source assembly for the strict terminal leaf on `2g = 5n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveRadiusTerminalLeafAssembly68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 48000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The strict terminal selector leaf is empty.  Thus the source-level
`2g=5n` cascade ends on the single equality wall `h=5n`, with at least one
of the two terminal coefficients attained. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusTerminalEquality68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      2 * g = 5 * n) :
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
    let h := secondaryResidualGap68 n d ee
    l = 0 ∧ beta = 0 ∧ delta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
      h = 5 * n ∧ (d.coeff 0 ≠ 0 ∨ ee.coeff n ≠ 0) := by
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
  let h := secondaryResidualGap68 n d ee
  have old :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusTerminalResiduals68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hwall
  change l = 0 ∧ beta = 0 ∧ delta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
      FiveRadiusTerminalSelector68 d ee n h at old
  refine ⟨old.1, old.2.1, old.2.2.1, old.2.2.2.1,
    old.2.2.2.2.1, old.2.2.2.2.2.1, old.2.2.2.2.2.2.1, ?_⟩
  rcases old.2.2.2.2.2.2.2.cases with heq | hstrict
  · exact heq
  · exfalso
    have core := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
    have drop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
    have secondary := maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
    change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧
      ce.natDegree ≤ 4 * n - g ∧ De.natDegree ≤ 5 * n - g ∧
      ee.natDegree ≤ 6 * n - g ∧ _ at secondary
    have hn : 0 < n := by simpa only [n] using core.1
    have ha : Ae.coeff (2 * n) ≠ 0 := by
      simpa only [n, Ae] using core.2.2.2.2.2
    have hA : Ae.natDegree ≤ 2 * n := by
      have hAe : Ae.natDegree = 2 * n := by
        simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
      omega
    have hwall' : 2 * g = 5 * n := by
      simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall
    have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
      simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
    have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
        (1 / 3 : k) • (Ae * ce) + ee := by
      simpa only [ce, ee] using
        cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
    have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
      simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
    obtain ⟨i4, hi4⟩ := hsys.firstFour
    have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i4 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralFourPolynomial68_of_eq
          l beta gamma delta epsilon zeta i4 A B C0 D E hi4
    have hi4c := hi4e
    rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
      hDrec, old.1, old.2.1, old.2.2.1] at hi4c
    obtain ⟨i3, hi3⟩ := hsys.firstThree
    have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i3 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralThreePolynomial68_of_eq
          l beta gamma delta epsilon zeta i3 A B C0 D E hi3
    have hi3c := hi3e
    rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
      hDrec, old.1, old.2.1, old.2.2.1] at hi3c
    have h1e : lowerRowOnePolynomial68
        (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
        (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          Ae Be Ce De Ee) Ce De Ee = 0 := by
      dsimp only [Ae, Be, Ce, De, Ee]
      rw [← expand_integratedTPolynomial68, ← expand_integratedUPolynomial68,
        ← expand_integratedVPolynomial68, lowerRowOnePolynomial68_expand,
        hsys.rowOne, map_zero, zero_mul]
    rw [hCrec, hDrec, hErec] at h1e
    have hrow := polynomialSecondaryResidualRowOne68
      l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee h1e
    rw [old.1, old.2.1, old.2.2.1] at hrow
    have hreduced := fiveRadiusReducedRowOnePolynomial68_eq_zero
      alpha gamma epsilon zeta eta i3 Ae Be ce d ee hi3c hrow
    have hd0 : d = 0 := hstrict.2.2.1
    rw [hd0] at hi4c hreduced
    have hi4strict : cubicFirstIntegralFourPolynomial68
        0 0 gamma 0 epsilon zeta Ae Be ce
          ((1 / 3 : k) • (Ae * Be)) ee = C i4 := by
      simpa only [add_zero] using hi4c
    exact fiveRadius_strictTerminal_impossible68
      gamma epsilon zeta i4 Ae Be ce ee n g h hn hwall'
      hstrict.1 hstrict.2.1 ha hA secondary.2.1 secondary.2.2.1
      old.2.2.2.2.2.1 old.2.2.2.2.2.2.1 hi4strict
      (by simpa only [add_zero] using hreduced)

#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepFiveRadiusTerminalEquality68

end LaterDeepFiveRadiusTerminalLeafAssembly68

end Max11DegreeRoutes
