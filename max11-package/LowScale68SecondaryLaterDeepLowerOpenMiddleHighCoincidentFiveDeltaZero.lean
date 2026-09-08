import LowScale68SecondaryLaterDeepLowerOpenMiddleHighCoincidentFiveWall

/-! # Deleting `delta = 0` on the coincident exact-five wall

At `2h = 3g = 5n`, setting `delta = 0` turns the exact row-two packet into
the balanced relation.  The balanced row-one coefficient is nonzero while
all constant-Jacobian loads lie below it, giving a contradiction.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleHighCoincidentFiveDeltaZero68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 26000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 24000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighCoincidentFive_forces_delta_ne_zero68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hopen :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hmiddle :
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
      h < 2 * g)
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
      let d := secondaryDDefectPolynomial68 Ae Be De
      let h := secondaryResidualGap68 n d ee
      2 * h = 5 * n ∧ 3 * g = 5 * n) : delta ≠ 0 := by
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
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change h < 2 * g at hmiddle
  change 2 * h = 5 * n ∧ 3 * g = 5 * n at hwall
  intro hdelta
  have hbalanced : 2 * h = 3 * g := by omega
  have hsix : 3 * g < 6 * n := by omega
  have ordinary :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleOrdinary68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle)
  change l = 0 ∧ beta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
      d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧ _
    at ordinary
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
  have hg : 0 < g := secondary.1
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := secondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := secondary.2.2.1
  have hd : d.natDegree ≤ 5 * n - h := ordinary.2.2.2.1
  have he : ee.natDegree ≤ 6 * n - h := ordinary.2.2.2.2.1
  have he' : ee.natDegree ≤ 6 * n - g := he.trans (by omega)
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have hD : ((1 / 3 : k) • (Ae * Be) + d).natDegree ≤ 5 * n - g := by
    compute_degree
    omega
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec, ordinary.1, ordinary.2.1, hdelta] at hi4c
  have hi3c := hi3e
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hDrec, ordinary.1, ordinary.2.1, hdelta] at hi3c
  have hsum : g + h < 5 * n := by omega
  have face :=
    polynomialSecondaryResidualBetweenFace68_of_laterDeepLowerOpen_sum_lt_five
      gamma 0 epsilon zeta i4 i3 Ae Be ce d ee n g h hn hg ordinary.2.2.1
      hmiddle hopen hsum hA hB hc hd he hi4c hi3c
  have hrowTwo : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowTwoPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hCrec, hDrec, hErec] at hrowTwo
  have hrow2 := polynomialSecondaryResidualRowTwo68
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee hrowTwo
  rw [ordinary.1, ordinary.2.1, hdelta] at hrow2
  have hred : fiveRadiusReducedRowTwoPolynomial68
      gamma epsilon zeta i4 Ae Be ce d ee = 0 := by
    have ht := laterDeepFiveSumReducedRowTwoPolynomial68_eq_zero
      alpha gamma 0 epsilon zeta eta i4 Ae Be ce d ee hi4c hrow2
    simpa only [laterDeepFiveSumReducedRowTwoPolynomial68, zero_smul, add_zero]
      using ht
  have hrelation :=
    fiveRadiusReducedRowTwo_balanced_relation_of_delta_zero_below_seven68
      gamma epsilon zeta i4 Ae Be ce d ee n g h hn hg ordinary.2.2.1
      hmiddle hopen hbalanced (by omega) hA hB hc hd he
      ordinary.2.2.2.2.2.2.2.2.2 hred
  have hI3 :=
    secondaryResidualInvariantThreePolynomial68_degree_le_sixRadius_of_laterDeepLowerOpen
      gamma 0 epsilon zeta i3 Ae Be ce d ee n g hn hopen hA hB hc
      (hd.trans (by omega)) he' hi3c
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedTPolynomial68, ← expand_integratedUPolynomial68,
      ← expand_integratedVPolynomial68, lowerRowOnePolynomial68_expand,
      hsys.rowOne, map_zero, zero_mul]
  have hrowOne : secondaryResidualRowOnePolynomial68 Ae Be ce d ee +
      cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + d) ee = 0 := by
    have hr := h1e
    rw [hCrec, hDrec, hErec] at hr
    exact polynomialSecondaryResidualRowOne68
      l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee hr
  rw [ordinary.1, ordinary.2.1, hdelta] at hrowOne
  have hload :=
    cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_highBalanced_below_six
      alpha gamma epsilon zeta eta Ae Be ce
      ((1 / 3 : k) • (Ae * Be) + d) ee n g hn hg hopen hsix
      hA hB hc hD he'
  have hcoeff := congrArg
    (fun p : k[X] => p.coeff (12 * n - 3 * g - 1)) hrowOne
  rw [coeff_add, coeff_zero, coeff_eq_zero_of_natDegree_lt hload, add_zero]
    at hcoeff
  exact residualRowOne_balanced_coeff_ne_zero_of_high_below_six68
    Ae Be ce d ee n g h hn hg ordinary.2.2.1 hmiddle hbalanced hsix
    hA hB hc hd he hI3 ordinary.2.2.2.2.2.2.1
    ordinary.2.2.2.2.2.2.2.2.2 face.four hrelation hcoeff

#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighCoincidentFive_forces_delta_ne_zero68

end LaterDeepLowerOpenMiddleHighCoincidentFiveDeltaZero68

end Max11DegreeRoutes
