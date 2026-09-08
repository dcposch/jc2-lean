import Sol68LaterDeepLowerOpenMiddleFiveSumRightSevenClosureScratch
import LowScale68SecondaryLaterDeepLowerOpenMiddleHighZetaZeroEndgame

/-! # Closing the zeta-zero residual on the exact five-sum wall

The exact five-sum packet gives `delta=0`, four nonzero residual edges, and
the ordinary discriminant.  With `zeta=0`, reduced row two deletes the two
strict comparisons between `2h` and `3g`.  On their equality wall, I3 gives
the incidence relation and bounds its residual invariant; the independent
row-one coefficient is then nonzero while its load is strictly lower.  Thus
the balanced comparison is impossible as well, and the exact five-sum wall
has no surviving branch.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleFiveSumZetaZeroClosure68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleFiveSumZetaZero_impossible68
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
      g + h = 5 * n)
    (hzeta : zeta = 0) : False := by
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
  change g + h = 5 * n at hwall
  have reduced :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleFiveSum_reduced68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hwall)
  change h < 2 * g ∧ delta = 0 ∧
      Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
      d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
        3 * ce.coeff (4 * n - g) ^ 2 = 0 ∧ _ at reduced
  have selected :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
        using reduced.1)
  change l = 0 ∧ beta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧ _
    at selected
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
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using core.2.2.2.2.2
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := secondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := secondary.2.2.1
  have hd : d.natDegree ≤ 5 * n - h := selected.2.2.2.1
  have he : ee.natDegree ≤ 6 * n - h := selected.2.2.2.2.1
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
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
    hDrec, selected.1, selected.2.1, reduced.2.1, hzeta] at hi4c
  have hi3c := hi3e
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hDrec, selected.1, selected.2.1, reduced.2.1, hzeta] at hi3c
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
  rw [selected.1, selected.2.1, reduced.2.1, hzeta] at hrow2
  have hred : fiveRadiusReducedRowTwoPolynomial68
      gamma epsilon 0 i4 Ae Be ce d ee = 0 := by
    have ht := laterDeepFiveSumReducedRowTwoPolynomial68_eq_zero
      alpha gamma 0 epsilon 0 eta i4 Ae Be ce d ee hi4c hrow2
    simpa only [laterDeepFiveSumReducedRowTwoPolynomial68, zero_smul, add_zero]
      using ht
  rcases lt_trichotomy (2 * h) (3 * g) with hleft | hbalanced | hright
  · exact fiveRadiusReducedRowTwo_leftDE_impossible_of_delta_zeta_zero68
      gamma epsilon i4 Ae Be ce d ee n g h hn hg selected.2.2.1 reduced.1
      hopen hleft reduced.2.2.2.2.1 reduced.2.2.2.2.2.1
      hA hB hc hd he hred
  · have hload4 :=
      secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_delta_zeta_zero
        gamma epsilon Ae Be ce d ee n g h hn reduced.1 hopen hB hd
    have face :=
      polynomialSecondaryResidualBetweenFace68_of_laterDeepLowerOpen_delta_zero
        gamma epsilon 0 i4 i3 Ae Be ce d ee n g h hn hg selected.2.2.1
        reduced.1 hopen hload4 hA hB hc hd he hi4c hi3c
    have hrelation :=
      fiveRadiusReducedRowTwo_balanced_relation_of_delta_zeta_zero68
        gamma epsilon i4 Ae Be ce d ee n g h hn hg selected.2.2.1
        reduced.1 hopen hbalanced hA hB hc hd he
        reduced.2.2.2.2.2.2.1 hred
    have height : 3 * g < 8 * n := by omega
    have hI3 :=
      secondaryResidualInvariantThreePolynomial68_degree_le_six_sub_h_of_balanced_zeta_zero
        gamma epsilon i3 Ae Be ce d ee n g h hn selected.2.2.1
        reduced.1 hopen hbalanced height hB hc he hi3c
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
    rw [selected.1, selected.2.1, reduced.2.1, hzeta] at hrowOne
    have hload1 :=
      cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_balanced_zeta_zero
        alpha gamma epsilon eta Ae Be ce d ee n g h hn hg selected.2.2.1
        reduced.1 hopen hbalanced height hA hB hc hd he
    have hcoeff := congrArg
      (fun p : k[X] => p.coeff (12 * n - 3 * g - 1)) hrowOne
    rw [coeff_add, coeff_zero, coeff_eq_zero_of_natDegree_lt hload1, add_zero]
      at hcoeff
    exact residualRowOne_balanced_coeff_ne_zero_of_high_zeta_zero68
      Ae Be ce d ee n g h hn hg selected.2.2.1 reduced.1 hbalanced height
      hA hB hc hd he hI3 reduced.2.2.2.1 reduced.2.2.2.2.2.2.1
      face.four hrelation hcoeff
  · exact fiveRadiusReducedRowTwo_rightFixed_impossible_of_delta_zeta_zero68
      gamma epsilon i4 Ae Be ce d ee n g h hn hg selected.2.2.1 reduced.1
      hopen hright ha reduced.2.2.1 hA hB hc hd he
      reduced.2.2.2.2.2.2.1 hred

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleFiveSum_impossible68
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
      g + h = 5 * n) : False := by
  have hzeta :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleFiveSum_forces_zeta_zero68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hopen hwall
  exact
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleFiveSumZetaZero_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hopen hwall hzeta

#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleFiveSumZetaZero_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleFiveSum_impossible68

end LaterDeepLowerOpenMiddleFiveSumZetaZeroClosure68

end Max11DegreeRoutes
