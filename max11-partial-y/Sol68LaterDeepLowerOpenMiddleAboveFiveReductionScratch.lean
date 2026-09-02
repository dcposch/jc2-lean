import Sol68LaterDeepLowerOpenMiddleFiveSumZetaZeroClosureScratch
import LowScale68SecondaryLaterDeepLowerOpenMiddleHighLeftFiveRowZeroEndgame
import LowScale68SecondaryLaterDeepLowerOpenMiddleHighRightFiveRowZeroEndgame
import LowScale68SecondaryLaterDeepLowerOpenMiddleHighCoincidentSevenEndgame

/-! # Reduction of the strict above-five middle chamber

The branch `5n < g+h` immediately has `delta=0`.  The ordinary row-two and
row-one closures force both high inequalities strictly.  A simultaneous
`zeta=0` is impossible in the entire middle chamber.  The high zeta selector,
together with the balanced and strict/coincident seven-wall closures, leaves
exactly the two asymmetric seven walls.  The final source selector preserves
the untouched sibling `g+h<5n` verbatim.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleAboveFiveReduction68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleDeltaZetaZero_impossible68
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
    (hdelta : delta = 0) (hzeta : zeta = 0) : False := by
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
  have ordinary :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleOrdinary68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
        using hmiddle)
  change l = 0 ∧ beta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
      d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
        3 * ce.coeff (4 * n - g) ^ 2 = 0 at ordinary
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
    hDrec, ordinary.1, ordinary.2.1, hdelta, hzeta] at hi4c
  have hi3c := hi3e
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hDrec, ordinary.1, ordinary.2.1, hdelta, hzeta] at hi3c
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
  rw [ordinary.1, ordinary.2.1, hdelta, hzeta] at hrow2
  have hred : fiveRadiusReducedRowTwoPolynomial68
      gamma epsilon 0 i4 Ae Be ce d ee = 0 := by
    have ht := laterDeepFiveSumReducedRowTwoPolynomial68_eq_zero
      alpha gamma 0 epsilon 0 eta i4 Ae Be ce d ee hi4c hrow2
    simpa only [laterDeepFiveSumReducedRowTwoPolynomial68, zero_smul, add_zero]
      using ht
  rcases lt_trichotomy (2 * h) (3 * g) with hleft | hbalanced | hright
  · exact fiveRadiusReducedRowTwo_leftDE_impossible_of_delta_zeta_zero68
      gamma epsilon i4 Ae Be ce d ee n g h hn hg ordinary.2.2.1 hmiddle
      hopen hleft ordinary.2.2.2.2.2.2.2.1
      ordinary.2.2.2.2.2.2.2.2.1 hA hB hc hd he hred
  · have hload4 :=
      secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_delta_zeta_zero
        gamma epsilon Ae Be ce d ee n g h hn hmiddle hopen hB hd
    have face :=
      polynomialSecondaryResidualBetweenFace68_of_laterDeepLowerOpen_delta_zero
        gamma epsilon 0 i4 i3 Ae Be ce d ee n g h hn hg ordinary.2.2.1
        hmiddle hopen hload4 hA hB hc hd he hi4c hi3c
    have hrelation :=
      fiveRadiusReducedRowTwo_balanced_relation_of_delta_zeta_zero68
        gamma epsilon i4 Ae Be ce d ee n g h hn hg ordinary.2.2.1
        hmiddle hopen hbalanced hA hB hc hd he
        ordinary.2.2.2.2.2.2.2.2.2 hred
    have height : 3 * g < 8 * n := by omega
    have hI3 :=
      secondaryResidualInvariantThreePolynomial68_degree_le_six_sub_h_of_balanced_zeta_zero
        gamma epsilon i3 Ae Be ce d ee n g h hn ordinary.2.2.1
        hmiddle hopen hbalanced height hB hc he hi3c
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
    rw [ordinary.1, ordinary.2.1, hdelta, hzeta] at hrowOne
    have hload1 :=
      cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_balanced_zeta_zero
        alpha gamma epsilon eta Ae Be ce d ee n g h hn hg ordinary.2.2.1
        hmiddle hopen hbalanced height hA hB hc hd he
    have hcoeff := congrArg
      (fun p : k[X] => p.coeff (12 * n - 3 * g - 1)) hrowOne
    rw [coeff_add, coeff_zero, coeff_eq_zero_of_natDegree_lt hload1, add_zero]
      at hcoeff
    exact residualRowOne_balanced_coeff_ne_zero_of_high_zeta_zero68
      Ae Be ce d ee n g h hn hg ordinary.2.2.1 hmiddle hbalanced height
      hA hB hc hd he hI3 ordinary.2.2.2.2.2.2.1
      ordinary.2.2.2.2.2.2.2.2.2 face.four hrelation hcoeff
  · exact fiveRadiusReducedRowTwo_rightFixed_impossible_of_delta_zeta_zero68
      gamma epsilon i4 Ae Be ce d ee n g h hn hg ordinary.2.2.1 hmiddle
      hopen hright (by simpa only [n, Ae] using core.2.2.2.2.2)
      ordinary.2.2.2.2.2.1 hA hB hc hd he
      ordinary.2.2.2.2.2.2.2.2.2 hred

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddle_forces_strictHigh68
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
      h < 2 * g) :
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
    5 * n < 2 * h ∧ 5 * n < 3 * g := by
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
  have callLeft (hw : 2 * h < 3 * g ∧ 2 * h < 5 * n) : False :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleLeftImpossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hw)
  have callRight (hw : 3 * g < 2 * h ∧ 3 * g < 5 * n) : False :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleRightImpossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hw)
  have callBalanced (hw : 2 * h = 3 * g ∧ 3 * g < 5 * n) : False :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleBalancedBelowDelta_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hw)
  have callLeftFive (hw : 2 * h = 5 * n ∧ 5 * n < 3 * g) : False :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighLeftFive_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hw)
  have callRightFive (hw : 3 * g = 5 * n ∧ 5 * n < 2 * h) : False :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighRightFive_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hw)
  have callCoincident (hw : 2 * h = 5 * n ∧ 3 * g = 5 * n) : False :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighCoincidentFive_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hw)
  have hH : 5 * n < 2 * h := by
    rcases lt_trichotomy (2 * h) (5 * n) with hlow | hwall | hhigh
    · rcases lt_trichotomy (2 * h) (3 * g) with hl | hb | hr
      · exact False.elim (callLeft ⟨hl, hlow⟩)
      · exact False.elim (callBalanced ⟨hb, by omega⟩)
      · exact False.elim (callRight ⟨hr, by omega⟩)
    · rcases lt_trichotomy (3 * g) (5 * n) with hr | hc | hl
      · exact False.elim (callRight ⟨by omega, hr⟩)
      · exact False.elim (callCoincident ⟨hwall, hc⟩)
      · exact False.elim (callLeftFive ⟨hwall, hl⟩)
    · exact hhigh
  have hG : 5 * n < 3 * g := by
    rcases lt_trichotomy (3 * g) (5 * n) with hlow | hwall | hhigh
    · rcases lt_trichotomy (2 * h) (3 * g) with hl | hb | hr
      · exact False.elim (callLeft ⟨hl, by omega⟩)
      · exact False.elim (callBalanced ⟨hb, hlow⟩)
      · exact False.elim (callRight ⟨hr, hlow⟩)
    · rcases lt_trichotomy (2 * h) (5 * n) with hl | hc | hr
      · exact False.elim (callLeft ⟨by omega, hl⟩)
      · exact False.elim (callCoincident ⟨hc, hwall⟩)
      · exact False.elim (callRightFive ⟨hwall, hr⟩)
    · exact hhigh
  exact ⟨hH, hG⟩

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleAboveFive_reduced68
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
    (habove :
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
      5 * n < g + h) :
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
    h < 2 * g ∧ delta = 0 ∧ zeta ≠ 0 ∧
      5 * n < 2 * h ∧ 5 * n < 3 * g ∧ g + h < 7 * n ∧
      Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
      d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
        3 * ce.coeff (4 * n - g) ^ 2 = 0 ∧
      ((2 * h = 7 * n ∧ 3 * g < 7 * n) ∨
        (3 * g = 7 * n ∧ 2 * h < 7 * n)) := by
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
  change 5 * n < g + h at habove
  have hmiddle :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpen_forces_middle68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
  change h < 2 * g at hmiddle
  have hstrict :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddle_forces_strictHigh68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle)
  change 5 * n < 2 * h ∧ 5 * n < 3 * g at hstrict
  have above :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleAboveFiveSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using habove)
  change delta = 0 ∧ _ at above
  have hdelta : delta = 0 := above.1
  have hzeta : zeta ≠ 0 := by
    intro hz
    exact maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleDeltaZetaZero_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle)
      hdelta hz
  have ordinary :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleOrdinary68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle)
  change l = 0 ∧ beta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
      d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
        3 * ce.coeff (4 * n - g) ^ 2 = 0 at ordinary
  have zselector :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighStrict_zetaSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hstrict)
  change (2 * h = 3 * g ∧ 2 * h < 7 * n) ∨
      2 * h = 7 * n ∨ 3 * g = 7 * n ∨ zeta = 0 at zselector
  have walls : 2 * h = 7 * n ∨ 3 * g = 7 * n := by
    rcases zselector with hbalanced | hH | hG | hz
    · exact False.elim
        (maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighBalancedBelowSeven_impossible68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
          hterminal hsys
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle)
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
            using hstrict)
          (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
            using And.intro hbalanced.1 (by omega : 3 * g < 7 * n)))
    · exact Or.inl hH
    · exact Or.inr hG
    · exact False.elim (hzeta hz)
  have residual : (2 * h = 7 * n ∧ 3 * g < 7 * n) ∨
      (3 * g = 7 * n ∧ 2 * h < 7 * n) := by
    rcases walls with hH | hG
    · rcases lt_trichotomy (3 * g) (7 * n) with hlt | heq | hgt
      · exact Or.inl ⟨hH, hlt⟩
      · exact False.elim
          (maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighCoincidentSeven_impossible68
            l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
            hterminal hsys
            (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
            (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
              using hmiddle)
            (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
              using And.intro hH heq))
      · exact False.elim
          (maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighLeftSeven_impossible68
            l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
            hterminal hsys
            (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
            (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
              using hmiddle)
            (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
              using And.intro hH hgt))
    · rcases lt_trichotomy (2 * h) (7 * n) with hlt | heq | hgt
      · exact Or.inr ⟨hG, hlt⟩
      · exact False.elim
          (maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighCoincidentSeven_impossible68
            l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
            hterminal hsys
            (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
            (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
              using hmiddle)
            (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
              using And.intro heq hG))
      · exact False.elim
          (maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighRightSeven_impossible68
            l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
            hterminal hsys
            (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
            (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
              using hmiddle)
            (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
              using And.intro hG hgt))
  have hsum7 : g + h < 7 * n := by rcases residual with hr | hr <;> omega
  exact ⟨hmiddle, hdelta, hzeta, hstrict.1, hstrict.2, hsum7,
    ordinary.2.2.2.2.2.1, ordinary.2.2.2.2.2.2.1,
    ordinary.2.2.2.2.2.2.2.1, ordinary.2.2.2.2.2.2.2.2.1,
    ordinary.2.2.2.2.2.2.2.2.2, residual⟩

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddle_offWall_selector68
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
      3 * n < 2 * g ∧ 2 * g < 5 * n) :
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
    g + h < 5 * n ∨
      (5 * n < g + h ∧ h < 2 * g ∧ delta = 0 ∧ zeta ≠ 0 ∧
        5 * n < 2 * h ∧ 5 * n < 3 * g ∧ g + h < 7 * n ∧
        Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
        d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧
        Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
          3 * ce.coeff (4 * n - g) ^ 2 = 0 ∧
        ((2 * h = 7 * n ∧ 3 * g < 7 * n) ∨
          (3 * g = 7 * n ∧ 2 * h < 7 * n))) := by
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
  rcases lt_trichotomy (g + h) (5 * n) with hbelow | hwall | habove
  · exact Or.inl hbelow
  · exact False.elim
      (maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleFiveSum_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hwall))
  · have reduced :=
      maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleAboveFive_reduced68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using habove)
    exact Or.inr ⟨habove, reduced⟩

#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleDeltaZetaZero_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddle_forces_strictHigh68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleAboveFive_reduced68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddle_offWall_selector68

end LaterDeepLowerOpenMiddleAboveFiveReduction68

end Max11DegreeRoutes
