import Sol68LaterDeepLowerOpenMiddleAboveFiveReductionScratch

/-! # Closing the two asymmetric seven walls above the five-sum wall

The two residual walls share the same row-two initial-form argument.  On
`3g=7n` with `2h<7n`, the derivative of `d*e` is uniquely highest.  On
`2h=7n` with `3g<7n`, the fixed discriminant face is uniquely highest.
The already forced equality `delta=0` removes the only possible higher load.
Both edge faces are nonzero, so the entire above-five chamber is impossible.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleAboveFiveSevenWallsClosure68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 6000000 in
theorem laterDeepFiveSumReducedRowTwo_rightSevenBelow_DE_impossible68
    (gamma epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 7 * n) (hbelow : 2 * h < 7 * n)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (he0 : e.coeff (6 * n - h) ≠ 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hrow : laterDeepFiveSumReducedRowTwoPolynomial68
      gamma 0 epsilon zeta i4 A B c d e = 0) : False := by
  let idx := 11 * n - 2 * h - 1
  have hdecoeff := fiveRadiusRowTwoDE68_coeff d e n h hn (by omega) hd he
  have hdeNe : ((8 / 3 : k) • derivative (d * e)).coeff idx ≠ 0 := by
    dsimp [idx]
    rw [hdecoeff]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num)
          (Nat.cast_ne_zero.mpr (by omega))) hd0) he0
  have hfixed : (fiveRadiusRowTwoFixedCore68 A B c).natDegree < idx := by
    have hb := fiveRadiusRowTwoFixedCore68_degree_le_of_laterDeepLowerOpen
      A B c n g hn hg hopen hA hB hc
    dsimp [idx]
    omega
  have htail : (fiveRadiusRowTwoTail68 gamma epsilon i4 A B c d).natDegree < idx := by
    have hBd : (derivative (B ^ 2 * d)).natDegree < idx := by
      have hp : (B ^ 2 * d).natDegree ≤
          (6 * n - 2 * g) + (5 * n - h) := by
        compute_degree
        omega
      have hder := natDegree_derivative_le (B ^ 2 * d)
      dsimp [idx]
      omega
    have hAd : (derivative A).natDegree < idx := by
      dsimp [idx]
      compute_degree
      omega
    have hBc : (derivative (B * c)).natDegree < idx := by
      have hp : (B * c).natDegree ≤
          (3 * n - g) + (4 * n - g) := by
        compute_degree
        omega
      have hder := natDegree_derivative_le (B * c)
      dsimp [idx]
      omega
    have hdd : (derivative d).natDegree < idx := by
      dsimp [idx]
      compute_degree
      omega
    have h1 := deepGap_natDegree_smul_lt68 (-8 / 9 : k) hBd
    have h2 := deepGap_natDegree_smul_lt68 (1 / 6 * i4 : k) hAd
    have h3 := deepGap_natDegree_smul_lt68 (4 / 3 * gamma : k) hBc
    have h4 := deepGap_natDegree_smul_lt68 (2 * epsilon : k) hdd
    simp only [fiveRadiusRowTwoTail68]
    exact deepGap_natDegree_add_lt
      (deepGap_natDegree_sub_lt (deepGap_natDegree_sub_lt h1 h2) h3) h4
  have hz : (zeta • derivative ((1 / 4 : k) • A ^ 2 + c)).natDegree < idx := by
    have hp : ((1 / 4 : k) • A ^ 2 + c).natDegree ≤ 4 * n := by
      compute_degree
      omega
    have hder := natDegree_derivative_le ((1 / 4 : k) • A ^ 2 + c)
    apply (natDegree_smul_le _ _).trans_lt
    dsimp [idx]
    omega
  have hzrow := congrArg (fun p : k[X] => p.coeff idx) hrow
  rw [laterDeepFiveSumReducedRowTwoPolynomial68, zero_smul, add_zero,
    fiveRadiusReducedRowTwoPolynomial68_faceSplit,
    coeff_add, coeff_add, coeff_add,
    coeff_eq_zero_of_natDegree_lt hfixed,
    coeff_eq_zero_of_natDegree_lt htail,
    coeff_eq_zero_of_natDegree_lt hz,
    coeff_zero] at hzrow
  simp only [zero_add, add_zero] at hzrow
  exact hdeNe hzrow

set_option maxHeartbeats 6000000 in
theorem laterDeepFiveSumReducedRowTwo_leftSevenBelow_fixed_impossible68
    (gamma epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 2 * h = 7 * n) (hbelow : 3 * g < 7 * n)
    (ha : A.coeff (2 * n) ≠ 0) (hb : B.coeff (3 * n - g) ≠ 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hrow : laterDeepFiveSumReducedRowTwoPolynomial68
      gamma 0 epsilon zeta i4 A B c d e = 0) : False := by
  let idx := 11 * n - 3 * g - 1
  have hfixed := fiveRadiusRowTwoFixedCore68_coeff_of_laterDeepLowerOpen
    A B c n g hn hg hopen hA hB hc hdisc
  have hfixedNe : (fiveRadiusRowTwoFixedCore68 A B c).coeff idx ≠ 0 := by
    dsimp [idx]
    rw [hfixed]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num)
          (Nat.cast_ne_zero.mpr (by omega))) ha)
      (pow_ne_zero 3 hb)
  have hde : ((8 / 3 : k) • derivative (d * e)).natDegree < idx := by
    have hp : (d * e).natDegree ≤
        (5 * n - h) + (6 * n - h) := by
      compute_degree
      omega
    have hder := natDegree_derivative_le (d * e)
    apply (natDegree_smul_le _ _).trans_lt
    dsimp [idx]
    omega
  have htail : (fiveRadiusRowTwoTail68 gamma epsilon i4 A B c d).natDegree < idx := by
    have hBd : (derivative (B ^ 2 * d)).natDegree < idx := by
      have hp : (B ^ 2 * d).natDegree ≤
          (6 * n - 2 * g) + (5 * n - h) := by
        compute_degree
        omega
      have hder := natDegree_derivative_le (B ^ 2 * d)
      dsimp [idx]
      omega
    have hAd : (derivative A).natDegree < idx := by
      dsimp [idx]
      compute_degree
      omega
    have hBc : (derivative (B * c)).natDegree < idx := by
      have hp : (B * c).natDegree ≤
          (3 * n - g) + (4 * n - g) := by
        compute_degree
        omega
      have hder := natDegree_derivative_le (B * c)
      dsimp [idx]
      omega
    have hdd : (derivative d).natDegree < idx := by
      dsimp [idx]
      compute_degree
      omega
    have h1 := deepGap_natDegree_smul_lt68 (-8 / 9 : k) hBd
    have h2 := deepGap_natDegree_smul_lt68 (1 / 6 * i4 : k) hAd
    have h3 := deepGap_natDegree_smul_lt68 (4 / 3 * gamma : k) hBc
    have h4 := deepGap_natDegree_smul_lt68 (2 * epsilon : k) hdd
    simp only [fiveRadiusRowTwoTail68]
    exact deepGap_natDegree_add_lt
      (deepGap_natDegree_sub_lt (deepGap_natDegree_sub_lt h1 h2) h3) h4
  have hz : (zeta • derivative ((1 / 4 : k) • A ^ 2 + c)).natDegree < idx := by
    have hp : ((1 / 4 : k) • A ^ 2 + c).natDegree ≤ 4 * n := by
      compute_degree
      omega
    have hder := natDegree_derivative_le ((1 / 4 : k) • A ^ 2 + c)
    apply (natDegree_smul_le _ _).trans_lt
    dsimp [idx]
    omega
  have hzrow := congrArg (fun p : k[X] => p.coeff idx) hrow
  rw [laterDeepFiveSumReducedRowTwoPolynomial68, zero_smul, add_zero,
    fiveRadiusReducedRowTwoPolynomial68_faceSplit,
    coeff_add, coeff_add, coeff_add,
    coeff_eq_zero_of_natDegree_lt hde,
    coeff_eq_zero_of_natDegree_lt htail,
    coeff_eq_zero_of_natDegree_lt hz,
    coeff_zero] at hzrow
  simp only [add_zero] at hzrow
  exact hfixedNe hzrow

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleAboveFive_impossible68
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
      5 * n < g + h) : False := by
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
  have reduced :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleAboveFive_reduced68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using habove)
  change h < 2 * g ∧ delta = 0 ∧ zeta ≠ 0 ∧
      5 * n < 2 * h ∧ 5 * n < 3 * g ∧ g + h < 7 * n ∧
      Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
      d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
        3 * ce.coeff (4 * n - g) ^ 2 = 0 ∧
      ((2 * h = 7 * n ∧ 3 * g < 7 * n) ∨
        (3 * g = 7 * n ∧ 2 * h < 7 * n)) at reduced
  rcases reduced with
    ⟨hmiddle, hdelta, hzeta, hHhigh, hGhigh, hsum7,
      hb0, hc0, hd0, he0, hdisc, residual⟩
  have selected :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
        using hmiddle)
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
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  have hi4c : cubicFirstIntegralFourPolynomial68
      0 0 gamma delta epsilon zeta Ae Be ce
        ((1 / 3 : k) • (Ae * Be) + d) ee = C i4 := by
    have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i4 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralFourPolynomial68_of_eq
          l beta gamma delta epsilon zeta i4 A B C0 D E hi4
    rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
      hDrec, selected.1, selected.2.1] at hi4e
    exact hi4e
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
  have hrow := polynomialSecondaryResidualRowTwo68
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee hrowTwo
  rw [selected.1, selected.2.1] at hrow
  have hred := laterDeepFiveSumReducedRowTwoPolynomial68_eq_zero
    alpha gamma delta epsilon zeta eta i4 Ae Be ce d ee hi4c hrow
  rw [hdelta] at hred
  rcases residual with hleft | hright
  · exact laterDeepFiveSumReducedRowTwo_leftSevenBelow_fixed_impossible68
      gamma epsilon zeta i4 Ae Be ce d ee n g h hn hg hopen hleft.1 hleft.2
      ha hb0 hA secondary.2.1 secondary.2.2.1
      selected.2.2.2.1 selected.2.2.2.2.1 hdisc hred
  · exact laterDeepFiveSumReducedRowTwo_rightSevenBelow_DE_impossible68
      gamma epsilon zeta i4 Ae Be ce d ee n g h hn hg hopen hright.1 hright.2
      hd0 he0 hA secondary.2.1 secondary.2.2.1
      selected.2.2.2.1 selected.2.2.2.2.1 hred

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddle_forces_belowFive68
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
    g + h < 5 * n := by
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
  have selector :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddle_offWall_selector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
  change g + h < 5 * n ∨ (5 * n < g + h ∧ _) at selector
  rcases selector with hbelow | habove
  · exact hbelow
  · exact False.elim
      (maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleAboveFive_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h]
          using habove.1))

#print axioms laterDeepFiveSumReducedRowTwo_rightSevenBelow_DE_impossible68
#print axioms laterDeepFiveSumReducedRowTwo_leftSevenBelow_fixed_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleAboveFive_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddle_forces_belowFive68

end LaterDeepLowerOpenMiddleAboveFiveSevenWallsClosure68

end Max11DegreeRoutes
