import LowScale68SecondaryLaterDeepLowerOpenMiddleOrdinaryRight

/-! # The `d * e` row-two obstruction in the strict open middle packet -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleOrdinaryLeft68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 3000000 in
theorem fiveRadiusRowTwoFixedCore68_degree_le_of_laterDeepLowerOpen
    (A B c : k[X]) (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (fiveRadiusRowTwoFixedCore68 A B c).natDegree ≤
      11 * n - 3 * g - 1 := by
  have hB2 : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hdB : (derivative B).natDegree ≤ 3 * n - g - 1 :=
    (natDegree_derivative_le B).trans (by omega)
  have hAB2 := natDegree_mul_le_of_le hA hB2
  have h1 : (A * B ^ 2 * derivative B).natDegree ≤
      11 * n - 3 * g - 1 := by
    have hm := natDegree_mul_le_of_le hAB2 hdB
    omega
  have hB3 : (B ^ 3).natDegree ≤ 9 * n - 3 * g := by
    compute_degree
    omega
  have hdA : (derivative A).natDegree ≤ 2 * n - 1 :=
    (natDegree_derivative_le A).trans (by omega)
  have h2 : (derivative A * B ^ 3).natDegree ≤
      11 * n - 3 * g - 1 := by
    have hm := natDegree_mul_le_of_le hdA hB3
    omega
  have hc2 : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hBc : (B * c ^ 2).natDegree ≤ 11 * n - 3 * g := by
    have hm := natDegree_mul_le_of_le hB hc2
    omega
  have h3 : (derivative (B * c ^ 2)).natDegree ≤
      11 * n - 3 * g - 1 :=
    (natDegree_derivative_le _).trans (by omega)
  have h1s := (natDegree_smul_le (-2 : k) (A * B ^ 2 * derivative B)).trans h1
  have h2s := (natDegree_smul_le (-2 / 3 : k) (derivative A * B ^ 3)).trans h2
  have h3s := (natDegree_smul_le (6 : k) (derivative (B * c ^ 2))).trans h3
  have hadd1 := (natDegree_add_le
    ((-2 : k) • (A * B ^ 2 * derivative B))
    ((-2 / 3 : k) • (derivative A * B ^ 3))).trans (max_le h1s h2s)
  have hadd2 := (natDegree_add_le
    (((-2 : k) • (A * B ^ 2 * derivative B)) +
      (-2 / 3 : k) • (derivative A * B ^ 3))
    ((6 : k) • derivative (B * c ^ 2))).trans (max_le hadd1 h3s)
  simp only [fiveRadiusRowTwoFixedCore68]
  exact (natDegree_smul_le _ _).trans hadd2

set_option maxHeartbeats 5000000 in
theorem laterDeepFiveSumReducedRowTwo_leftDE_impossible68
    (gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hleft : 2 * h < 3 * g) (hdeltaBelow : 2 * h < 5 * n)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (he0 : e.coeff (6 * n - h) ≠ 0)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hrow : laterDeepFiveSumReducedRowTwoPolynomial68
      gamma delta epsilon zeta i4 A B c d e = 0) : False := by
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
  have hdelta :
      (delta • derivative (laterDeepFiveSumDeltaPrimitive68 A B c e)).natDegree < idx := by
    have hp : (laterDeepFiveSumDeltaPrimitive68 A B c e).natDegree ≤ 6 * n := by
      simp only [laterDeepFiveSumDeltaPrimitive68]
      compute_degree
      omega
    have hder := natDegree_derivative_le
      (laterDeepFiveSumDeltaPrimitive68 A B c e)
    apply (natDegree_smul_le _ _).trans_lt
    dsimp [idx]
    omega
  have hzrow := congrArg (fun p : k[X] => p.coeff idx) hrow
  rw [laterDeepFiveSumReducedRowTwoPolynomial68,
    fiveRadiusReducedRowTwoPolynomial68_faceSplit,
    coeff_add, coeff_add, coeff_add, coeff_add,
    coeff_eq_zero_of_natDegree_lt hfixed,
    coeff_eq_zero_of_natDegree_lt htail,
    coeff_eq_zero_of_natDegree_lt hz,
    coeff_eq_zero_of_natDegree_lt hdelta,
    coeff_zero] at hzrow
  simp only [zero_add, add_zero] at hzrow
  exact hdeNe hzrow

set_option maxHeartbeats 24000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleLeftImpossible68
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
    (hleft :
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
      2 * h < 3 * g ∧ 2 * h < 5 * n) : False := by
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
  change 2 * h < 3 * g ∧ 2 * h < 5 * n at hleft
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
      hDrec, ordinary.1, ordinary.2.1] at hi4e
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
  rw [ordinary.1, ordinary.2.1] at hrow
  have hred := laterDeepFiveSumReducedRowTwoPolynomial68_eq_zero
    alpha gamma delta epsilon zeta eta i4 Ae Be ce d ee hi4c hrow
  exact laterDeepFiveSumReducedRowTwo_leftDE_impossible68
    gamma delta epsilon zeta i4 Ae Be ce d ee n g h hn hg ordinary.2.2.1
    hmiddle hopen hleft.1 hleft.2 ordinary.2.2.2.2.2.2.2.1
    ordinary.2.2.2.2.2.2.2.2.1 hA secondary.2.1 secondary.2.2.1
    ordinary.2.2.2.1 ordinary.2.2.2.2.1 hred

#print axioms fiveRadiusRowTwoFixedCore68_degree_le_of_laterDeepLowerOpen
#print axioms laterDeepFiveSumReducedRowTwo_leftDE_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleLeftImpossible68

end LaterDeepLowerOpenMiddleOrdinaryLeft68

end Max11DegreeRoutes
