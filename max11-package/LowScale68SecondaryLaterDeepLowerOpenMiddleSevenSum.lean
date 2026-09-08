import LowScale68SecondaryLaterDeepLowerOpenMiddleSelector

/-! # The `zeta*A` wall on the strict lower later-deep middle residual -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleSevenSum68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_delta_zero_sum_lt_seven
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hsum : g + h < 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hd : d.natDegree ≤ 5 * n - h) :
    (secondaryLoadInvariantFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        9 * n - g - h := by
  rw [secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta_delta]
  compute_degree
  omega

theorem secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_delta_zeta_zero
    (gamma epsilon : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hd : d.natDegree ≤ 5 * n - h) :
    (secondaryLoadInvariantFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        9 * n - g - h := by
  rw [secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta_delta]
  simp only [zero_smul, zero_add]
  compute_degree
  omega

theorem secondaryLoadInvariantFourPolynomial68_coeff_twoRadius_of_delta_zero_seven_sum
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hsum : 7 * n ≤ g + h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hd : d.natDegree ≤ 5 * n - h) :
    (secondaryLoadInvariantFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (2 * n) =
        zeta * A.coeff (2 * n) := by
  have hBlt : B.natDegree < 2 * n := hB.trans_lt (by omega)
  have hdlt : d.natDegree < 2 * n := hd.trans_lt (by omega)
  rw [secondaryLoadInvariantFourPolynomial68_residualCoordinates_of_l_beta_delta]
  simp only [coeff_add, coeff_smul, smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hBlt,
    coeff_eq_zero_of_natDegree_lt hdlt]
  ring

theorem cubicFirstIntegralFourPolynomial68_forces_zeta_of_middle_sum_gt_seven
    (gamma epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hsum : 7 * n < g + h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (ha : A.coeff (2 * n) ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    zeta = 0 := by
  have hhom : (secondaryResidualInvariantFourPolynomial68 B c d e).natDegree <
      2 * n := by
    have hB3 : (B ^ 3).natDegree < 2 * n := by compute_degree; omega
    have hBe : (B * e).natDegree < 2 * n := by compute_degree; omega
    have hcd : (c * d).natDegree < 2 * n := by compute_degree; omega
    simp only [secondaryResidualInvariantFourPolynomial68]
    exact deepGap_natDegree_add_lt
      (deepGap_natDegree_add_lt
        (deepGap_natDegree_smul_lt68 (-8 / 27 : k) hB3)
        (deepGap_natDegree_smul_lt68 (8 / 3 : k) hBe))
      (deepGap_natDegree_smul_lt68 (8 / 3 : k) hcd)
  have hcoeff := congrArg (fun p : k[X] => p.coeff (2 * n)) hi4
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c
        ((1 / 3 : k) • (A * B) + d) e =
        secondaryResidualInvariantFourPolynomial68 B c d e from
      cubicFirstIntegralFourPolynomial68_residualCoordinates A B c d e,
    coeff_add, coeff_eq_zero_of_natDegree_lt hhom, zero_add,
    secondaryLoadInvariantFourPolynomial68_coeff_twoRadius_of_delta_zero_seven_sum
      gamma epsilon zeta A B c d e n g h hn hopen (le_of_lt hsum)
      hA hB hd] at hcoeff
  have hi : 2 * n ≠ 0 := by omega
  simp only [coeff_C, if_neg hi] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_right ha

theorem cubicFirstIntegralFourPolynomial68_middle_sevenSumWall_relation
    (gamma epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : g + h = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4) :
    (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - h) +
          c.coeff (4 * n - g) * d.coeff (5 * n - h)) +
      zeta * A.coeff (2 * n) = 0 := by
  have hi : 9 * n - g - h = 2 * n := by omega
  have hcoeff := congrArg (fun p : k[X] => p.coeff (9 * n - g - h)) hi4
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c
        ((1 / 3 : k) • (A * B) + d) e =
        secondaryResidualInvariantFourPolynomial68 B c d e from
      cubicFirstIntegralFourPolynomial68_residualCoordinates A B c d e,
    coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_middle_of_laterDeepLowerOpen
      B c d e n g h hn hg hgh hh hopen hB hc hd he, hi,
    secondaryLoadInvariantFourPolynomial68_coeff_twoRadius_of_delta_zero_seven_sum
      gamma epsilon zeta A B c d e n g h hn hopen (le_of_eq hwall.symm)
      hA hB hd] at hcoeff
  have hnz : 2 * n ≠ 0 := by omega
  simp only [coeff_C, if_neg hnz] at hcoeff
  simpa using hcoeff

theorem polynomialSecondaryResidualBetweenFace68_of_laterDeepLowerOpen_delta_zero
    (gamma epsilon zeta i4 i3 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hload :
      (secondaryLoadInvariantFourPolynomial68 0 0 gamma 0 epsilon zeta
        A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
          9 * n - g - h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    SecondaryResidualBetweenFace68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (e.coeff (6 * n - h)) := by
  constructor
  · have hz := congrArg (fun p : k[X] => p.coeff (9 * n - g - h)) hi4
    rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
      show cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c
          ((1 / 3 : k) • (A * B) + d) e =
          secondaryResidualInvariantFourPolynomial68 B c d e from
        cubicFirstIntegralFourPolynomial68_residualCoordinates A B c d e,
      coeff_add,
      secondaryResidualInvariantFourPolynomial68_coeff_middle_of_laterDeepLowerOpen
        B c d e n g h hn hg hgh hh hopen hB hc hd he,
      coeff_eq_zero_of_natDegree_lt hload, add_zero] at hz
    have hindex : 9 * n - g - h ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · have hthree := cubicFirstIntegralThreePolynomial68_residualMiddle_forces_face_of_laterDeepLowerOpen
      gamma 0 epsilon zeta i3 A B c d e n g h hn hg hgh hh hopen
      hA hB hc hd he hi3
    linear_combination hthree

set_option maxHeartbeats 24000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleAboveFiveSelector68
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
    delta = 0 ∧
      ((g + h < 7 * n ∧
          Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
          d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧
          Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
            3 * ce.coeff (4 * n - g) ^ 2 = 0) ∨
        (g + h = 7 * n ∧
          (-(Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
                d.coeff (5 * n - h)) +
              3 * ce.coeff (4 * n - g) * ee.coeff (6 * n - h) = 0) ∧
          (8 / 3 : k) *
                (Be.coeff (3 * n - g) * ee.coeff (6 * n - h) +
                  ce.coeff (4 * n - g) * d.coeff (5 * n - h)) +
              zeta * Ae.coeff (2 * n) = 0) ∨
        (7 * n < g + h ∧ zeta = 0 ∧
          Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
          d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧
          Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
            3 * ce.coeff (4 * n - g) ^ 2 = 0)) := by
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
  change 5 * n < g + h at habove
  have selected :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen) (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hmiddle)
  change l = 0 ∧ beta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
      (d.coeff (5 * n - h) ≠ 0 ∨ ee.coeff (6 * n - h) ≠ 0) ∧ _
    at selected
  have hdelta : delta = 0 := by
    rcases selected.2.2.2.2.2.2.2 with below | wall | above
    · exact False.elim ((not_lt_of_ge (le_of_lt habove)) below.1)
    · exact False.elim ((ne_of_gt habove) wall.1)
    · exact above.2.1
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
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4c : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta Ae Be ce
        ((1 / 3 : k) • (Ae * Be) + d) ee = C i4 := by
    have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i4 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralFourPolynomial68_of_eq
          l beta gamma delta epsilon zeta i4 A B C0 D E hi4
    rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
      hDrec, selected.1, selected.2.1, hdelta] at hi4e
    exact hi4e
  have hi3c : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon zeta Ae Be ce
        ((1 / 3 : k) • (Ae * Be) + d) ee = C i3 := by
    have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i3 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralThreePolynomial68_of_eq
          l beta gamma delta epsilon zeta i3 A B C0 D E hi3
    rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
      hDrec, selected.1, selected.2.1, hdelta] at hi3e
    exact hi3e
  refine ⟨hdelta, ?_⟩
  rcases lt_trichotomy (g + h) (7 * n) with hsum | hsum | hsum
  · left
    have hload :=
      secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_delta_zero_sum_lt_seven
        gamma epsilon zeta Ae Be ce d ee n g h hn hopen hsum hA
        secondary.2.1 selected.2.2.2.1
    have face :=
      polynomialSecondaryResidualBetweenFace68_of_laterDeepLowerOpen_delta_zero
        gamma epsilon zeta i4 i3 Ae Be ce d ee n g h hn hg selected.2.2.1
        hmiddle hopen hload hA secondary.2.1 secondary.2.2.1
        selected.2.2.2.1 selected.2.2.2.2.1 hi4c hi3c
    have classified := secondaryResidualBetweenFace68_classify_of_support
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (ee.coeff (6 * n - h)) ha selected.2.2.2.2.2.1
      selected.2.2.2.2.2.2.1 face
    exact ⟨hsum, classified.1, classified.2.1, classified.2.2.1,
      classified.2.2.2.1, classified.2.2.2.2⟩
  · right; left
    have three :=
      cubicFirstIntegralThreePolynomial68_residualMiddle_forces_face_of_laterDeepLowerOpen
        gamma 0 epsilon zeta i3 Ae Be ce d ee n g h hn hg selected.2.2.1
        hmiddle hopen hA secondary.2.1 secondary.2.2.1
        selected.2.2.2.1 selected.2.2.2.2.1 hi3c
    have four := cubicFirstIntegralFourPolynomial68_middle_sevenSumWall_relation
      gamma epsilon zeta i4 Ae Be ce d ee n g h hn hg selected.2.2.1
      hmiddle hopen hsum hA secondary.2.1 secondary.2.2.1
      selected.2.2.2.1 selected.2.2.2.2.1 hi4c
    exact ⟨hsum, three, four⟩
  · right; right
    have hzeta := cubicFirstIntegralFourPolynomial68_forces_zeta_of_middle_sum_gt_seven
      gamma epsilon zeta i4 Ae Be ce d ee n g h hn hmiddle hopen hsum
      hA secondary.2.1 secondary.2.2.1 selected.2.2.2.1
      selected.2.2.2.2.1 ha hi4c
    have hload :=
      secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_delta_zeta_zero
        gamma epsilon Ae Be ce d ee n g h hn hmiddle hopen secondary.2.1
        selected.2.2.2.1
    have hi4z := hi4c
    rw [hzeta] at hi4z
    have hi3z := hi3c
    rw [hzeta] at hi3z
    have face :=
      polynomialSecondaryResidualBetweenFace68_of_laterDeepLowerOpen_delta_zero
        gamma epsilon 0 i4 i3 Ae Be ce d ee n g h hn hg selected.2.2.1
        hmiddle hopen hload hA secondary.2.1 secondary.2.2.1
        selected.2.2.2.1 selected.2.2.2.2.1 hi4z hi3z
    have classified := secondaryResidualBetweenFace68_classify_of_support
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (ee.coeff (6 * n - h)) ha selected.2.2.2.2.2.1
      selected.2.2.2.2.2.2.1 face
    exact ⟨hsum, hzeta, classified.1, classified.2.1,
      classified.2.2.1, classified.2.2.2.1, classified.2.2.2.2⟩

#print axioms secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_delta_zero_sum_lt_seven
#print axioms secondaryLoadInvariantFourPolynomial68_coeff_twoRadius_of_delta_zero_seven_sum
#print axioms cubicFirstIntegralFourPolynomial68_forces_zeta_of_middle_sum_gt_seven
#print axioms cubicFirstIntegralFourPolynomial68_middle_sevenSumWall_relation
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleAboveFiveSelector68

end LaterDeepLowerOpenMiddleSevenSum68

end Max11DegreeRoutes
