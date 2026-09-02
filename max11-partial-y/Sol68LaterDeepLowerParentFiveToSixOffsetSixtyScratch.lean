import Sol68LaterDeepLowerParentFiveToSixStrideReductionScratch

/-! # The offset-sixty load in the five-to-six chamber

At offset `60`, the quartic target `9n-2g-60` can meet an old load only
when it equals the top `A` weight `2n`.  The expansion divisibilities and
the five-to-six inequalities make this the unique wall `n=60, g=180`.
There the exact residual equation carries the load `zeta*a`.  Above the
wall, I4 and I3 give the usual load-free residual face, hence either both
new edges vanish or all four directions are nonzero on the discriminant.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetSixty68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Homogeneous I4 at offset `60`. -/
theorem secondaryResidualInvariantFourPolynomial68_coeff_gap_sixty_fiveToSix
    (B c d e : k[X]) (n g : ℕ) (hn60 : 60 ≤ n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 60)
    (he : e.natDegree ≤ 6 * n - g - 60) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
        (9 * n - 2 * g - 60) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - g - 60) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g - 60)) := by
  have hB3 : (B ^ 3).natDegree < 9 * n - 2 * g - 60 := by
    compute_degree
    omega
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g)
    (6 * n - g - 60) hB he
  have hBei : (3 * n - g) + (6 * n - g - 60) =
      9 * n - 2 * g - 60 := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g)
    (5 * n - g - 60) hc hd
  have hcdi : (4 * n - g) + (5 * n - g - 60) =
      9 * n - 2 * g - 60 := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3, hBe, hcd]
  ring

/-- Exact I4 coefficient at offset `60`.  The `zeta*A` term is retained:
it is the unique possible old-weight load at this target. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_gap_sixty_loaded_fiveToSix
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hn60 : 60 ≤ n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 60)
    (he : e.natDegree ≤ 6 * n - g - 60) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (9 * n - 2 * g - 60) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - g - 60) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g - 60)) +
        zeta * A.coeff (9 * n - 2 * g - 60) := by
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates,
    coeff_add, coeff_add, coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_gap_sixty_fiveToSix
      B c d e n g hn60 hwindow hB hc hd he]
  have hloadB : ((2 * epsilon : k) • B).natDegree <
      9 * n - 2 * g - 60 := by
    compute_degree
    omega
  have hloadd : ((4 * gamma : k) • d).natDegree <
      9 * n - 2 * g - 60 := by
    compute_degree
    omega
  rw [coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadd]
  simp only [coeff_smul, smul_eq_mul]
  ring

/-- Homogeneous I3 at offset `60`. -/
theorem secondaryResidualInvariantThreePolynomial68_coeff_gap_sixty_fiveToSix
    (A B c d e : k[X])
    (n g : ℕ) (hn60 : 60 ≤ n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 60)
    (he : e.natDegree ≤ 6 * n - g - 60) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (10 * n - 2 * g - 60) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - g - 60)) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - g - 60)) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n)
    (3 * n - g) (5 * n - g - 60) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (5 * n - g - 60) =
      10 * n - 2 * g - 60 := by omega
  rw [hABdi] at hABd
  have hB2c : (B ^ 2 * c).natDegree < 10 * n - 2 * g - 60 := by
    compute_degree
    omega
  have hce := coeff_mul_at_bounds68 c e (4 * n - g)
    (6 * n - g - 60) hc he
  have hcei : (4 * n - g) + (6 * n - g - 60) =
      10 * n - 2 * g - 60 := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 10 * n - 2 * g - 60 := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd,
    coeff_eq_zero_of_natDegree_lt hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

/-- I3 remains load-free at offset `60`, including on the I4 load wall. -/
theorem cubicFirstIntegralThreePolynomial68_coeff_gap_sixty_fiveToSix
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hn60 : 60 ≤ n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - 60)
    (he : e.natDegree ≤ 6 * n - g - 60) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (10 * n - 2 * g - 60) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - g - 60)) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - g - 60)) := by
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates,
    coeff_sub, coeff_add, coeff_add, coeff_add,
    secondaryResidualInvariantThreePolynomial68_coeff_gap_sixty_fiveToSix
      A B c d e n g hn60 hwindow hA hB hc hd he]
  have hloadB : (zeta • B).natDegree < 10 * n - 2 * g - 60 := by
    compute_degree
    omega
  have hloadc : ((2 * epsilon : k) • c).natDegree <
      10 * n - 2 * g - 60 := by
    compute_degree
    omega
  have hloade : ((4 * gamma : k) • e).natDegree <
      10 * n - 2 * g - 60 := by
    compute_degree
    omega
  have hloadB2 : ((2 / 3 * gamma : k) • B ^ 2).natDegree <
      10 * n - 2 * g - 60 := by
    compute_degree
    omega
  rw [coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadc,
    coeff_eq_zero_of_natDegree_lt hloade,
    coeff_eq_zero_of_natDegree_lt hloadB2]
  ring

set_option maxHeartbeats 30000000 in
/-- Exact source-facing offset-`60` classification.  The sole old-load wall
is `(n,g)=(60,180)` and retains `zeta*a` in I4.  Above it, the new edge pair
either vanishes or is the honest nonzero discriminant packet. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_offsetSixtyPacket68
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
    (n = 60 ∧ g = 180 ∧
      (8 / 3 : k) *
          (Be.coeff (3 * n - g) * ee.coeff (6 * n - g - 60) +
            ce.coeff (4 * n - g) * d.coeff (5 * n - g - 60)) +
        zeta * Ae.coeff (2 * n) = 0 ∧
      -(Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
          d.coeff (5 * n - g - 60)) +
        3 * ce.coeff (4 * n - g) * ee.coeff (6 * n - g - 60) = 0) ∨
    (60 < n ∧
      ((d.coeff (5 * n - g - 60) = 0 ∧
          ee.coeff (6 * n - g - 60) = 0) ∨
        (Be.coeff (3 * n - g) ≠ 0 ∧
          ce.coeff (4 * n - g) ≠ 0 ∧
          d.coeff (5 * n - g - 60) ≠ 0 ∧
          ee.coeff (6 * n - g - 60) ≠ 0 ∧
          Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
            3 * ce.coeff (4 * n - g) ^ 2 = 0))) := by
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
  change (_ ∧ _ ∧ _ ∧ _) ∨ (60 < n ∧ ((_ ∧ _) ∨
    (_ ∧ _ ∧ _ ∧ _ ∧ _)))
  have hparent :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_forces_fiveToSixStride68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlater)
  change 5 * n < 2 * g ∧ 2 * g ≤ 6 * n ∧ _ = 0 ∧ _ = 0 ∧
    30 ∣ n ∧ 30 ∣ g ∧ 30 < n ∧ _ ∧
    d.natDegree ≤ 5 * n - g - 60 ∧
    ee.natDegree ≤ 6 * n - g - 60 at hparent
  obtain ⟨hgt5, hle6, _hfour, _hthree, hn30, hg30, hnBig,
    _hprevious, hd, he⟩ := hparent
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n := ⟨hgt5, hle6⟩
  have hn60 : 60 ≤ n := by
    obtain ⟨u, hu⟩ := hn30
    omega
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hgt3 : 3 * n < 2 * g := by omega
  have hlbeta :=
    maximalExpandedIntegratedPolynomialLowerSystem_l_beta_eq_zero_of_threeRadius_lt_twoGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgt3)
  have hl : l = 0 := hlbeta.1
  have hbeta : beta = 0 := hlbeta.2
  obtain ⟨i4, hI4raw⟩ := data.invariant
  have hI4 := hI4raw
  rw [hl, hbeta] at hI4
  have hdelta :=
    cubicFirstIntegralFourPolynomial68_forces_delta_eq_zero_of_l_beta
      gamma delta epsilon zeta i4 Ae Be ce De ee n g data.hn data.hg
      hwindow.1 data.hA data.hB data.hc data.hD data.he data.ha hI4
  rw [hdelta] at hI4
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  rw [hDrec] at hI4
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  obtain ⟨i3, hi3raw⟩ := hsys.firstThree
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3raw
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hl, hbeta, hdelta, hDrec] at hi3e
  have hmain :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_mainFamily68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) at hmain
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧
    ce.natDegree ≤ 4 * n - g ∧ De.natDegree ≤ 5 * n - g ∧
    ee.natDegree ≤ 6 * n - g ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0 ∨
      De.coeff (5 * n - g) ≠ 0 ∨ ee.coeff (6 * n - g) ≠ 0)
      at hsecondary
  have hold := firstSecondary_mainFamily_attainment_split68
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
    (ee.coeff (6 * n - g)) data.ha hmain hsecondary.2.2.2.2.2
  have hcoeff3 := congrArg
    (fun p : k[X] => p.coeff (10 * n - 2 * g - 60)) hi3e
  rw [cubicFirstIntegralThreePolynomial68_coeff_gap_sixty_fiveToSix
    gamma epsilon zeta Ae Be ce d ee n g hn60 hwindow data.hA data.hB
    data.hc hd he] at hcoeff3
  have hj3 : 10 * n - 2 * g - 60 ≠ 0 := by omega
  simp only [coeff_C, if_neg hj3] at hcoeff3
  have hthree :
      -(Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
          d.coeff (5 * n - g - 60)) +
        3 * ce.coeff (4 * n - g) * ee.coeff (6 * n - g - 60) = 0 := by
    exact (mul_eq_zero.mp hcoeff3).resolve_left (by norm_num)
  by_cases hnwall : n = 60
  · left
    have hgwall : g = 180 := by
      obtain ⟨v, hv⟩ := hg30
      omega
    have hcoeff4 := congrArg
      (fun p : k[X] => p.coeff (9 * n - 2 * g - 60)) hI4
    rw [cubicFirstIntegralFourPolynomial68_coeff_gap_sixty_loaded_fiveToSix
      gamma epsilon zeta Ae Be ce d ee n g hn60 hwindow data.hA data.hB
      data.hc hd he] at hcoeff4
    have hj4 : 9 * n - 2 * g - 60 ≠ 0 := by omega
    simp only [coeff_C, if_neg hj4] at hcoeff4
    have htarget : 9 * n - 2 * g - 60 = 2 * n := by omega
    rw [htarget] at hcoeff4
    exact ⟨hnwall, hgwall, hcoeff4, hthree⟩
  · right
    have hnAbove : 60 < n := by omega
    have hcoeff4 := congrArg
      (fun p : k[X] => p.coeff (9 * n - 2 * g - 60)) hI4
    rw [cubicFirstIntegralFourPolynomial68_coeff_gap_sixty_loaded_fiveToSix
      gamma epsilon zeta Ae Be ce d ee n g hn60 hwindow data.hA data.hB
      data.hc hd he] at hcoeff4
    have hj4 : 9 * n - 2 * g - 60 ≠ 0 := by omega
    simp only [coeff_C, if_neg hj4] at hcoeff4
    have hAload : Ae.coeff (9 * n - 2 * g - 60) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have htarget : 2 * n < 9 * n - 2 * g - 60 := by omega
      exact lt_of_le_of_lt data.hA htarget
    rw [hAload, mul_zero, add_zero] at hcoeff4
    have hfour :
        Be.coeff (3 * n - g) * ee.coeff (6 * n - g - 60) +
          ce.coeff (4 * n - g) * d.coeff (5 * n - g - 60) = 0 := by
      exact (mul_eq_zero.mp hcoeff4).resolve_left (by norm_num)
    have hthree' :
        -Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
            d.coeff (5 * n - g - 60) +
          3 * ce.coeff (4 * n - g) * ee.coeff (6 * n - g - 60) = 0 := by
      linear_combination hthree
    have hface : SecondaryResidualBetweenFace68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (d.coeff (5 * n - g - 60))
        (ee.coeff (6 * n - g - 60)) := ⟨hfour, hthree'⟩
    exact ⟨hnAbove,
      firstSecondary_mainFamily_gapSucc_classify68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) (d.coeff (5 * n - g - 60))
        (ee.coeff (6 * n - g - 60)) data.ha hold hface⟩

#print axioms secondaryResidualInvariantFourPolynomial68_coeff_gap_sixty_fiveToSix
#print axioms cubicFirstIntegralFourPolynomial68_coeff_gap_sixty_loaded_fiveToSix
#print axioms secondaryResidualInvariantThreePolynomial68_coeff_gap_sixty_fiveToSix
#print axioms cubicFirstIntegralThreePolynomial68_coeff_gap_sixty_fiveToSix
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_offsetSixtyPacket68

end LaterDeepLowerParentFiveToSixOffsetSixty68

end Max11DegreeRoutes
