import LowScale68SecondaryLaterDeepLowerOpenMiddleHighRightFiveWall

/-! # The coincident exact-five wall `2h = 3g = 5n`

All three degree-`6n-1` terms survive: the fixed `B,c` face, the `d*e`
face, and the `delta*A^3` load.  After the discriminant relation their exact
coefficient is the finite scalar packet

`15 * delta * a^3 - 64 * (4*b*c^2 - 9*d*e) = 0`.

Thus `delta = 0` is exactly the old balanced row-two relation; deleting that
subcase requires the balanced row-one obstruction.  This module records the
sharp source-facing packet without conflating it with that next step.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleHighCoincidentFiveWall68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 5000000 in
theorem fiveRadiusReducedRowTwoPolynomial68_coincidentFive_tail_degree_lt
    (gamma epsilon zeta i4 : k) (A B c d : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwallH : 2 * h = 5 * n) (hwallG : 3 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h) :
    (fiveRadiusRowTwoTail68 gamma epsilon i4 A B c d +
        zeta • derivative ((1 / 4 : k) • A ^ 2 + c)).natDegree <
      6 * n - 1 := by
  let idx := 6 * n - 1
  have htail :
      (fiveRadiusRowTwoTail68 gamma epsilon i4 A B c d).natDegree < idx := by
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
  have hz :
      (zeta • derivative ((1 / 4 : k) • A ^ 2 + c)).natDegree < idx := by
    have hp : ((1 / 4 : k) • A ^ 2 + c).natDegree ≤ 4 * n := by
      compute_degree
      omega
    have hder := natDegree_derivative_le ((1 / 4 : k) • A ^ 2 + c)
    apply (natDegree_smul_le _ _).trans_lt
    dsimp [idx]
    omega
  dsimp [idx] at htail hz ⊢
  exact deepGap_natDegree_add_lt htail hz

set_option maxHeartbeats 8000000 in
theorem laterDeepFiveSumReducedRowTwo_coincidentFive_relation68
    (gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hh : h < 2 * g)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwallH : 2 * h = 5 * n) (hwallG : 3 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hdisc : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0)
    (hrow : laterDeepFiveSumReducedRowTwoPolynomial68
      gamma delta epsilon zeta i4 A B c d e = 0) :
    (15 : k) * delta * A.coeff (2 * n) ^ 3 -
      (64 : k) * ((4 : k) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) ^ 2 -
        (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h)) = 0 := by
  let idx := 6 * n - 1
  have hfixed := fiveRadiusRowTwoFixedCore68_coeff_of_laterDeepLowerOpen
    A B c n g hn hg hopen hA hB hc hdisc
  have hde := fiveRadiusRowTwoDE68_coeff d e n h hn (by omega) hd he
  have hidxG : 11 * n - 3 * g - 1 = idx := by
    dsimp [idx]
    omega
  have hidxH : 11 * n - 2 * h - 1 = idx := by
    dsimp [idx]
    omega
  rw [hidxG] at hfixed
  rw [hidxH] at hde
  have htail := fiveRadiusReducedRowTwoPolynomial68_coincidentFive_tail_degree_lt
    gamma epsilon zeta i4 A B c d n g h hn hg hgh hh hopen hwallH hwallG
    hA hB hc hd
  have hdelta :=
    laterDeepFiveSumDeltaPrimitive68_derivative_coeff_sixRadius_of_highOrdinary
      A B c e n g h hn hg hgh hA hB hc he
  have hcoeff := congrArg (fun p : k[X] => p.coeff idx) hrow
  rw [laterDeepFiveSumReducedRowTwoPolynomial68, coeff_add,
    fiveRadiusReducedRowTwoPolynomial68_faceSplit] at hcoeff
  have htailCoeff :
      ((fiveRadiusRowTwoTail68 gamma epsilon i4 A B c d +
          zeta • derivative ((1 / 4 : k) • A ^ 2 + c)).coeff idx) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by simpa only [idx] using htail)
  have hgroup : fiveRadiusRowTwoFixedCore68 A B c +
        (8 / 3 : k) • derivative (d * e) +
        fiveRadiusRowTwoTail68 gamma epsilon i4 A B c d +
        zeta • derivative ((1 / 4 : k) • A ^ 2 + c) =
      fiveRadiusRowTwoFixedCore68 A B c +
        (8 / 3 : k) • derivative (d * e) +
        (fiveRadiusRowTwoTail68 gamma epsilon i4 A B c d +
          zeta • derivative ((1 / 4 : k) • A ^ 2 + c)) := by
    abel
  rw [hgroup, coeff_add, coeff_add, htailCoeff, add_zero, hfixed, hde,
    coeff_smul, smul_eq_mul] at hcoeff
  dsimp [idx] at hcoeff
  rw [hdelta] at hcoeff
  have hNG : 11 * n - 3 * g = 6 * n := by omega
  have hNH : 11 * n - 2 * h = 6 * n := by omega
  rw [hNG, hNH] at hcoeff
  push_cast at hcoeff
  have hnK : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hfactor : (n : k) *
      ((15 : k) * delta * A.coeff (2 * n) ^ 3 -
        (64 : k) * ((4 : k) * B.coeff (3 * n - g) *
          c.coeff (4 * n - g) ^ 2 -
          (9 : k) * d.coeff (5 * n - h) * e.coeff (6 * n - h))) = 0 := by
    linear_combination (36 : k) * hcoeff -
      (256 / 3 : k) * (n : k) * B.coeff (3 * n - g) * hdisc
  exact (mul_eq_zero.mp hfactor).resolve_left hnK

set_option maxHeartbeats 18000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighCoincidentFive_packet68
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
      2 * h = 5 * n ∧ 3 * g = 5 * n) :
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
    (15 : k) * delta * Ae.coeff (2 * n) ^ 3 -
      (64 : k) * ((4 : k) * Be.coeff (3 * n - g) *
        ce.coeff (4 * n - g) ^ 2 -
        (9 : k) * d.coeff (5 * n - h) * ee.coeff (6 * n - h)) = 0 := by
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
  exact laterDeepFiveSumReducedRowTwo_coincidentFive_relation68
    gamma delta epsilon zeta i4 Ae Be ce d ee n g h hn hg ordinary.2.2.1
    hmiddle hopen hwall.1 hwall.2 hA secondary.2.1 secondary.2.2.1
    ordinary.2.2.2.1 ordinary.2.2.2.2.1 ordinary.2.2.2.2.2.2.2.2.2
    hred

#print axioms fiveRadiusReducedRowTwoPolynomial68_coincidentFive_tail_degree_lt
#print axioms laterDeepFiveSumReducedRowTwo_coincidentFive_relation68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleHighCoincidentFive_packet68

end LaterDeepLowerOpenMiddleHighCoincidentFiveWall68

end Max11DegreeRoutes
