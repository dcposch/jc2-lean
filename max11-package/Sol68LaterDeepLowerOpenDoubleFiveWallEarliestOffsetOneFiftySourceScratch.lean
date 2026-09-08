import Sol68LaterDeepLowerOpenDoubleFiveWallEarliestOffsetOneFiftyAlgebraScratch

/-! # Source packet at the earliest offset-one-fifty delta wall -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleFiveWallEarliestOffsetOneFiftySource68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateEarliestOffsetOneFifty68
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
    (hdouble :
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
      2 * g ≤ h)
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
      3 * g = 5 * n)
    (hdegenerate :
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
      ce.coeff (4 * n - g) = 0 ∧ Be.coeff (3 * n - g) ≠ 0 ∧
        d.coeff (5 * n - 2 * g) = 0 ∧ ee.coeff (6 * n - 2 * g) ≠ 0)
    (hearly :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n = 90 ∧ g = 150) :
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
    ce.natDegree ≤ 60 ∧ d.natDegree ≤ 0 ∧
      (8 / 9 : k) *
        (-(Ae.coeff 180 * Be.coeff 120 * d.coeff 0) -
          Be.coeff 120 ^ 2 * ce.coeff 60 +
          3 * ce.coeff 60 * ee.coeff 240) =
        (1 / 2 : k) * delta * Ae.coeff 180 * Be.coeff 120 := by
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
  let Dtr := (1 / 3 : k) • (Ae * Be) + d
  change 3 * n < 2 * g ∧ 2 * g < 5 * n at hopen
  change 2 * g ≤ h at hdouble
  change 3 * g = 5 * n at hwall
  change ce.coeff (4 * n - g) = 0 ∧ Be.coeff (3 * n - g) ≠ 0 ∧
      d.coeff (5 * n - 2 * g) = 0 ∧ ee.coeff (6 * n - 2 * g) ≠ 0
    at hdegenerate
  change n = 90 ∧ g = 150 at hearly
  have core := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have drop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have secondary := maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧ ce.natDegree ≤ 4 * n - g ∧
    De.natDegree ≤ 5 * n - g ∧ ee.natDegree ≤ 6 * n - g ∧ _ at secondary
  have hn : 0 < n := by simpa only [n] using core.1
  have hA : Ae.natDegree ≤ 2 * n := by
    have ht : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
    omega
  have drops :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenResidualDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
  change l = 0 ∧ beta = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) ∧
      d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧ g < h at drops
  have hdbase : d.natDegree < 5 * n := drops.2.2.2.2.1.trans (by omega)
  have hebase : ee.natDegree < 6 * n := drops.2.2.2.2.2.1.trans (by omega)
  have bounds := secondaryResidualGap68_degreeBounds n d ee hdbase hebase
  have selector :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change h = 2 * g ∧ _ at selector
  have hd2 : d.natDegree ≤ 5 * n - 2 * g := by
    have ht := bounds.1
    change d.natDegree ≤ 5 * n - h at ht
    rw [selector.1] at ht
    exact ht
  have he2 : ee.natDegree ≤ 6 * n - 2 * g := by
    have ht := bounds.2
    change ee.natDegree ≤ 6 * n - h at ht
    rw [selector.1] at ht
    exact ht
  have hz90raw :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateEarliestLoad68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdegenerate)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hearly)
  have hz90 : ce.coeff 120 = 0 ∧ d.coeff 60 = 0 := by
    change ce.coeff (4 * n - g - 90) = 0 ∧
      d.coeff (5 * n - 2 * g - 90) = 0 at hz90raw
    rw [hearly.1, hearly.2] at hz90raw
    norm_num at hz90raw ⊢
    exact hz90raw
  have hceexpand : ce = expand k 60 (cubicCDefectPolynomial68 A C0) := by
    simpa only [ce, Ae, Ce] using expand_cubicCDefectPolynomial68 60 A C0
  have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
    simp only [d, Ae, Be, De, secondaryDDefectPolynomial68,
      map_sub, expand_mul, Polynomial.smul_eq_C_mul, map_mul, expand_C]
  have hz30raw :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateOffsetThirty68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdegenerate)
  have hz30 : ce.coeff 180 = 0 ∧ d.coeff 120 = 0 := by
    change ce.coeff (4 * n - g - 30) = 0 ∧
      d.coeff (5 * n - 2 * g - 30) = 0 at hz30raw
    rw [hearly.1, hearly.2] at hz30raw
    norm_num at hz30raw ⊢
    exact hz30raw
  have hc180 : ce.natDegree ≤ 180 := by
    rw [hceexpand]
    apply natDegree_expand_le_sub_thirty_of_boundary_zero68
      (cubicCDefectPolynomial68 A C0) 210 (by norm_num) (by norm_num)
    · rw [← hceexpand]
      simpa [hearly.1, hearly.2] using secondary.2.2.1
    · rw [← hceexpand]
      simpa [hearly.1, hearly.2] using hdegenerate.1
  have hc120 : ce.natDegree ≤ 120 := by
    rw [hceexpand]
    apply natDegree_expand_le_sub_ninety_of_staggered_thirty_zero68
      (cubicCDefectPolynomial68 A C0) 210 (by norm_num) (by norm_num)
      (by norm_num)
    · simpa only [← hceexpand] using hc180
    · rw [← hceexpand]
      exact hz30.1
  have hd120 : d.natDegree ≤ 120 := by
    rw [hdexpand]
    apply natDegree_expand_le_sub_thirty_of_boundary_zero68
      (secondaryDDefectPolynomial68 A B D) 150 (by norm_num) (by norm_num)
    · rw [← hdexpand]
      simpa [hearly.1, hearly.2] using hd2
    · rw [← hdexpand]
      simpa [hearly.1, hearly.2] using hdegenerate.2.2.1
  have hd60 : d.natDegree ≤ 60 := by
    rw [hdexpand]
    apply natDegree_expand_le_sub_ninety_of_staggered_thirty_zero68
      (secondaryDDefectPolynomial68 A B D) 150 (by norm_num) (by norm_num)
      (by norm_num)
    · simpa only [← hdexpand] using hd120
    · rw [← hdexpand]
      exact hz30.2
  have hc60 : ce.natDegree ≤ 60 := by
    rw [hceexpand] at hc120 ⊢
    exact natDegree_expand_le_sixty_of_le_oneTwenty_coeff_oneTwenty_zero68
      (cubicCDefectPolynomial68 A C0) hc120 (by
        rw [← hceexpand]
        exact hz90.1)
  have hd0 : d.natDegree ≤ 0 := by
    rw [hdexpand] at hd60 ⊢
    exact natDegree_expand_le_zero_of_le_sixty_coeff_sixty_zero68
      (secondaryDDefectPolynomial68 A B D) hd60 (by
        rw [← hdexpand]
        exact hz90.2)
  refine ⟨hc60, hd0, ?_⟩
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = Dtr := by
    simpa only [Dtr, d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi3c : cubicFirstIntegralThreePolynomial68
      0 0 gamma delta epsilon zeta Ae Be ce Dtr ee = C i3 := by
    have hi3e : firstIntegralThreePolynomial68
        l beta gamma delta epsilon zeta Ae Be Ce De Ee = C i3 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralThreePolynomial68_of_eq
          l beta gamma delta epsilon zeta i3 A B C0 D E hi3
    rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
      hDrec, drops.1, drops.2.1] at hi3e
    exact hi3e
  have hcoeff := congrArg (fun p : k[X] => p.coeff 300) hi3c
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit, coeff_add,
    cubicFirstIntegralThreePolynomial68_residualCoordinates,
    secondaryResidualInvariantThreePolynomial68_coeff_earliest_offsetOneFifty
      Ae Be ce d ee (by omega) (by omega) hc60 hd0 (by omega),
    secondaryLoadInvariantThreePolynomial68_coeff_earliest_offsetOneFifty
      gamma delta epsilon zeta Ae Be ce d ee (by omega) (by omega)
      hc60 hd0 (by omega)] at hcoeff
  simp only [coeff_C, if_neg (by norm_num : 300 ≠ 0)] at hcoeff
  linear_combination hcoeff

#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateEarliestOffsetOneFifty68

end LaterDeepLowerOpenDoubleFiveWallEarliestOffsetOneFiftySource68

end Max11DegreeRoutes
