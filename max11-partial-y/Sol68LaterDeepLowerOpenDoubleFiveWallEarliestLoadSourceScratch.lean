import Sol68LaterDeepLowerOpenDoubleFiveWallEarliestLoadAlgebraScratch

/-! # Source closure of the first double-five lattice point -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleFiveWallEarliestLoadSource68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- At the first expanded lattice point on the exact double-five wall, the
epsilon/A equality load cancels, so the same invariant/row-one determinant
kills the two staggered offset-ninety defect edges. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateEarliestLoad68
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
    ce.coeff (4 * n - g - 90) = 0 ∧
      d.coeff (5 * n - 2 * g - 90) = 0 := by
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
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using core.2.2.2.2.2
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
  have hceexpand : ce = expand k 60 (cubicCDefectPolynomial68 A C0) := by
    simpa only [ce, Ae, Ce] using expand_cubicCDefectPolynomial68 60 A C0
  have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
    simp only [d, Ae, Be, De, secondaryDDefectPolynomial68,
      map_sub, expand_mul, Polynomial.smul_eq_C_mul, map_mul, expand_C]
  have hz30 :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateOffsetThirty68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdegenerate)
  change ce.coeff (4 * n - g - 30) = 0 ∧
      d.coeff (5 * n - 2 * g - 30) = 0 at hz30
  have hcbase : 30 ∣ 4 * n - g := by
    rw [hearly.1, hearly.2]
    norm_num
  have hdbaseDiv : 30 ∣ 5 * n - 2 * g := by
    rw [hearly.1, hearly.2]
    norm_num
  have hcStaggered : ¬60 ∣ 4 * n - g := by
    rw [hearly.1, hearly.2]
    norm_num
  have hdStaggered : ¬60 ∣ 5 * n - 2 * g := by
    rw [hearly.1, hearly.2]
    norm_num
  have hc30deg : ce.natDegree ≤ 4 * n - g - 30 := by
    rw [hceexpand]
    apply natDegree_expand_le_sub_thirty_of_boundary_zero68
      (cubicCDefectPolynomial68 A C0) (4 * n - g) hcbase (by omega)
    · simpa only [← hceexpand] using secondary.2.2.1
    · rw [← hceexpand]
      exact hdegenerate.1
  have hd30deg : d.natDegree ≤ 5 * n - 2 * g - 30 := by
    rw [hdexpand]
    apply natDegree_expand_le_sub_thirty_of_boundary_zero68
      (secondaryDDefectPolynomial68 A B D) (5 * n - 2 * g)
      hdbaseDiv (by omega)
    · simpa only [← hdexpand] using hd2
    · rw [← hdexpand]
      exact hdegenerate.2.2.1
  have hc90 : ce.natDegree ≤ 4 * n - g - 90 := by
    rw [hceexpand]
    apply natDegree_expand_le_sub_ninety_of_staggered_thirty_zero68
      (cubicCDefectPolynomial68 A C0) (4 * n - g) hcbase hcStaggered
      (by omega)
    · simpa only [← hceexpand] using hc30deg
    · rw [← hceexpand]
      exact hz30.1
  have hd90 : d.natDegree ≤ 5 * n - 2 * g - 90 := by
    rw [hdexpand]
    apply natDegree_expand_le_sub_ninety_of_staggered_thirty_zero68
      (secondaryDDefectPolynomial68 A B D) (5 * n - 2 * g)
      hdbaseDiv hdStaggered (by omega)
    · simpa only [← hdexpand] using hd30deg
    · rw [← hdexpand]
      exact hz30.2
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = Dtr := by
    simpa only [Dtr, d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have hD : Dtr.natDegree ≤ 5 * n - g := by
    rw [← hDrec]
    exact secondary.2.2.2.1
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
  have hcoeff3 := congrArg
    (fun p : k[X] => p.coeff (10 * n - 3 * g - 90)) hi3c
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit, coeff_add,
    cubicFirstIntegralThreePolynomial68_residualCoordinates,
    secondaryResidualInvariantThreePolynomial68_coeff_double_drop_ninety_of_fiveWall
      Ae Be ce d ee n g hn (by omega) hwall hA secondary.2.1 hc90 hd90 he2,
    coeff_eq_zero_of_natDegree_lt
      (secondaryLoadInvariantThreePolynomial68_degree_lt_offsetNinety_of_doubleFiveWall
        gamma delta epsilon zeta Ae Be ce Dtr ee n g hn (by omega) hwall
        hA secondary.2.1 secondary.2.2.1 hD he2), add_zero] at hcoeff3
  have hidx3 : 10 * n - 3 * g - 90 ≠ 0 := by omega
  simp only [coeff_C, if_neg hidx3] at hcoeff3
  have hi3scalar :
      -Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
          d.coeff (5 * n - 2 * g - 90) -
        Be.coeff (3 * n - g) ^ 2 * ce.coeff (4 * n - g - 90) +
        3 * ce.coeff (4 * n - g - 90) * ee.coeff (6 * n - 2 * g) = 0 := by
    have ht := (mul_eq_zero.mp hcoeff3).resolve_left (by norm_num)
    linear_combination ht
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedTPolynomial68, ← expand_integratedUPolynomial68,
      ← expand_integratedVPolynomial68, lowerRowOnePolynomial68_expand,
      hsys.rowOne, map_zero, zero_mul]
  have hrowPoly : secondaryResidualRowOnePolynomial68 Ae Be ce d ee +
      cubicLoadRowOnePolynomial68 0 alpha 0 gamma delta epsilon zeta eta
        Ae Be ce Dtr ee = 0 := by
    have hr := h1e
    rw [hCrec, hDrec, hErec, drops.1, drops.2.1] at hr
    exact polynomialSecondaryResidualRowOne68
      0 alpha 0 gamma delta epsilon zeta eta Ae Be ce d ee hr
  have hloadOne :
      (cubicLoadRowOnePolynomial68 0 alpha 0 gamma delta epsilon zeta eta
        Ae Be ce Dtr ee).natDegree < 12 * n - 3 * g - 91 := by
    have ht := cubicLoadRowOnePolynomial68_degree_lt_earliest_doubleFiveWall
      alpha gamma delta epsilon zeta eta Ae Be ce Dtr ee
      (by omega) (by omega) (by omega) (by omega) (by omega)
    omega
  have hcoeffOne := congrArg
    (fun p : k[X] => p.coeff (12 * n - 3 * g - 91)) hrowPoly
  rw [coeff_add, coeff_zero, coeff_eq_zero_of_natDegree_lt hloadOne, add_zero,
    secondaryResidualRowOnePolynomial68_coeff_double_drop_ninety_of_fiveWall
      Ae Be ce d ee n g hn (by omega) hwall hA secondary.2.1 hc90 hd90 he2]
    at hcoeffOne
  have hrowScalar :
      2 * Ae.coeff (2 * n) ^ 2 * Be.coeff (3 * n - g) *
          d.coeff (5 * n - 2 * g - 90) * (5 * (n : k) - 90) -
        6 * Ae.coeff (2 * n) * ce.coeff (4 * n - g - 90) *
          ee.coeff (6 * n - 2 * g) * (5 * (n : k) - 90) -
        4 * (n : k) * Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 *
          ce.coeff (4 * n - g - 90) = 0 := by
    have ht := (mul_eq_zero.mp hcoeffOne).resolve_left (by norm_num)
    have hcastM : (((5 * n - 90 : ℕ) : k)) = 5 * (n : k) - 90 := by
      rw [Nat.cast_sub (by omega : 90 ≤ 5 * n)]
      push_cast
      rfl
    rw [hcastM] at ht
    exact ht
  exact laterDeepLowerOpenDoubleFiveWall_degenerate_offsetNinety_edges_zero68
    n (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g - 90)) (d.coeff (5 * n - 2 * g - 90))
    (ee.coeff (6 * n - 2 * g)) hn ha hdegenerate.2.1 hi3scalar hrowScalar

#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateEarliestLoad68

end LaterDeepLowerOpenDoubleFiveWallEarliestLoadSource68

end Max11DegreeRoutes
