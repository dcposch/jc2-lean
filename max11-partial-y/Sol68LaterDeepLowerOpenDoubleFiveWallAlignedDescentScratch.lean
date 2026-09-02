import Sol68LaterDeepLowerOpenDoubleFiveWallOffsetThirtySourceScratch

/-! # Two-stride descent on the aligned degenerate five wall -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleFiveWallAlignedDescent68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 30000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateAlignedDescent68
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
    (hcAlign :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      60 ∣ 4 * n - g)
    (hdAlign :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      60 ∣ 5 * n - 2 * g) :
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
    ce.natDegree ≤ 4 * n - g - 120 ∧
      d.natDegree ≤ 5 * n - 2 * g - 120 := by
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
  change 2 * g ≤ h at hdouble
  change 3 * g = 5 * n at hwall
  change ce.coeff (4 * n - g) = 0 ∧ Be.coeff (3 * n - g) ≠ 0 ∧
      d.coeff (5 * n - 2 * g) = 0 ∧ ee.coeff (6 * n - 2 * g) ≠ 0
    at hdegenerate
  change 60 ∣ 4 * n - g at hcAlign
  change 60 ∣ 5 * n - 2 * g at hdAlign
  have stride :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallStrideSelector68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hdouble)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change _ ∧
      ((ce.coeff (4 * n - g) = 0 ∧ Be.coeff (3 * n - g) ≠ 0 ∧
          d.coeff (5 * n - 2 * g) = 0 ∧ ee.coeff (6 * n - 2 * g) ≠ 0 ∧
          60 < g ∧
          ((¬60 ∣ 4 * n - g) ∨ (¬60 ∣ 5 * n - 2 * g) ∨
            (ce.coeff (4 * n - g - 60) = 0 ∧
              d.coeff (5 * n - 2 * g - 60) = 0))) ∨
        (ce.coeff (4 * n - g) ≠ 0 ∧ _)) at stride
  have hsixty : ce.coeff (4 * n - g - 60) = 0 ∧
      d.coeff (5 * n - 2 * g - 60) = 0 := by
    rcases stride.2 with hdeg | hnondeg
    · rcases hdeg.2.2.2.2.2 with hcNot | hdNot | hz
      · exact False.elim (hcNot hcAlign)
      · exact False.elim (hdNot hdAlign)
      · exact hz
    · exact False.elim (hnondeg.1 hdegenerate.1)
  have secondary := maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧ ce.natDegree ≤ 4 * n - g ∧
    De.natDegree ≤ 5 * n - g ∧ ee.natDegree ≤ 6 * n - g ∧ _ at secondary
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
  have hceexpand : ce = expand k 60 (cubicCDefectPolynomial68 A C0) := by
    simpa only [ce, Ae, Ce] using expand_cubicCDefectPolynomial68 60 A C0
  have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
    simp only [d, Ae, Be, De, secondaryDDefectPolynomial68,
      map_sub, expand_mul, Polynomial.smul_eq_C_mul, map_mul, expand_C]
  have hc60deg : ce.natDegree ≤ 4 * n - g - 60 := by
    rw [hceexpand]
    apply natDegree_expand_le_sub_sixty_of_aligned_boundary_zero68
      (cubicCDefectPolynomial68 A C0) (4 * n - g) hcAlign (by omega)
    · simpa only [← hceexpand] using secondary.2.2.1
    · rw [← hceexpand]
      exact hdegenerate.1
  have hd60deg : d.natDegree ≤ 5 * n - 2 * g - 60 := by
    rw [hdexpand]
    apply natDegree_expand_le_sub_sixty_of_aligned_boundary_zero68
      (secondaryDDefectPolynomial68 A B D) (5 * n - 2 * g) hdAlign
      (by omega)
    · simpa only [← hdexpand] using hd2
    · rw [← hdexpand]
      exact hdegenerate.2.2.1
  have hcAlign' : 60 ∣ 4 * n - g - 60 := by
    obtain ⟨u, hu⟩ := hcAlign
    refine ⟨u - 1, ?_⟩
    omega
  have hdAlign' : 60 ∣ 5 * n - 2 * g - 60 := by
    obtain ⟨u, hu⟩ := hdAlign
    refine ⟨u - 1, ?_⟩
    omega
  constructor
  · have ht : ce.natDegree ≤ (4 * n - g - 60) - 60 := by
      rw [hceexpand] at hc60deg ⊢
      apply natDegree_expand_le_sub_sixty_of_aligned_boundary_zero68
        (cubicCDefectPolynomial68 A C0) (4 * n - g - 60) hcAlign'
        (by omega) hc60deg
      rw [← hceexpand]
      exact hsixty.1
    omega
  · have ht : d.natDegree ≤ (5 * n - 2 * g - 60) - 60 := by
      rw [hdexpand] at hd60deg ⊢
      apply natDegree_expand_le_sub_sixty_of_aligned_boundary_zero68
        (secondaryDDefectPolynomial68 A B D) (5 * n - 2 * g - 60)
        hdAlign' (by omega) hd60deg
      rw [← hdexpand]
      exact hsixty.2
    omega

#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenDoubleFiveWallDegenerateAlignedDescent68

end LaterDeepLowerOpenDoubleFiveWallAlignedDescent68

end Max11DegreeRoutes
