import LowScale68SecondaryLaterDeepThreeRadiusZeroResidualSource

/-! # Parent assembly after deleting the zero three-radius residual leaf -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentAfterThreeRadius68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 12000000 in
/-- The lower later-deep parent after deleting `2g=5n` and the zero
residual leaf at `2g=3n`.  All common translated data are outside the final
split.  The only children are the two attained nonzero packets on the exact
three-radius wall and the strict open sibling `3n<2g<5n`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerParentAfterThreeRadius68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hwindow :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) :
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
    3 * n ≤ 2 * g ∧ 2 * g < 5 * n ∧ l = 0 ∧ beta = 0 ∧
      firstSecondaryThree68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 ∧
      firstSecondaryOne68 (n : k) (g : k)
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 ∧
      ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) ∧
      g < h ∧ d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
      ((2 * g = 3 * n ∧
          (d.coeff (5 * n - h) ≠ 0 ∨ ee.coeff (6 * n - h) ≠ 0) ∧
          ((h < 2 * g ∧
              SecondaryResidualBetweenFace68
                (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
                (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
                (ee.coeff (6 * n - h))) ∨
            (2 * g ≤ h ∧
              ThreeRadiusResidualDoubleInvariantFace68
                (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
                (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
                (ee.coeff (6 * n - 2 * g))))) ∨
        (3 * n < 2 * g ∧ 2 * g < 5 * n)) := by
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
  change 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n at hwindow
  have parent :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerParentResidualEntry68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change 3 * n ≤ 2 * g ∧ 2 * g < 5 * n ∧ l = 0 ∧ beta = 0 ∧
      firstSecondaryThree68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 ∧
      firstSecondaryOne68 (n : k) (g : k)
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 ∧
      ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) ∧
      d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧ g < h
    at parent
  obtain ⟨hlow, hupp, hl, hbeta, hthree, hone, hetop, hrel,
    hddrop, hedrop, hgh⟩ := parent
  have core := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have secondary := maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧
    ce.natDegree ≤ 4 * n - g ∧ De.natDegree ≤ 5 * n - g ∧
    ee.natDegree ≤ 6 * n - g ∧ _ at secondary
  have hn : 0 < n := by simpa only [n] using core.1
  have hdbase : d.natDegree < 5 * n := hddrop.trans (by omega)
  have hebase : ee.natDegree < 6 * n := hedrop.trans (by omega)
  have hbounds := secondaryResidualGap68_degreeBounds n d ee hdbase hebase
  have hsupport : Be.coeff (3 * n - g) ≠ 0 ∨
      ce.coeff (4 * n - g) ≠ 0 := by
    rcases secondary.2.2.2.2.2 with hb | hc | hD | he
    · exact Or.inl hb
    · exact Or.inr hc
    · left
      intro hb0
      have hab : Ae.coeff (2 * n) * Be.coeff (3 * n - g) = 0 := by
        rw [hb0, mul_zero]
      rw [hrel] at hab
      exact hD ((mul_eq_zero.mp hab).resolve_left (by norm_num))
    · exact False.elim (he hetop)
  refine ⟨hlow, hupp, hl, hbeta, hthree, hone, hetop, hrel,
    hgh, hbounds.1, hbounds.2, hsupport, ?_⟩
  by_cases hwall : 2 * g = 3 * n
  · left
    have exactWall :=
      maximalExpandedIntegratedPolynomialLowerSystem_laterDeepThreeRadiusNonzeroResidualSelector68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
    change l = 0 ∧ beta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧ _
      at exactWall
    exact ⟨hwall, exactWall.2.2.2.2.2.2⟩
  · right
    exact ⟨lt_of_le_of_ne hlow (Ne.symm hwall), hupp⟩

#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerParentAfterThreeRadius68

end LaterDeepLowerParentAfterThreeRadius68

end Max11DegreeRoutes
