import Sol68LaterDeepLowerParentOuterReductionScratch
import LowScale68SecondaryLaterDeepFiveToSixEarliestWall

/-! # Reduction of the later-deep outer parent to the five-to-six stride

The strict six-to-seven chamber and the exact seven-radius wall are already
empty.  Thus the preceding outer trichotomy lands in `5n < 2g <= 6n`.
There the expansion-stride theorem has a single exceptional load wall,
`n=30, g=90`; the exact endpoint source calculation eliminates it.  What
remains has both translated defects lower by one full expansion stride.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixStrideReduction68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Once the unique earliest loaded endpoint is removed, the five-to-six
window has a uniform full-stride support drop for the translated `D` and
`E` defects. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_strideSixty68
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
      5 * n < 2 * g ∧ 2 * g ≤ 6 * n) :
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
    30 ∣ n ∧ 30 ∣ g ∧ 30 < n ∧
      (∀ s, 1 ≤ s → s < 60 →
        d.coeff (5 * n - g - s) = 0 ∧
        ee.coeff (6 * n - g - s) = 0) ∧
      d.natDegree ≤ 5 * n - g - 60 ∧
      ee.natDegree ≤ 6 * n - g - 60 := by
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
  change 5 * n < 2 * g ∧ 2 * g ≤ 6 * n at hwindow
  change 30 ∣ n ∧ 30 ∣ g ∧ 30 < n ∧
    (∀ s, 1 ≤ s → s < 60 →
      d.coeff (5 * n - g - s) = 0 ∧
      ee.coeff (6 * n - g - s) = 0) ∧
    d.natDegree ≤ 5 * n - g - 60 ∧
    ee.natDegree ≤ 6 * n - g - 60
  have hthirty :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_strideThirtyDescent68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change 30 ∣ n ∧ 30 ∣ g ∧ _ at hthirty
  have hstride :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_strideSixty_or_earliestWall68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change (n = 30 ∧ g = 90) ∨
    (30 < n ∧
      (∀ s, 1 ≤ s → s < 60 →
        d.coeff (5 * n - g - s) = 0 ∧
        ee.coeff (6 * n - g - s) = 0) ∧
      d.natDegree ≤ 5 * n - g - 60 ∧
      ee.natDegree ≤ 6 * n - g - 60) at hstride
  rcases hstride with hwall | hdrop
  · exact False.elim
      (maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_earliestWall_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall))
  · exact ⟨hthirty.1, hthirty.2.1, hdrop.1,
      hdrop.2.1, hdrop.2.2.1, hdrop.2.2.2⟩

set_option maxHeartbeats 30000000 in
/-- The next later-deep parent is forced entirely into the sharpened
five-to-six packet: the open six-to-seven and exact seven siblings are
empty, while the remaining branch drops by one full expansion stride. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_forces_fiveToSixStride68
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
    5 * n < 2 * g ∧ 2 * g ≤ 6 * n ∧
      firstSecondaryFour68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 ∧
      firstSecondaryThree68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 ∧
      30 ∣ n ∧ 30 ∣ g ∧ 30 < n ∧
      (∀ s, 1 ≤ s → s < 60 →
        d.coeff (5 * n - g - s) = 0 ∧
        ee.coeff (6 * n - g - s) = 0) ∧
      d.natDegree ≤ 5 * n - g - 60 ∧
      ee.natDegree ≤ 6 * n - g - 60 := by
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
  change 5 * n < 2 * g ∧ 2 * g ≤ 6 * n ∧
    _ = 0 ∧ _ = 0 ∧ 30 ∣ n ∧ 30 ∣ g ∧ 30 < n ∧
    (∀ s, 1 ≤ s → s < 60 →
      d.coeff (5 * n - g - s) = 0 ∧
      ee.coeff (6 * n - g - s) = 0) ∧
    d.natDegree ≤ 5 * n - g - 60 ∧
    ee.natDegree ≤ 6 * n - g - 60
  have houter :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuterReduction68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlater)
  change 5 * n < 2 * g ∧ 2 * g < 8 * n ∧
    ((_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) ∨
      (_ ∧ _ ∧ _ ∧ _ ∧ _)) at houter
  rcases houter.2.2 with hfive | hsix | hseven
  · have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n :=
      ⟨houter.1, hfive.1⟩
    have hdrop :=
      maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_strideSixty68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
    change 30 ∣ n ∧ 30 ∣ g ∧ 30 < n ∧ _ ∧ _ ∧ _ at hdrop
    exact ⟨hwindow.1, hwindow.2, hfive.2.1, hfive.2.2,
      hdrop.1, hdrop.2.1, hdrop.2.2.1, hdrop.2.2.2.1,
      hdrop.2.2.2.2.1, hdrop.2.2.2.2.2⟩
  · exact False.elim
      (maximalExpandedIntegratedPolynomialLowerSystem_sixToSeven_empty68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
            (⟨hsix.1, hsix.2.1⟩ : 6 * n < 2 * g ∧ 2 * g < 7 * n)))
  · exact False.elim
      (maximalExpandedIntegratedPolynomialLowerSystem_sevenRadiusWall_empty68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hseven.1))

#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_strideSixty68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_forces_fiveToSixStride68

end LaterDeepLowerParentFiveToSixStrideReduction68

end Max11DegreeRoutes
