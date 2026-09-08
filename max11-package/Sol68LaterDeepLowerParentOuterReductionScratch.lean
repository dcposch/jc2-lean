import Sol68LaterDeepLowerOpenMiddleBelowFiveClosureScratch
import LowScale68SecondaryLaterDeepPreclampedLowerEndgame

/-! # Later-deep lower-parent and outer reduction

The completed strict lower-open argument, together with the already closed
three- and five-radius boundary cases, empties the whole closed lower window
`3n <= 2g <= 5n`.  The clamped endgame then removes `8n <= 2g`.

Consequently the next parent is exactly preclamped.  Its sharp surviving
packet is recorded using both ordinary invariant faces below six radii, the
unique-`c` classification in the open six-to-seven chamber, and the full
loaded packet on the exact seven-radius wall.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentOuterReduction68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The immediate closed lower parent is empty, including both boundary
walls. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerParent_impossible68
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
      3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n) : False := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n at hwindow
  have hopen :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerParent_forces_openMiddle68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change 3 * n < 2 * g ∧ 2 * g < 5 * n ∧ _ at hopen
  exact
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpen_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          (⟨hopen.1, hopen.2.1⟩ : 3 * n < 2 * g ∧ 2 * g < 5 * n))

set_option maxHeartbeats 30000000 in
/-- Sharp next-parent reduction above the lower window.  No point survives
outside `5n < 2g < 8n`; inside it the three displayed packets are exhaustive.
-/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuterReduction68
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
    5 * n < 2 * g ∧ 2 * g < 8 * n ∧
      ((2 * g ≤ 6 * n ∧
          firstSecondaryFour68
            (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
            (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
            (ee.coeff (6 * n - g)) = 0 ∧
          firstSecondaryThree68
            (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
            (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
            (ee.coeff (6 * n - g)) = 0) ∨
        (6 * n < 2 * g ∧ 2 * g < 7 * n ∧ Be = 0 ∧
          ce.coeff (4 * n - g) ≠ 0 ∧
          De.coeff (5 * n - g) = 0 ∧ ee.coeff (6 * n - g) = 0) ∨
        (2 * g = 7 * n ∧ Be = 0 ∧
          De.coeff (5 * n - g) ^ 2 +
            2 * ce.coeff (4 * n - g) * ee.coeff (6 * n - g) = 0 ∧
          (8 / 3 : k) * De.coeff (5 * n - g) * ce.coeff (4 * n - g) +
            zeta * Ae.coeff (2 * n) = 0 ∧
          ee.coeff (6 * n - g) *
            (2 * Ae.coeff (2 * n) * ce.coeff (4 * n - g) +
              3 * ee.coeff (6 * n - g)) = 0)) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 3 * n ≤ 2 * g at hlater
  change 5 * n < 2 * g ∧ 2 * g < 8 * n ∧
    ((_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) ∨
      (_ ∧ _ ∧ _ ∧ _ ∧ _))
  have hgt5 : 5 * n < 2 * g := by
    by_contra hnot
    have hle5 : 2 * g ≤ 5 * n := by omega
    exact
      maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerParent_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
            (⟨hlater, hle5⟩ : 3 * n ≤ 2 * g ∧ 2 * g ≤ 5 * n))
  have hlt8 : 2 * g < 8 * n := by
    by_contra hnot
    have hge8 : 8 * n ≤ 2 * g := by omega
    exact
      maximalExpandedIntegratedPolynomialLowerSystem_clamped_empty68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hge8)
  have hsplit :=
    maximalExpandedIntegratedPolynomialLowerSystem_preclampedSplit68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          (⟨hgt5, hlt8⟩ : 5 * n < 2 * g ∧ 2 * g < 8 * n))
  change (_ ∧ _) ∨ (_ ∧ _ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _) at hsplit
  refine ⟨hgt5, hlt8, ?_⟩
  rcases hsplit with hle6 | hopen67 | hwall7
  · left
    have hfaces :=
      maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_invariantFaces68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
            (⟨hgt5, hle6.1⟩ : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n))
    change _ = 0 ∧ _ = 0 at hfaces
    exact ⟨hle6.1, hfaces.1, hfaces.2⟩
  · right; left
    have hpacket :=
      maximalExpandedIntegratedPolynomialLowerSystem_sixToSeven_c_only_top68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
            (⟨hopen67.1, hopen67.2.1⟩ :
              6 * n < 2 * g ∧ 2 * g < 7 * n))
    change Be = 0 ∧ _ ≠ 0 ∧ _ = 0 ∧ _ = 0 at hpacket
    exact ⟨hopen67.1, hopen67.2.1, hpacket.1,
      hpacket.2.1, hpacket.2.2.1, hpacket.2.2.2⟩
  · right; right
    have hpacket :=
      maximalExpandedIntegratedPolynomialLowerSystem_sevenRadiusWall_packet68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall7.1)
    change Be = 0 ∧ _ = 0 ∧ _ = 0 ∧ _ = 0 at hpacket
    exact ⟨hwall7.1, hpacket.1, hpacket.2.1,
      hpacket.2.2.1, hpacket.2.2.2⟩

#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerParent_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuterReduction68

end LaterDeepLowerParentOuterReduction68

end Max11DegreeRoutes
