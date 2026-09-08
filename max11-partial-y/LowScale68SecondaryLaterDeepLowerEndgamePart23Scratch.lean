import LowScale68SecondaryLaterDeepLowerEndgamePart22Scratch

/-! # Later-deep lower `(6,8)` window `3n ≤ 2g ≤ 5n`

Tracked I4 already records the mixed walls `2g = 3n` and `2g = 5n` and
the ordinary `F₄` face between them.  This module extracts the matching
I3 face, proves that row-one is load-free after the extra `alpha`/`c`/`gamma`
cancellations, and closes the open interval `3n < 2g < 5n` to the ordinary
five-face `e = 0`, `a*b = 3d`.  The two walls keep mixed I4 together with
mixed `F₂`/`F₀`; they are not empty.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

/-! ## I3 at `10n-2g` -/

/-! ## Degree bounds for the extra-cancelled one-forms -/

/-! ## Row-one load below `12n-2g-1` -/

/-! ## Row-two and row-zero loads after `beta = 0` on the open interval -/

/-! ## Homogeneous one-form coefficients on `3n ≤ 2g ≤ 5n` -/

/-! ## Integrated one-form coefficients -/

/-! ## Packaged five-face on the open interval -/

/-! ## Canonical expanded endpoints -/

set_option maxHeartbeats 8000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerSplit68
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
    l = 0 ∧
      firstSecondaryThree68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 ∧
      firstSecondaryOne68 (n : k) (g : k)
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0 ∧
      ((2 * g = 3 * n ∧
          (-8 / 9 : k) * firstSecondaryFour68
              (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
              (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
              (ee.coeff (6 * n - g)) +
            (5 / 72 * beta : k) * Ae.coeff (2 * n) ^ 3 = 0) ∨
        (3 * n < 2 * g ∧ 2 * g < 5 * n ∧ beta = 0 ∧
          ee.coeff (6 * n - g) = 0 ∧
          Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
            3 * De.coeff (5 * n - g)) ∨
        (2 * g = 5 * n ∧ beta = 0 ∧
          (-8 / 9 : k) * firstSecondaryFour68
              (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
              (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
              (ee.coeff (6 * n - g)) +
            (1 / 4 * delta : k) * Ae.coeff (2 * n) ^ 2 = 0)) := by
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
  have hI3 :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLower_I3face68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  have hF1 :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLower_F1face68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  have hl : l = 0 := hI3.1
  refine ⟨hl, hI3.2, hF1.2, ?_⟩
  have hgt : n < 2 * g := by
    have hn : 0 < n := by
      have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
      simpa only [n] using hcore.1
    omega
  have hsplit :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadSplit68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          And.intro hgt hwindow.1)
  change l = 0 ∧ _ at hsplit
  rcases hsplit.2 with hwall3 | hopen | hwall5 | hdeep
  · exact Or.inl hwall3
  · refine Or.inr (Or.inl ?_)
    have hclass :=
      maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenClassified68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
            And.intro hopen.1 hopen.2.1)
    exact ⟨hopen.1, hopen.2.1, hclass.2.1, hclass.2.2.1, hclass.2.2.2⟩
  · exact Or.inr (Or.inr hwall5)
  · have : 5 * n < 2 * g ∧ 2 * g ≤ 5 * n := ⟨hdeep.1, hwindow.2⟩
    omega

end LaterDeepLowerEndgame68
end Max11DegreeRoutes
