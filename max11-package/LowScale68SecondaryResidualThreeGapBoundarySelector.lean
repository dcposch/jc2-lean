import LowScale68SecondaryResidualLeftBoundary
import LowScale68SecondaryResidualHalfRadiusBoundary
import LowScale68SecondaryResidualThreeGapBoundaryMiddle
import LowScale68SecondaryResidualDoubleLoadWallCanonical
import LowScale68SecondaryResidualOvershootBoundary

/-! # Canonical exhaustive selector for the residual wall `n = 3g`

The four tracked impossibility theorems already close every comparison of
`2h` against `n` and of `h` against `2g` except overshoot `h > 2g`.  The
tracked overshoot wrapper then closes that remaining lane.  This module
packages the partition: Nat trichotomy on `2h` versus `n`, and after
`n < 2h` a second trichotomy on `h` versus `2g`.  The common hypotheses
are exactly the union of the imported wrappers: the canonical source and
the wall `n = 3g`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Exhaustive arithmetic -/

/-- Residual-wall comparisons of `2h` against `n` and of `h` against `2g`. -/
theorem residualThreeGapBoundarySelector_cases (n g h : ℕ) :
    2 * h < n ∨
      2 * h = n ∨
        (n < 2 * h ∧ h < 2 * g) ∨
          h = 2 * g ∨
            2 * g < h := by
  rcases lt_trichotomy (2 * h) n with hlt | heq | hgt
  · exact Or.inl hlt
  · exact Or.inr (Or.inl heq)
  · rcases lt_trichotomy h (2 * g) with hmid | hwall | hover
    · exact Or.inr (Or.inr (Or.inl ⟨hgt, hmid⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hwall)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hover)))

theorem residualThreeGapBoundarySelector_twoGap
    (n g : ℕ) (hg : 0 < g) (hwall : n = 3 * g) : 2 * g < n := by
  omega

theorem residualThreeGapBoundarySelector_overshoot_iff
    (n g h : ℕ) (hwall : n = 3 * g) : 2 * g < h ↔ n < g + h := by
  omega

theorem residualThreeGapBoundarySelector_doubleBounds
    {d e : k[X]} (n g h : ℕ) (hh : h = 2 * g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    d.natDegree ≤ 5 * n - 2 * g ∧ e.natDegree ≤ 6 * n - 2 * g := by
  subst hh
  exact ⟨hd, he⟩

/-! ## Canonical expanded wrapper -/

set_option maxHeartbeats 4000000 in
/-- On a canonical expanded source, the wall `n = 3g` forces the selected
residual gap into the remaining overshoot lane `h > 2g`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_residualThreeGapBoundarySelector_overshoot68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
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
      n = 3 * g) :
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
    2 * g < h := by
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
  have hwall' : n = 3 * g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hg : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hsmall : 2 * g < n :=
    residualThreeGapBoundarySelector_twoGap n g hg hwall'
  have hdrops :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualDegreeDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
  change d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g at hdrops
  have hgh : g < h := by
    simpa only [h] using secondaryResidualGap68_gt_of_strictDrops n g d ee
      hdrops.1 hdrops.2
  have hdbase : d.natDegree < 5 * n := by omega
  have hebase : ee.natDegree < 6 * n := by omega
  have hbounds : d.natDegree ≤ 5 * n - h ∧
      ee.natDegree ≤ 6 * n - h := by
    simpa only [h] using secondaryResidualGap68_degreeBounds n d ee
      hdbase hebase
  change 2 * g < h
  rcases residualThreeGapBoundarySelector_cases n g h with
    hleft | hhalf | hmid | hdouble | hover
  · exact
      (maximalExpandedIntegratedPolynomialLowerSystem_residualLeftBoundaryWall_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall')
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using
          And.intro hgh hleft)).elim
  · exact
      (maximalExpandedIntegratedPolynomialLowerSystem_residualHalfRadiusBoundaryWall_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall')
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using
          hhalf)).elim
  · exact
      (maximalExpandedIntegratedPolynomialLowerSystem_residualThreeGapBoundaryMiddle_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          hwall'.symm)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using
          hmid)).elim
  · exact
      (maximalExpandedIntegratedPolynomialLowerSystem_residualDoubleLoadWall_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          hwall'.symm)
        (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using
            residualThreeGapBoundarySelector_doubleBounds (d := d) (e := ee)
              n g h hdouble hbounds.1 hbounds.2)).elim
  · exact hover

set_option maxHeartbeats 4000000 in
/-- The residual wall `n = 3g` is empty on a canonical expanded source. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_residualThreeGapBoundary_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
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
      n = 3 * g) :
    False := by
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
  have hover :=
    maximalExpandedIntegratedPolynomialLowerSystem_residualThreeGapBoundarySelector_overshoot68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hwall
  change 2 * g < h at hover
  have hwall' : n = 3 * g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall
  exact
    maximalExpandedIntegratedPolynomialLowerSystem_residualOvershootBoundaryWall_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall')
      (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using
          (residualThreeGapBoundarySelector_overshoot_iff n g h hwall').mp
            hover)

#print axioms residualThreeGapBoundarySelector_cases
#print axioms residualThreeGapBoundarySelector_twoGap
#print axioms residualThreeGapBoundarySelector_overshoot_iff
#print axioms residualThreeGapBoundarySelector_doubleBounds
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_residualThreeGapBoundarySelector_overshoot68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_residualThreeGapBoundary_impossible68

end Max11DegreeRoutes
