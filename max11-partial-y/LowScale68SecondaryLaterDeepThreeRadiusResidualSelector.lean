import LowScale68SecondaryLaterDeepThreeRadiusResidualFaces

/-! # Source residual selector on the exact wall `2g = 3n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepThreeRadiusResidualSelector68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Exact first residual split on the surviving sibling `2g=3n`.
The nonzero residual pair exposes either the ordinary middle face or the
ordinary double invariant face; the identically-zero residual pair is kept
as the one honest exceptional leaf. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepThreeRadiusResidualSelector68
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
      2 * g = 3 * n) :
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
    l = 0 ∧ beta = 0 ∧ g < h ∧
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
      ((d = 0 ∧ ee = 0) ∨
        ((d.coeff (5 * n - h) ≠ 0 ∨ ee.coeff (6 * n - h) ≠ 0) ∧
          ((h < 2 * g ∧
              SecondaryResidualBetweenFace68
                (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
                (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
                (ee.coeff (6 * n - h))) ∨
            (2 * g ≤ h ∧
              ThreeRadiusResidualDoubleInvariantFace68
                (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
                (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
                (ee.coeff (6 * n - 2 * g)))))) := by
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
  change 2 * g = 3 * n at hwall
  have entry :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerThreeRadiusResidualEntry68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change l = 0 ∧ beta = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) ∧
    d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧ g < h
      at entry
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
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using core.2.2.2.2.2
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
    omega
  have hdbase : d.natDegree < 5 * n := entry.2.2.2.2.1.trans (by omega)
  have hebase : ee.natDegree < 6 * n := entry.2.2.2.2.2.1.trans (by omega)
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
      rw [entry.2.2.2.1] at hab
      exact hD ((mul_eq_zero.mp hab).resolve_left (by norm_num))
    · exact False.elim (he entry.2.2.1)
  refine ⟨entry.1, entry.2.1, entry.2.2.2.2.2.2,
    hbounds.1, hbounds.2, hsupport, ?_⟩
  by_cases hzero : d = 0 ∧ ee = 0
  · exact Or.inl hzero
  · right
    have attained := secondaryResidualGap68_boundary_attained
      n d ee hdbase hebase hzero
    refine ⟨attained, ?_⟩
    have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
      simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
    have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
        (1 / 3 : k) • (Ae * ce) + ee := by
      simpa only [ce, ee] using
        cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
    have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
      simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
    obtain ⟨i4, hi4⟩ := hsys.firstFour
    obtain ⟨i3, hi3⟩ := hsys.firstThree
    have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i4 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralFourPolynomial68_of_eq
          l beta gamma delta epsilon zeta i4 A B C0 D E hi4
    have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i3 := by
      simpa only [Ae, Be, Ce, De, Ee] using
        expand_firstIntegralThreePolynomial68_of_eq
          l beta gamma delta epsilon zeta i3 A B C0 D E hi3
    have hi4c := hi4e
    rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
      hDrec, entry.1, entry.2.1] at hi4c
    have hi3c := hi3e
    rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
      hDrec, entry.1, entry.2.1] at hi3c
    by_cases hh : h < 2 * g
    · left
      exact ⟨hh, polynomialSecondaryResidualBetweenFace68_of_threeRadiusWall
        gamma delta epsilon zeta i4 i3 Ae Be ce d ee n g h hn hwall
        entry.2.2.2.2.2.2 hh hA secondary.2.1 secondary.2.2.1
        hbounds.1 hbounds.2 hi4c hi3c⟩
    · right
      have hdouble : d.natDegree ≤ 5 * n - 2 * g ∧
          ee.natDegree ≤ 6 * n - 2 * g := by
        constructor <;> omega
      exact ⟨le_of_not_gt hh,
        polynomialThreeRadiusResidualDoubleInvariantFace68
          gamma delta epsilon zeta i4 i3 Ae Be ce d ee n g hn hwall
          hA secondary.2.1 secondary.2.2.1 hdouble.1 hdouble.2 hi4c hi3c⟩

#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepThreeRadiusResidualSelector68

end LaterDeepThreeRadiusResidualSelector68

end Max11DegreeRoutes
