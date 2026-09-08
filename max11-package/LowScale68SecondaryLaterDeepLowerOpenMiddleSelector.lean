import LowScale68SecondaryLaterDeepLowerParentAfterThreeRadius

/-! # The first residual-load wall on the strict lower later-deep sibling

This isolates the entire middle residual child `h < 2g` of
`3n < 2g < 5n`.  Below `g+h=5n` one obtains the ordinary nonzero
discriminant face.  At equality the `delta*A^2` load enters exactly, and
above equality the same coefficient first forces `delta=0`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleSelector68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Source-facing selector for the first load wall on the middle residual
child of the strict lower later-deep chamber. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleSelector68
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
      h < 2 * g) :
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
      (d.coeff (5 * n - h) ≠ 0 ∨ ee.coeff (6 * n - h) ≠ 0) ∧
      ((g + h < 5 * n ∧
          Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
          d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧
          Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
            3 * ce.coeff (4 * n - g) ^ 2 = 0) ∨
        (g + h = 5 * n ∧
          (-(Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
                d.coeff (5 * n - h)) +
              3 * ce.coeff (4 * n - g) * ee.coeff (6 * n - h) = 0) ∧
          (8 / 3 : k) *
                (Be.coeff (3 * n - g) * ee.coeff (6 * n - h) +
                  ce.coeff (4 * n - g) * d.coeff (5 * n - h)) +
              (1 / 4 * delta : k) * Ae.coeff (2 * n) ^ 2 = 0) ∨
        (5 * n < g + h ∧ delta = 0 ∧
          (-(Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
                d.coeff (5 * n - h)) +
              3 * ce.coeff (4 * n - g) * ee.coeff (6 * n - h) = 0))) := by
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
  have drops :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenResidualDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hopen)
  change l = 0 ∧ beta = 0 ∧ ee.coeff (6 * n - g) = 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
        3 * De.coeff (5 * n - g) ∧
      d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧ g < h
    at drops
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
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using core.2.2.2.2.2
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using drop.1
    omega
  have hdbase : d.natDegree < 5 * n := drops.2.2.2.2.1.trans (by omega)
  have hebase : ee.natDegree < 6 * n := drops.2.2.2.2.2.1.trans (by omega)
  have bounds := secondaryResidualGap68_degreeBounds n d ee hdbase hebase
  have support : Be.coeff (3 * n - g) ≠ 0 ∨
      ce.coeff (4 * n - g) ≠ 0 := by
    rcases secondary.2.2.2.2.2 with hb | hc | hD | he
    · exact Or.inl hb
    · exact Or.inr hc
    · left
      intro hb0
      have hab : Ae.coeff (2 * n) * Be.coeff (3 * n - g) = 0 := by
        rw [hb0, mul_zero]
      rw [drops.2.2.2.1] at hab
      exact hD ((mul_eq_zero.mp hab).resolve_left (by norm_num))
    · exact False.elim (he drops.2.2.1)
  have notboth : ¬ (d = 0 ∧ ee = 0) := by
    rintro ⟨hd0, he0⟩
    have hhzero := hmiddle
    simp only [h, secondaryResidualGap68, polynomialGap68, hd0, he0,
      if_pos, Nat.min_eq_left (by omega : 5 * n + 1 ≤ 6 * n + 1)] at hhzero
    omega
  have attained := secondaryResidualGap68_boundary_attained
    n d ee hdbase hebase notboth
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
    hDrec, drops.1, drops.2.1] at hi4c
  have hi3c := hi3e
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hDrec, drops.1, drops.2.1] at hi3c
  refine ⟨drops.1, drops.2.1, drops.2.2.2.2.2.2,
    bounds.1, bounds.2, support, attained, ?_⟩
  have three :=
    cubicFirstIntegralThreePolynomial68_residualMiddle_forces_face_of_laterDeepLowerOpen
      gamma delta epsilon zeta i3 Ae Be ce d ee n g h hn hg
      drops.2.2.2.2.2.2 hmiddle hopen hA secondary.2.1 secondary.2.2.1
      bounds.1 bounds.2 hi3c
  rcases lt_trichotomy (g + h) (5 * n) with hsum | hsum | hsum
  · left
    have face :=
      polynomialSecondaryResidualBetweenFace68_of_laterDeepLowerOpen_sum_lt_five
        gamma delta epsilon zeta i4 i3 Ae Be ce d ee n g h hn hg
        drops.2.2.2.2.2.2 hmiddle hopen hsum hA secondary.2.1
        secondary.2.2.1 bounds.1 bounds.2 hi4c hi3c
    have classified := secondaryResidualBetweenFace68_classify_of_support
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (ee.coeff (6 * n - h)) ha support attained face
    exact ⟨hsum, classified.1, classified.2.1, classified.2.2.1,
      classified.2.2.2.1, classified.2.2.2.2⟩
  · right; left
    have four := cubicFirstIntegralFourPolynomial68_fiveSumWall_relation
      gamma delta epsilon zeta i4 Ae Be ce d ee n g h hn hg
      drops.2.2.2.2.2.2 hmiddle hopen hsum hA secondary.2.1
      secondary.2.2.1 bounds.1 bounds.2 hi4c
    exact ⟨hsum, three, four⟩
  · right; right
    have hdelta := cubicFirstIntegralFourPolynomial68_forces_delta_of_sum_gt_five
      gamma delta epsilon zeta i4 Ae Be ce d ee n g h hn hmiddle hopen hsum
      hA secondary.2.1 secondary.2.2.1 bounds.1 bounds.2 ha hi4c
    exact ⟨hsum, hdelta, three⟩

#print axioms maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLowerOpenMiddleSelector68

end LaterDeepLowerOpenMiddleSelector68

end Max11DegreeRoutes
