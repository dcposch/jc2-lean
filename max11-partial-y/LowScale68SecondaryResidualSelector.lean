import LowScale68SecondaryResidualMiddle
import LowScale68SecondaryResidualDouble

/-! # Selecting the next `(6,8)` residual face

The first secondary face leaves both translated odd directions strictly below
gap `g`.  Their minimum actual gap selects either a middle face below `2g` or
the already-impossible residual double face.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SecondaryResidualSelector68

variable {k : Type*} [Field k] [CharZero k]

/-- Minimum actual gap of the two translated odd residual directions. -/
def secondaryResidualGap68 (n : ℕ) (d e : k[X]) : ℕ :=
  min (polynomialGap68 n 5 d) (polynomialGap68 n 6 e)

/-- Both translated residual directions have gap strictly greater than the
first secondary gap. -/
theorem secondaryResidualGap68_gt
    (n g : ℕ) (d e : k[X]) (hsmall : 3 * g < n)
    (hd : d.natDegree < 5 * n - g)
    (he : e.natDegree < 6 * n - g) :
    g < secondaryResidualGap68 n d e := by
  apply lt_min
  · by_cases hd0 : d = 0
    · simp [polynomialGap68, hd0]
      omega
    · simp only [polynomialGap68, if_neg hd0]
      omega
  · by_cases he0 : e = 0
    · simp [polynomialGap68, he0]
      omega
    · simp only [polynomialGap68, if_neg he0]
      omega

/-- Both residual polynomials lie below the boundary selected by their
minimum actual gap. -/
theorem secondaryResidualGap68_degreeBounds
    (n : ℕ) (d e : k[X])
    (hd : d.natDegree < 5 * n) (he : e.natDegree < 6 * n) :
    d.natDegree ≤ 5 * n - secondaryResidualGap68 n d e ∧
      e.natDegree ≤ 6 * n - secondaryResidualGap68 n d e := by
  have hdmin : secondaryResidualGap68 n d e ≤ polynomialGap68 n 5 d :=
    Nat.min_le_left _ _
  have hemin : secondaryResidualGap68 n d e ≤ polynomialGap68 n 6 e :=
    Nat.min_le_right _ _
  constructor
  · by_cases hd0 : d = 0
    · simp [hd0]
    · simp only [polynomialGap68, if_neg hd0] at hdmin
      omega
  · by_cases he0 : e = 0
    · simp [he0]
    · simp only [polynomialGap68, if_neg he0] at hemin
      omega

/-- If the residual pair is not identically zero, one genuine leading
coefficient attains its minimum gap. -/
theorem secondaryResidualGap68_boundary_attained
    (n : ℕ) (d e : k[X])
    (hd : d.natDegree < 5 * n) (he : e.natDegree < 6 * n)
    (hnotboth : ¬ (d = 0 ∧ e = 0)) :
    d.coeff (5 * n - secondaryResidualGap68 n d e) ≠ 0 ∨
      e.coeff (6 * n - secondaryResidualGap68 n d e) ≠ 0 := by
  have hlt : secondaryResidualGap68 n d e < 6 * n + 1 := by
    have hsome : d ≠ 0 ∨ e ≠ 0 := by tauto
    rcases hsome with hd0 | he0
    · exact lt_of_le_of_lt (Nat.min_le_left _ _)
        (polynomialGap68_lt_sentinel_of_ne_zero n 5 d (by omega) hd0)
    · exact lt_of_le_of_lt (Nat.min_le_right _ _)
        (polynomialGap68_lt_sentinel_of_ne_zero n 6 e (by omega) he0)
  rcases min_choice (polynomialGap68 n 5 d) (polynomialGap68 n 6 e) with
      hselected | hselected
  · left
    have hgap : secondaryResidualGap68 n d e = polynomialGap68 n 5 d := by
      simpa only [secondaryResidualGap68] using hselected
    have hd0 : d ≠ 0 := by
      intro hz
      simp only [hgap, polynomialGap68, if_pos hz] at hlt
      omega
    simp only [polynomialGap68, if_neg hd0] at hgap
    have hindex : 5 * n - secondaryResidualGap68 n d e = d.natDegree := by
      omega
    rw [hindex, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hd0
  · right
    have hgap : secondaryResidualGap68 n d e = polynomialGap68 n 6 e := by
      simpa only [secondaryResidualGap68] using hselected
    have he0 : e ≠ 0 := by
      intro hz
      simp only [hgap, polynomialGap68, if_pos hz] at hlt
      omega
    simp only [polynomialGap68, if_neg he0] at hgap
    have hindex : 6 * n - secondaryResidualGap68 n d e = e.natDegree := by
      omega
    rw [hindex, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr he0

set_option maxHeartbeats 6000000 in
/-- In the chamber `3g<n`, the actual residual gap is necessarily a middle
gap `g<h<2g`.  All four leading residual directions are nonzero and satisfy
the exact middle-face discriminant relation. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualSelect68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hsmall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * g < n) :
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
    ∃ h : ℕ, g < h ∧ h < 2 * g ∧
      Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
      d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧
      Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
        3 * ce.coeff (4 * n - g) ^ 2 = 0 := by
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
  change 3 * g < n at hsmall
  change ∃ h : ℕ, g < h ∧ h < 2 * g ∧
    Be.coeff (3 * n - g) ≠ 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
    d.coeff (5 * n - h) ≠ 0 ∧ ee.coeff (6 * n - h) ≠ 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
      3 * ce.coeff (4 * n - g) ^ 2 = 0
  have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hboundary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondarySmallGapBoundary68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          (show 2 * g < n by omega))
  change ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) at hboundary
  have hsupport := hboundary.2.2
  have hdrops :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualDegreeDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          (show 2 * g < n by omega))
  change d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g at hdrops
  have hnotboth : ¬ (d = 0 ∧ ee = 0) := by
    rintro ⟨hd0, he0⟩
    have hdouble : d.natDegree ≤ 5 * n - 2 * g ∧
        ee.natDegree ≤ 6 * n - 2 * g := by
      simp only [hd0, he0, natDegree_zero]
      omega
    have hface :=
      maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualDouble68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
        (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdouble)
    change SecondaryResidualTiedDoubleFace68 (n : k) (g : k)
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (ee.coeff (6 * n - 2 * g)) at hface
    exact secondaryResidualDoubleFace68_impossible n g
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (ee.coeff (6 * n - 2 * g)) ha hsupport hsmall hface
  have hgh : g < h := by
    simpa only [h] using secondaryResidualGap68_gt n g d ee hsmall
      hdrops.1 hdrops.2
  have hdbase : d.natDegree < 5 * n := by omega
  have hebase : ee.natDegree < 6 * n := by omega
  have hbounds : d.natDegree ≤ 5 * n - h ∧
      ee.natDegree ≤ 6 * n - h := by
    simpa only [h] using secondaryResidualGap68_degreeBounds n d ee
      hdbase hebase
  have hattained : d.coeff (5 * n - h) ≠ 0 ∨
      ee.coeff (6 * n - h) ≠ 0 := by
    simpa only [h] using secondaryResidualGap68_boundary_attained n d ee
      hdbase hebase hnotboth
  by_cases hh : h < 2 * g
  · have hface :=
      maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualMiddleFace68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E h
        hterminal hsys (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgh)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hh)
        (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hbounds)
    change SecondaryResidualBetweenFace68
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (ee.coeff (6 * n - h)) at hface
    have hclass := secondaryResidualBetweenFace68_classify_of_support
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (ee.coeff (6 * n - h)) ha hsupport hattained hface
    exact ⟨h, hgh, hh, hclass.1, hclass.2.1, hclass.2.2.1,
      hclass.2.2.2.1, hclass.2.2.2.2⟩
  · have hdouble : d.natDegree ≤ 5 * n - 2 * g ∧
        ee.natDegree ≤ 6 * n - 2 * g := by
      constructor <;> omega
    have hface :=
      maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualDouble68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsmall)
        (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d] using hdouble)
    change SecondaryResidualTiedDoubleFace68 (n : k) (g : k)
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (ee.coeff (6 * n - 2 * g)) at hface
    exact (secondaryResidualDoubleFace68_impossible n g
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (ee.coeff (6 * n - 2 * g)) ha hsupport hsmall hface).elim

end SecondaryResidualSelector68

#print axioms secondaryResidualGap68_gt
#print axioms secondaryResidualGap68_degreeBounds
#print axioms secondaryResidualGap68_boundary_attained
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualSelect68

end Max11DegreeRoutes
