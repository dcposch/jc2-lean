import LowScale68SecondaryLaterDeepFiveToSixResidualNext

/-! # Expansion-lattice exclusion of the first nonzero residual edges

All canonical source polynomials are expanded by `60`.  Consequently a
nonzero residual edge can move away from the old boundary only by a multiple
of `60`; the apparent `g+1` and `g+2` discriminant packets are empty before
one needs their next row-one coefficient.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveToSixNonzeroEdge68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 12000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- A nonzero coefficient of an expanded polynomial has index divisible by
the expansion stride. -/
theorem coeff_expand_ne_zero_dvd68
    (m : ℕ) (hm : 0 < m) (p : k[X]) (i : ℕ)
    (hi : (expand k m p).coeff i ≠ 0) : m ∣ i := by
  by_contra hdiv
  rw [coeff_expand hm, if_neg hdiv] at hi
  exact hi rfl

/-- Translation by `A*B/3` commutes with expansion. -/
theorem secondaryDDefectPolynomial68_expand
    (m : ℕ) (A B D : k[X]) :
    secondaryDDefectPolynomial68 (expand k m A) (expand k m B)
        (expand k m D) =
      expand k m (secondaryDDefectPolynomial68 A B D) := by
  simp only [secondaryDDefectPolynomial68, map_sub, expand_mul,
    Polynomial.smul_eq_C_mul, map_mul, expand_C]

/-- If the leading `A` and `B` edges and a translated `D` edge are nonzero,
then the residual displacement `s` is divisible by the expansion stride. -/
theorem expandedSecondaryDActiveEdge_stride_dvd68
    (m : ℕ) (hm : 0 < m) (A B D : k[X])
    (n g s : ℕ) (hg : g ≤ 3 * n) (hs : s ≤ 5 * n - g)
    (ha : (expand k m A).coeff (2 * n) ≠ 0)
    (hb : (expand k m B).coeff (3 * n - g) ≠ 0)
    (hd : (secondaryDDefectPolynomial68
      (expand k m A) (expand k m B) (expand k m D)).coeff
        (5 * n - g - s) ≠ 0) :
    m ∣ s := by
  have hAdiv : m ∣ 2 * n :=
    coeff_expand_ne_zero_dvd68 m hm A (2 * n) ha
  have hBdiv : m ∣ 3 * n - g :=
    coeff_expand_ne_zero_dvd68 m hm B (3 * n - g) hb
  have hbase : m ∣ 5 * n - g := by
    have hadd := Nat.dvd_add hAdiv hBdiv
    have hi : 2 * n + (3 * n - g) = 5 * n - g := by omega
    simpa only [hi] using hadd
  have hdexpand : secondaryDDefectPolynomial68
      (expand k m A) (expand k m B) (expand k m D) =
      expand k m (secondaryDDefectPolynomial68 A B D) :=
    secondaryDDefectPolynomial68_expand m A B D
  have hedge : m ∣ 5 * n - g - s := by
    rw [hdexpand] at hd
    exact coeff_expand_ne_zero_dvd68 m hm
      (secondaryDDefectPolynomial68 A B D) (5 * n - g - s) hd
  obtain ⟨u, hu⟩ := hbase
  obtain ⟨v, hv⟩ := hedge
  have hvu : v ≤ u := by
    exact Nat.le_of_mul_le_mul_left (by omega) hm
  refine ⟨u - v, ?_⟩
  symm
  calc
    m * (u - v) = m * u - m * v := Nat.mul_sub_left_distrib m u v
    _ = s := by omega

/-- In particular the first adjacent residual edge is empty. -/
theorem expandedSecondaryDActiveEdge_one_impossible68
    (A B D : k[X]) (n g : ℕ) (hn : 0 < n) (hg : g ≤ 3 * n)
    (ha : (expand k 60 A).coeff (2 * n) ≠ 0)
    (hb : (expand k 60 B).coeff (3 * n - g) ≠ 0)
    (hd : (secondaryDDefectPolynomial68
      (expand k 60 A) (expand k 60 B) (expand k 60 D)).coeff
        (5 * n - g - 1) ≠ 0) : False := by
  have hs : 1 ≤ 5 * n - g := by omega
  have hdiv := expandedSecondaryDActiveEdge_stride_dvd68
    60 (by norm_num) A B D n g 1 hg hs ha hb hd
  norm_num at hdiv

/-- The second adjacent residual edge is empty as well. -/
theorem expandedSecondaryDActiveEdge_two_impossible68
    (A B D : k[X]) (n g : ℕ) (hn : 0 < n) (hg : g ≤ 3 * n)
    (ha : (expand k 60 A).coeff (2 * n) ≠ 0)
    (hb : (expand k 60 B).coeff (3 * n - g) ≠ 0)
    (hd : (secondaryDDefectPolynomial68
      (expand k 60 A) (expand k 60 B) (expand k 60 D)).coeff
        (5 * n - g - 2) ≠ 0) : False := by
  have hs : 2 ≤ 5 * n - g := by omega
  have hdiv := expandedSecondaryDActiveEdge_stride_dvd68
    60 (by norm_num) A B D n g 2 hg hs ha hb hd
  norm_num at hdiv

set_option maxHeartbeats 18000000 in
/-- Both nonzero discriminant alternatives in the `g+1/g+2` packet are
excluded by the source expansion lattice.  Hence both translated defects
vanish at the first two adjacent coefficients. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_firstTwoEdgesZero68
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
    d.coeff (5 * n - g - 1) = 0 ∧
      ee.coeff (6 * n - g - 1) = 0 ∧
      d.coeff (5 * n - g - 2) = 0 ∧
      ee.coeff (6 * n - g - 2) = 0 := by
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
  change d.coeff (5 * n - g - 1) = 0 ∧
    ee.coeff (6 * n - g - 1) = 0 ∧
    d.coeff (5 * n - g - 2) = 0 ∧
    ee.coeff (6 * n - g - 2) = 0
  have hpacket :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_residualNext68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change FiveToSixResidualNextPacket68
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
    (ee.coeff (6 * n - g)) (d.coeff (5 * n - g - 1))
    (ee.coeff (6 * n - g - 1)) (d.coeff (5 * n - g - 2))
    (ee.coeff (6 * n - g - 2)) at hpacket
  have hg3 : g ≤ 3 * n := by omega
  have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hn : 0 < n := by simpa only [n] using hcore.1
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  rcases hpacket with hfirst | hzero | hsecond
  · have himpossible := expandedSecondaryDActiveEdge_one_impossible68
      A B D n g hn hg3 data.ha hfirst.1 hfirst.2.2.1
    exact False.elim himpossible
  · exact hzero
  · have himpossible := expandedSecondaryDActiveEdge_two_impossible68
      A B D n g hn hg3 data.ha hsecond.2.2.1
        hsecond.2.2.2.2.1
    exact False.elim himpossible

end LaterDeepFiveToSixNonzeroEdge68

#print axioms coeff_expand_ne_zero_dvd68
#print axioms secondaryDDefectPolynomial68_expand
#print axioms expandedSecondaryDActiveEdge_stride_dvd68
#print axioms expandedSecondaryDActiveEdge_one_impossible68
#print axioms expandedSecondaryDActiveEdge_two_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_firstTwoEdgesZero68

end Max11DegreeRoutes
