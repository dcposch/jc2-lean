import LowScale68SecondaryResidualLeftLoadWindow

/-! # Left residual load window on the closed `(6,8)` chamber `2g < n ≤ 3g`

The tracked module closes the open strip `n < 3g`.  Plan §3.5.A notes
that the comparison which actually fires is `2h < 3g`, and this follows
even on the wall `n = 3g` from `2h < n`.  This file reproves the
smallest arithmetic and row-two coefficient lemmas under `n ≤ 3g`, then
runs the same middle-face / left-scalar argument.  The chamber is empty,
so `l = 0`; the tracked residual load-zero endgame closes the canonical
branch, including `n = 3g`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Chamber arithmetic: `2h < n ≤ 3g` implies `2h < 3g` -/

theorem residualLeftBoundary_leftOfCubic
    (n g h : ℕ) (hlarge : n ≤ 3 * g) (hleft : 2 * h < n) :
    2 * h < 3 * g :=
  Nat.lt_of_lt_of_le hleft hlarge

theorem residualLeftBoundary_lt_double
    (n g h : ℕ) (hlarge : n ≤ 3 * g) (hleft : 2 * h < n) :
    h < 2 * g := by
  have h23 : 2 * h < 3 * g := residualLeftBoundary_leftOfCubic n g h hlarge hleft
  omega

theorem residualLeftBoundary_cubic_lt_leftIndex
    (n g h : ℕ) (hlarge : n ≤ 3 * g) (hleft : 2 * h < n) :
    11 * n - 3 * g - 1 < 11 * n - 2 * h - 1 := by
  have h23 : 2 * h < 3 * g := residualLeftBoundary_leftOfCubic n g h hlarge hleft
  omega

/-! ## Jacobian load below the left index, without `n < 3g` -/

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowTwoPolynomial68_degree_lt_leftIndex_of_leftBoundary
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hlarge : n ≤ 3 * g)
    (hgh : g < h) (hleft : 2 * h < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e).natDegree <
        11 * n - 2 * h - 1 := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hle := cubicLoadRowTwoPolynomial68_degree_le_loadIndex_of_leftLoadWindow
    l alpha beta gamma delta epsilon zeta eta A B c D e n g h
    hn hg hsmall hgh hA hB hc hD he
  exact hle.trans_lt (residualLeftLoadWindow_load_lt_leftIndex n h hleft)

/-! ## Left row-two coefficient after the I4-forced `Q` bound -/

set_option maxHeartbeats 4000000 in
/-- On `2h < n ≤ 3g`, residual row two is dominated by `derivative(d*e)`
once I4 has forced `Q` into the load window.  The cubic comparison is
`2h < 3g`, which is free from `2h < n`. -/
theorem residualRowTwo_coeff_leftChamber68_of_leftBoundary
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hsmall : 2 * g < n) (hlarge : n ≤ 3 * g) (hleft : 2 * h < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 8 * n) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 2 * h - 1) =
      (8 / 3 : k) * ((11 * n - 2 * h : ℕ) : k) *
        d.coeff (5 * n - h) * e.coeff (6 * n - h) := by
  let Q := residualIncidenceQ68 B c d e
  let inner := residualRowTwoInner68 A B c d e
  set idx := 11 * n - 2 * h - 1
  have hh : h < 2 * g :=
    residualLeftBoundary_lt_double n g h hlarge hleft
  have hidxLoad : 10 * n - 1 < idx := by
    dsimp [idx]
    exact residualLeftLoadWindow_load_lt_leftIndex n h hleft
  have hidxCubic : 11 * n - 3 * g - 1 < idx := by
    dsimp [idx]
    exact residualLeftBoundary_cubic_lt_leftIndex n g h hlarge hleft
  have hQdeg :=
    residualRowTwoInner_Q_degree_le_loadIndex_of_leftLoadWindow
      A B c d e n hn hA hQ
  have hAQ : (A * derivative Q).natDegree < idx :=
    hQdeg.1.trans_lt hidxLoad
  have hAQ' : (derivative A * Q).natDegree < idx :=
    hQdeg.2.trans_lt hidxLoad
  have hcore := residualRowTwoInner_BcCore_degree_le68_of_twoGap
    A B c n g hg hsmall hA hB hc
  have hAB : (A * B ^ 2 * derivative B).natDegree < idx :=
    hcore.1.trans_lt hidxCubic
  have hA3 : (derivative A * B ^ 3).natDegree < idx :=
    hcore.2.1.trans_lt hidxCubic
  have hBc : (derivative (B * c ^ 2)).natDegree < idx :=
    hcore.2.2.trans_lt hidxCubic
  have hBd := residualRowTwoInner_Bd_degree_le68_of_twoGap
    B d n g h hg hgh hh hsmall hB hd
  have hBd' : (derivative (B ^ 2 * d)).natDegree < idx := by
    dsimp [idx]
    omega
  have hdebound := natDegree_mul_le_of_le hd he
  have hide : (5 * n - h) + (6 * n - h) = 11 * n - 2 * h := by omega
  rw [hide] at hdebound
  have hdecoeff := coeff_mul_at_bounds68 d e (5 * n - h) (6 * n - h) hd he
  rw [hide] at hdecoeff
  have hder0 : 0 < 11 * n - 2 * h := by omega
  have hde := coeff_derivative_at_bound68 (d * e) (11 * n - 2 * h) hder0
  rw [hdecoeff] at hde
  have h0Q : ((-6 : k) • (A * derivative Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ, mul_zero]
  have h0Q' : ((3 : k) • (derivative A * Q)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAQ', mul_zero]
  have h0AB : ((-2 : k) • (A * B ^ 2 * derivative B)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hAB, mul_zero]
  have h0A3 : ((-2 / 3 : k) • (derivative A * B ^ 3)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hA3, mul_zero]
  have h0Bd : ((6 : k) • derivative (B ^ 2 * d)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBd', mul_zero]
  have h0Bc : ((6 : k) • derivative (B * c ^ 2)).coeff idx = 0 := by
    rw [coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hBc, mul_zero]
  have hde' : ((-18 : k) • derivative (d * e)).coeff idx =
      (-18 : k) * (d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((11 * n - 2 * h : ℕ) : k)) := by
    rw [coeff_smul, smul_eq_mul]
    dsimp [idx]
    rw [hde]
  have hinner : inner.coeff idx =
      (-18 : k) * (d.coeff (5 * n - h) * e.coeff (6 * n - h) *
        ((11 * n - 2 * h : ℕ) : k)) := by
    dsimp [inner, residualRowTwoInner68]
    simp only [coeff_add]
    rw [h0Q, h0Q', h0AB, h0A3, h0Bd, h0Bc, hde']
    ring
  rw [residualRowTwo_eq_inner68, coeff_smul, smul_eq_mul]
  change ((-4 / 27 : k) * inner.coeff idx) = _
  rw [hinner]
  ring

set_option maxHeartbeats 2000000 in
theorem residualRowTwo_leftChamber_ne_zero68_of_leftBoundary
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hsmall : 2 * g < n) (hlarge : n ≤ 3 * g) (hleft : 2 * h < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hQ : (residualIncidenceQ68 B c d e).natDegree ≤ 8 * n)
    (hd0 : d.coeff (5 * n - h) ≠ 0)
    (he0 : e.coeff (6 * n - h) ≠ 0) :
    (secondaryResidualRowTwoPolynomial68 A B c d e).coeff
        (11 * n - 2 * h - 1) ≠ 0 := by
  rw [residualRowTwo_coeff_leftChamber68_of_leftBoundary A B c d e n g h
    hn hg hgh hsmall hlarge hleft hA hB hc hd he hQ]
  have hscalar : (8 / 3 : k) ≠ 0 := by norm_num
  have hN : ((11 * n - 2 * h : ℕ) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hscalar hN) hd0) he0

/-! ## Polynomial face: middle I4/I3 plus left row two -/

set_option maxHeartbeats 4000000 in
theorem polynomialSecondaryResidualLeftBoundary68_impossible
    (l alpha beta gamma delta epsilon zeta eta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hlarge : n ≤ 3 * g)
    (hgh : g < h) (hleft : 2 * h < n)
    (hA : A.natDegree ≤ 2 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hsupport : B.coeff (3 * n - g) ≠ 0 ∨ c.coeff (4 * n - g) ≠ 0)
    (hattained : d.coeff (5 * n - h) ≠ 0 ∨ e.coeff (6 * n - h) ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrowTwo :
      secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon
          zeta eta A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    False := by
  have hmid := polynomialSecondaryResidualBetweenFace68_of_leftLoadWindow
    l beta gamma delta epsilon zeta i4 i3 A B c d e n g h
    hg hgh hsmall hlarge hleft hA hB hc hd he hi4 hi3
  have hclass := secondaryResidualBetweenFace68_classify_of_support
    (A.coeff (2 * n)) (B.coeff (3 * n - g))
    (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
    (e.coeff (6 * n - h)) ha hsupport hattained hmid
  have hQ := residualIncidenceQ68_degree_le_eightRadius_of_leftLoadWindow
    l beta gamma delta epsilon zeta i4 A B c d e n g h
    hg hsmall hgh hA hB hc hd he hi4
  have hload :=
    cubicLoadRowTwoPolynomial68_degree_lt_leftIndex_of_leftBoundary
      l alpha beta gamma delta epsilon zeta eta A B c d e n g h
      hn hg hsmall hlarge hgh hleft hA hB hc hd he
  have hcoeff0 := residualRowTwo_coeff_eq_zero_of_loadCutoff68
    A B c d e
    (cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon
      zeta eta A B c ((1 / 3 : k) • (A * B) + d) e)
    (11 * n - 2 * h - 1) hload hrowTwo
  exact residualRowTwo_leftChamber_ne_zero68_of_leftBoundary
    A B c d e n g h hn hg hgh hsmall hlarge hleft hA hB hc hd he hQ
    hclass.2.2.1 hclass.2.2.2.1 hcoeff0

/-- The empty chamber yields `l = 0` for composition with the tracked
residual load-zero endgame. -/
theorem polynomialSecondaryResidualLeftBoundary68_loadL_eq_zero
    (l alpha beta gamma delta epsilon zeta eta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hlarge : n ≤ 3 * g)
    (hgh : g < h) (hleft : 2 * h < n)
    (hA : A.natDegree ≤ 2 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hsupport : B.coeff (3 * n - g) ≠ 0 ∨ c.coeff (4 * n - g) ≠ 0)
    (hattained : d.coeff (5 * n - h) ≠ 0 ∨ e.coeff (6 * n - h) ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrowTwo :
      secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 l alpha beta gamma delta epsilon
          zeta eta A B c ((1 / 3 : k) • (A * B) + d) e = 0) :
    l = 0 :=
  (polynomialSecondaryResidualLeftBoundary68_impossible
    l alpha beta gamma delta epsilon zeta eta i4 i3 A B c d e n g h
    hn hg hsmall hlarge hgh hleft hA ha hB hc hd he hsupport hattained
    hi4 hi3 hrowTwo).elim

theorem integratedPolynomialLowerSystem68_residualLeftBoundary_loadL_eq_zero
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hsmall : 2 * g < n) (hlarge : n ≤ 3 * g)
    (hgh : g < h) (hleft : 2 * h < n)
    (hC0 : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hD : D = (1 / 3 : k) • (A * B) + d)
    (hE : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hA : A.natDegree ≤ 2 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hsupport : B.coeff (3 * n - g) ≠ 0 ∨ c.coeff (4 * n - g) ≠ 0)
    (hattained : d.coeff (5 * n - h) ≠ 0 ∨ e.coeff (6 * n - h) ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    l = 0 := by
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4c : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c D e = C i4 := by
    have h := hi4
    rw [hC0, hE, firstIntegralFourPolynomial68_cubicCoordinates] at h
    exact h
  have hi3c : cubicFirstIntegralThreePolynomial68
      l beta gamma delta epsilon zeta A B c D e = C i3 := by
    have h := hi3
    rw [hC0, hE, firstIntegralThreePolynomial68_cubicCoordinates] at h
    exact h
  have hi4d : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4 := by
    simpa [hD] using hi4c
  have hi3d : cubicFirstIntegralThreePolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3 := by
    simpa [hD] using hi3c
  have hrowTwo := integratedPolynomialLowerSystem68_residualRowTwo
    l alpha beta gamma delta epsilon zeta eta terminal
    A B C0 D E c d e hC0 hD hE hsys
  exact polynomialSecondaryResidualLeftBoundary68_loadL_eq_zero
    l alpha beta gamma delta epsilon zeta eta i4 i3 A B c d e n g h
    hn hg hsmall hlarge hgh hleft hA ha hB hc hd he hsupport hattained
    hi4d hi3d hrowTwo

/-! ## Canonical expanded system -/

set_option maxHeartbeats 4000000 in
/-- On a maximal expanded system in `2g < n ≤ 3g`, a residual gap with
`g < h` and `2h < n` forces `l = 0`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_residualLeftBoundary_loadL_eq_zero68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hchamber :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      2 * g < n ∧ n ≤ 3 * g)
    (hleft :
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
      g < h ∧ 2 * h < n) :
    l = 0 := by
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
  change 2 * g < n ∧ n ≤ 3 * g at hchamber
  change g < h ∧ 2 * h < n at hleft
  have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hn : 0 < n := by simpa only [n] using hcore.1
  have hg : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hdrops :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualDegreeDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber.1)
  change d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g at hdrops
  have hdbase : d.natDegree < 5 * n := by omega
  have hebase : ee.natDegree < 6 * n := by omega
  have hbounds : d.natDegree ≤ 5 * n - h ∧
      ee.natDegree ≤ 6 * n - h := by
    simpa only [h] using secondaryResidualGap68_degreeBounds n d ee
      hdbase hebase
  have hnotboth : ¬(d = 0 ∧ ee = 0) :=
    residualLeftLoadWindow_not_both_zero n h d ee hn hleft.2 rfl
  have hattained :
      d.coeff (5 * n - h) ≠ 0 ∨ ee.coeff (6 * n - h) ≠ 0 := by
    simpa only [h] using
      secondaryResidualGap68_boundary_attained n d ee hdbase hebase hnotboth
  have hboundary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondarySmallGapBoundary68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber.1)
  have hsupport :
      Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0 := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hboundary.2.2
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    calc
      Ee = (1 / 3 : k) • (Ae * Ce) - (2 / 27 : k) • Ae ^ 3 + ee := by
        simpa only [ee] using cubicEDefectPolynomial68_reconstruct Ae Ce Ee
      _ = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
        rw [hCrec]
        apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
        simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
          map_pow, RatFunc.algebraMap_C]
        simp only [map_div₀, map_ofNat, map_one]
        ring
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    have hx := congrArg (expand k 60) hi4
    simpa [Ae, Be, Ce, De, Ee, expand_firstIntegralFourPolynomial68] using hx
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    have hx := congrArg (expand k 60) hi3
    simpa [Ae, Be, Ce, De, Ee, expand_firstIntegralThreePolynomial68] using hx
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec] at hi4c
  have hi3c := hi3e
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hDrec] at hi3c
  have h2e : lowerRowTwoPolynomial68
      (integratedSPolynomial68 l alpha beta delta Ae Be Ce De)
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Be Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedSPolynomial68, ← expand_integratedTPolynomial68,
      ← expand_integratedUPolynomial68, ← expand_integratedVPolynomial68,
      lowerRowTwoPolynomial68_expand, hsys.rowTwo, map_zero, zero_mul]
  have hrowTwo :
      let Crec := (1 / 3 : k) • Ae ^ 2 + ce
      let Drec := (1 / 3 : k) • (Ae * Be) + d
      let Erec := (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee
      lowerRowTwoPolynomial68
        (integratedSPolynomial68 l alpha beta delta Ae Be Crec Drec)
        (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Crec Drec
          Erec)
        (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Crec
          Drec Erec)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          Ae Be Crec Drec Erec) Be Crec Drec Erec = 0 := by
    simp only
    rw [← hCrec, ← hDrec, ← hErec]
    exact h2e
  have hsum := polynomialSecondaryResidualRowTwo68
    l alpha beta gamma delta epsilon zeta eta Ae Be ce d ee hrowTwo
  exact polynomialSecondaryResidualLeftBoundary68_loadL_eq_zero
    l alpha beta gamma delta epsilon zeta eta i4 i3 Ae Be ce d ee n g h
    hn hg hchamber.1 hchamber.2 hleft.1 hleft.2 hA ha hB hc
    hbounds.1 hbounds.2 hsupport hattained hi4c hi3c hsum

set_option maxHeartbeats 2000000 in
/-- After the closed left load window forces `l = 0`, the tracked residual
load-zero endgame closes the canonical `2g < n` branch, including the
wall `n = 3g`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_residualLeftBoundary_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hchamber :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      2 * g < n ∧ n ≤ 3 * g)
    (hleft :
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
      g < h ∧ 2 * h < n) :
    False := by
  have hl :=
    maximalExpandedIntegratedPolynomialLowerSystem_residualLeftBoundary_loadL_eq_zero68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys hchamber hleft
  exact maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualLoadZero_impossible68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys hl (by
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      exact hchamber.1)

/-- Specialisation of the closed chamber to the wall `n = 3g`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_residualLeftBoundaryWall_impossible68
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
      n = 3 * g)
    (hleft :
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
      g < h ∧ 2 * h < n) :
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
  change n = 3 * g at hwall
  have hgpos : 0 < g := by
    have hsecondary :=
      maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have hsmall : 2 * g < n := by
    rw [hwall]
    omega
  have hlarge : n ≤ 3 * g := by
    rw [hwall]
  exact
    maximalExpandedIntegratedPolynomialLowerSystem_residualLeftBoundary_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys ⟨hsmall, hlarge⟩ hleft

#print axioms residualLeftBoundary_leftOfCubic
#print axioms residualRowTwo_coeff_leftChamber68_of_leftBoundary
#print axioms polynomialSecondaryResidualLeftBoundary68_impossible
#print axioms polynomialSecondaryResidualLeftBoundary68_loadL_eq_zero
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_residualLeftBoundary_loadL_eq_zero68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_residualLeftBoundary_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_residualLeftBoundaryWall_impossible68

end Max11DegreeRoutes
