import LowScale68SecondaryLaterDeepFiveToSixStrideDescent

/-! # The earliest five-to-six load wall

At the sole residual arithmetic wall `n=30`, `g=90`, expansion support
reduces the source chart to a linear `A,e` pair and constant `B,c,d`.
This file first eliminates that literal scalar-polynomial model and then
connects the canonical expanded source to it.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveToSixEarliestWall68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Literal linear/constant endpoint model.  The two invariants and three
lower rows are incompatible once the `A` and `B` leading scalars are
nonzero. -/
theorem fiveToSix_earliestWall_linearModel_inconsistent68
    (alpha gamma epsilon zeta eta terminal i4 i3 : k)
    (a a0 b c0 d0 r e0 : k) (ha : a ≠ 0) (hb : b ≠ 0) :
    let A : k[X] := C a * X + C a0
    let B : k[X] := C b
    let c : k[X] := C c0
    let d : k[X] := C d0
    let e : k[X] := C r * X + C e0
    let C0 : k[X] := (1 / 3 : k) • A ^ 2 + c
    let D : k[X] := (1 / 3 : k) • (A * B) + d
    let E : k[X] := (1 / 27 : k) • A ^ 3 +
      (1 / 3 : k) • (A * c) + e
    firstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
        A B C0 D E = C i4 →
    firstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
        A B C0 D E = C i3 →
    lowerRowTwoPolynomial68
        (integratedSPolynomial68 0 alpha 0 0 A B C0 D)
        (integratedTPolynomial68 0 alpha 0 gamma epsilon A B C0 D E)
        (integratedUPolynomial68 0 alpha 0 gamma 0 zeta A B C0 D E)
        (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta
          A B C0 D E) B C0 D E = 0 →
    lowerRowOnePolynomial68
        (integratedTPolynomial68 0 alpha 0 gamma epsilon A B C0 D E)
        (integratedUPolynomial68 0 alpha 0 gamma 0 zeta A B C0 D E)
        (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta
          A B C0 D E) C0 D E = 0 →
    lowerRowZeroPolynomial68
        (integratedUPolynomial68 0 alpha 0 gamma 0 zeta A B C0 D E)
        (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta
          A B C0 D E) D E = C terminal → False := by
  dsimp only
  intro hI4 hI3 hrow2 hrow1 hrow0
  rw [firstIntegralFourPolynomial68_cubicCoordinates,
    cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates] at hI4
  rw [firstIntegralThreePolynomial68_cubicCoordinates,
    cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates] at hI3
  simp only [secondaryResidualInvariantFourPolynomial68,
    secondaryResidualInvariantThreePolynomial68,
    Polynomial.smul_eq_C_mul] at hI4 hI3
  ring_nf at hI4 hI3
  simp only [← C_mul, ← C_pow] at hI4 hI3
  simp only [integratedSPolynomial68, integratedTPolynomial68,
    integratedUPolynomial68, integratedVPolynomial68,
    lowerRowTwoPolynomial68, lowerRowOnePolynomial68,
    lowerRowZeroPolynomial68, derivative_add, derivative_sub,
    derivative_mul, derivative_pow, derivative_smul, derivative_C,
    derivative_X, Polynomial.smul_eq_C_mul] at hrow2 hrow1 hrow0
  ring_nf at hrow2 hrow1 hrow0
  simp only [← C_mul, ← C_pow] at hrow2 hrow1 hrow0
  have h4 := congrArg (fun p : k[X] => p.derivative.eval 0) hI4
  have h3 := congrArg (fun p : k[X] => p.derivative.eval 0) hI3
  have hr2 := congrArg (fun p : k[X] => p.eval 0) hrow2
  have hr1 := congrArg (fun p : k[X] => p.eval 0) hrow1
  have hr0two := congrArg
    (fun p : k[X] => p.derivative.derivative.eval 0) hrow0
  have hr0one := congrArg (fun p : k[X] => p.derivative.eval 0) hrow0
  simp at h4 h3 hr2 hr1 hr0two hr0one
  simp only [← C_mul, ← C_pow, derivative_C, derivative_pow, derivative_X,
    eval_zero, eval_mul, eval_X, eval_C, zero_mul, mul_zero, zero_add,
    add_zero] at h4 h3 hr2 hr1 hr0two hr0one
  norm_num at h4 h3 hr2 hr1 hr0two hr0one
  ring_nf at h4 h3 hr2 hr1 hr0two hr0one
  have hr : r = 0 := by
    have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
    have hzero : a ^ 2 * (b * r) = 0 := by
      linear_combination (-9 / 8 : k) * hr0two +
        (a ^ 2 / 4 : k) * h4
    have hbr : b * r = 0 := (mul_eq_zero.mp hzero).resolve_left ha2
    exact (mul_eq_zero.mp hbr).resolve_left hb
  have hd : d0 = 0 := by
    rw [hr] at h3
    simp only [mul_zero, zero_mul, add_zero] at h3
    have hab : a * b ≠ 0 := mul_ne_zero ha hb
    exact (mul_eq_zero.mp (by linear_combination (-9 / 8 : k) * h3)).resolve_left hab
  have hzeta : zeta = 0 := by
    rw [hr] at h4
    ring_nf at h4
    exact (mul_eq_zero.mp h4).resolve_right ha
  simp only [hr, hd, hzeta] at h4 h3 hr2 hr1 hr0two hr0one
  ring_nf at h4 h3 hr2 hr1 hr0two hr0one
  have hgamma : 4 * c0 + 3 * gamma = 0 := by
    have hab2 : a * b ^ 2 ≠ 0 := mul_ne_zero ha (pow_ne_zero 2 hb)
    apply (mul_eq_zero.mp ?_).resolve_left hab2
    linear_combination (27 / 2 : k) * hr1
  have hepsilon : 4 * b ^ 2 - 9 * epsilon - 12 * e0 = 0 := by
    have hab : a * b ≠ 0 := mul_ne_zero ha hb
    apply (mul_eq_zero.mp ?_).resolve_left hab
    linear_combination 27 * hr2
  have hfinal : a ^ 2 * b ^ 3 = 0 := by
    linear_combination (-81 / 4 : k) * hr0one +
      (a ^ 2 * b / 4 : k) * hepsilon
  exact (mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 3 hb)) hfinal

/-- The canonical expanded source cannot occupy the sole arithmetic wall
left by the stride descent. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_earliestWall_impossible68
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
      n = 30 ∧ g = 90) : False := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let c : k[X] := cubicCDefectPolynomial68 A C0
  let d : k[X] := secondaryDDefectPolynomial68 A B D
  let e : k[X] := cubicEDefectPolynomial68 A C0 E
  change n = 30 ∧ g = 90 at hwall
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n := by omega
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hdesc :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_strideThirtyDescent68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change 30 ∣ n ∧ 30 ∣ g ∧ _ ∧
    (secondaryDDefectPolynomial68 Ae Be De).natDegree ≤
      5 * n - g - 30 ∧ ee.natDegree ≤ 6 * n - g - 30 at hdesc
  have hAdeg : Ae.natDegree = 60 := by
    have hAle := data.hA
    rw [hwall.1] at hAle
    norm_num at hAle
    have ha60 : Ae.coeff 60 ≠ 0 := by
      simpa only [hwall.1] using data.ha
    apply le_antisymm
    · exact hAle
    · exact le_natDegree_of_ne_zero ha60
  have hAorig : A.natDegree = 1 := by
    have h := hAdeg
    simp only [Ae, natDegree_expand] at h
    omega
  have hBorig : B.natDegree = 0 := by
    have h := data.hB
    simp only [hwall.1, hwall.2] at h
    have he : B.natDegree * 60 ≤ 0 := by
      simpa only [Be, natDegree_expand] using h
    omega
  have hcexpand : ce = expand k 60 c := by
    simpa only [ce, Ae, Ce, c] using expand_cubicCDefectPolynomial68 60 A C0
  have hcorig : c.natDegree = 0 := by
    have h := data.hc
    simp only [hwall.1, hwall.2] at h
    rw [hcexpand, natDegree_expand] at h
    omega
  have hdexpand : secondaryDDefectPolynomial68 Ae Be De = expand k 60 d := by
    simpa only [Ae, Be, De, d] using
      secondaryDDefectPolynomial68_expand 60 A B D
  have hdorig : d.natDegree = 0 := by
    have h := hdesc.2.2.2.1
    simp only [hwall.1, hwall.2] at h
    rw [hdexpand, natDegree_expand] at h
    omega
  have heexpand : ee = expand k 60 e := by
    simpa only [ee, Ae, Ce, Ee, e] using
      expand_cubicEDefectPolynomial68 60 A C0 E
  have heorig : e.natDegree ≤ 1 := by
    have h := hdesc.2.2.2.2
    simp only [hwall.1, hwall.2] at h
    rw [heexpand, natDegree_expand] at h
    omega
  obtain ⟨a, a0, hAform⟩ :=
    exists_eq_X_add_C_of_natDegree_le_one (p := A) (by omega)
  have ha : a ≠ 0 := by
    intro ha0
    rw [ha0, C_0, zero_mul, zero_add] at hAform
    have hconst : A.natDegree = 0 := by rw [hAform, natDegree_C]
    omega
  obtain ⟨b, hBform⟩ := natDegree_eq_zero.mp hBorig
  obtain ⟨c0, hcform⟩ := natDegree_eq_zero.mp hcorig
  obtain ⟨d0, hdform⟩ := natDegree_eq_zero.mp hdorig
  obtain ⟨r, e0, heform⟩ :=
    exists_eq_X_add_C_of_natDegree_le_one (p := e) heorig
  have htop :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_B_or_c_top68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0 at htop
  have hc30 : ce.coeff (4 * n - g) = 0 := by
    rw [hwall.1, hwall.2, hcexpand]
    rw [coeff_expand (by norm_num : 0 < 60), if_neg]
    norm_num
  have hbtop : Be.coeff (3 * n - g) ≠ 0 := by
    exact htop.resolve_right (fun hcne => hcne hc30)
  have hb : b ≠ 0 := by
    rw [hwall.1, hwall.2] at hbtop
    change Be.coeff 0 ≠ 0 at hbtop
    change (expand k 60 B).coeff 0 ≠ 0 at hbtop
    rw [← hBform] at hbtop
    simpa using hbtop
  have hgt3 : 3 * n < 2 * g := by omega
  have hlbeta :=
    maximalExpandedIntegratedPolynomialLowerSystem_l_beta_eq_zero_of_threeRadius_lt_twoGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgt3)
  have hl : l = 0 := hlbeta.1
  have hbeta : beta = 0 := hlbeta.2
  obtain ⟨i4, hi4raw⟩ := hsys.firstFour
  obtain ⟨i4e, hi4e⟩ := data.invariant
  have hdelta :=
    cubicFirstIntegralFourPolynomial68_forces_delta_eq_zero_of_l_beta
      gamma delta epsilon zeta i4e Ae Be ce De ee n g
      data.hn data.hg hwindow.1 data.hA data.hB data.hc data.hD data.he
      data.ha (by simpa only [hl, hbeta] using hi4e)
  have hCrec : C0 = (1 / 3 : k) • A ^ 2 + c := by
    simpa only [c] using cubicCDefectPolynomial68_reconstruct A C0
  have hDrec : D = (1 / 3 : k) • (A * B) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct A B D
  have hErec : E = (1 / 27 : k) • A ^ 3 +
      (1 / 3 : k) • (A * c) + e := by
    simpa only [c, e] using
      cubicEDefectPolynomial68_eq_cubicCoordinates A C0 E
  obtain ⟨i3, hi3raw⟩ := hsys.firstThree
  have hi4 := hi4raw
  have hi3 := hi3raw
  have hrow2 := hsys.rowTwo
  have hrow1 := hsys.rowOne
  have hrow0 := hsys.rowZero
  simp only [hl, hbeta, hdelta] at hi4 hi3 hrow2 hrow1 hrow0
  refine fiveToSix_earliestWall_linearModel_inconsistent68
    alpha gamma epsilon zeta eta terminal i4 i3
    a a0 b c0 d0 r e0 ha hb ?_ ?_ ?_ ?_ ?_
  · simpa only [← hAform, hBform, hcform, hdform, ← heform,
      ← hCrec, ← hDrec, ← hErec] using hi4
  · simpa only [← hAform, hBform, hcform, hdform, ← heform,
      ← hCrec, ← hDrec, ← hErec] using hi3
  · simpa only [← hAform, hBform, hcform, hdform, ← heform,
      ← hCrec, ← hDrec, ← hErec] using hrow2
  · simpa only [← hAform, hBform, hcform, hdform, ← heform,
      ← hCrec, ← hDrec, ← hErec] using hrow1
  · simpa only [← hAform, hBform, hcform, hdform, ← heform,
      ← hCrec, ← hDrec, ← hErec] using hrow0

end LaterDeepFiveToSixEarliestWall68

#print axioms fiveToSix_earliestWall_linearModel_inconsistent68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_earliestWall_impossible68

end Max11DegreeRoutes
