import LowScale68SecondaryLaterDeepSevenBoundaryEndgame

/-! # The remaining later-deep five-to-six window

The two invariant faces are already available.  Here the terminal lower row
is shown to retain its ordinary first-secondary scalar throughout
`5n < 2g ≤ 6n`, despite the deeper load chamber.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepFiveToSix68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 14000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The terminal lower row gives the ordinary scalar `F₀=0` throughout
`5n < 2g ≤ 6n` after `l=beta=delta=0`. -/
theorem lowerRowZeroPolynomial68_fiveToSix_forces_firstSecondaryZero
    (alpha gamma epsilon zeta eta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hrowCoeff :
      (lowerRowZeroPolynomial68
        (integratedUPolynomial68 0 alpha 0 gamma 0 zeta A B
          ((1 / 3 : k) • A ^ 2 + c) D
          ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
        (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta A B
          ((1 / 3 : k) • A ^ 2 + c) D
          ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
        D ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
          (13 * n - 2 * g - 1) = 0) :
    firstSecondaryZero68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 := by
  let j := 13 * n - 2 * g - 1
  let E0 : k[X] :=
    (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Ur : k[X] := (2 / 3 * gamma : k) • B + C zeta
  let W : k[X] :=
    (1 / 9 * gamma : k) • A ^ 2 + (2 / 3 * gamma : k) • c +
      (1 / 3 * epsilon : k) • A + C eta
  have hcoords := integratedPolynomial68_cubicCoordinates
    (0 : k) alpha 0 gamma 0 epsilon zeta eta A B c D e
  have hu := hcoords.u_eq
  have hv := hcoords.v_eq
  change integratedUPolynomial68 0 alpha 0 gamma 0 zeta A B
      ((1 / 3 : k) • A ^ 2 + c) D E0 = _ at hu
  change integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta A B
      ((1 / 3 : k) • A ^ 2 + c) D E0 = _ at hv
  change (lowerRowZeroPolynomial68 _ _ D E0).coeff j = 0 at hrowCoeff
  rw [hu, hv, cubicRowZeroPolynomial68_split,
    cubicHomogeneousRowZeroPolynomial68_eq_expanded,
    cubicHomogeneousRowZeroExpandedPolynomial68, coeff_add, coeff_add]
      at hrowCoeff
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by compute_degree; omega
  have hA2 : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using h
  have h1 : (A ^ 2 * B * c * derivative A).coeff j =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) * A.coeff (2 * n) *
          ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_mul_derivative_at_bounds68 (A ^ 2) B c A
      (4 * n) (3 * n - g) (4 * n - g) (2 * n) (by omega)
      hA2deg hB hc hA
    have hi : 4 * n + (3 * n - g) + (4 * n - g) + 2 * n - 1 = j := by
      dsimp only [j]
      omega
    rw [hi, hA2] at h
    exact h
  have h2 : (A * D * c * derivative A).coeff j =
      A.coeff (2 * n) * D.coeff (5 * n - g) *
        c.coeff (4 * n - g) * A.coeff (2 * n) *
          ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_mul_derivative_at_bounds68 A D c A
      (2 * n) (5 * n - g) (4 * n - g) (2 * n) (by omega)
      hA hD hc hA
    have hi : 2 * n + (5 * n - g) + (4 * n - g) + 2 * n - 1 = j := by
      dsimp only [j]
      omega
    simpa only [hi] using h
  have h3 : (D * e * derivative A).coeff j =
      D.coeff (5 * n - g) * e.coeff (6 * n - g) *
        A.coeff (2 * n) * ((2 * n : ℕ) : k) := by
    have h := coeff_mul_mul_derivative_at_bounds68 D e A
      (5 * n - g) (6 * n - g) (2 * n) (by omega) hD he hA
    have hi : (5 * n - g) + (6 * n - g) + 2 * n - 1 = j := by
      dsimp only [j]
      omega
    simpa only [hi] using h
  have hcore :
      (firstSecondaryCoreRowZeroPolynomial68 A B c D e).coeff j =
        (8 / 81 : k) * (n : k) * A.coeff (2 * n) *
          firstSecondaryZero68
            (A.coeff (2 * n)) (B.coeff (3 * n - g))
            (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
            (e.coeff (6 * n - g)) := by
    simp only [firstSecondaryCoreRowZeroPolynomial68, coeff_smul, coeff_sub,
      h1, h2, h3, smul_eq_mul]
    push_cast
    simp only [firstSecondaryZero68]
    ring
  have hremdeg : (cubicRemainderRowZeroPolynomial68 A B c D e).natDegree <
      j := by
    simp only [cubicRemainderRowZeroPolynomial68]
    dsimp only [j]
    compute_degree
    omega
  have hUl : cubicLoadUPolynomial68 0 alpha 0 gamma 0 zeta
      A B c D e = alpha • D + Ur := by
    simp [Ur, cubicLoadUPolynomial68]
    module
  have hVl : cubicLoadVPolynomial68 0 alpha 0 gamma 0 epsilon eta
      A B c D e = alpha • E0 + W := by
    simp only [E0, W, cubicLoadVPolynomial68, zero_mul, zero_smul,
      smul_zero, zero_add, add_zero]
    module
  have hloadEq :
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c D e = Ur * derivative E0 - D * derivative W := by
    rw [cubicLoadRowZeroPolynomial68, hUl, hVl]
    change (alpha • D + Ur) * derivative E0 -
      D * derivative (alpha • E0 + W) =
        Ur * derivative E0 - D * derivative W
    simp only [derivative_add]
    simp only [derivative_smul]
    simp only [Polynomial.smul_eq_C_mul]
    ring
  have hEdeg : E0.natDegree ≤ 6 * n := by
    simp only [E0]
    compute_degree
    omega
  have hUrdeg : Ur.natDegree ≤ 3 * n - g := by
    simp only [Ur]
    compute_degree
    omega
  have hWdeg : W.natDegree ≤ 4 * n := by
    simp only [W]
    compute_degree
    omega
  have hloaddeg :
      (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c D e).natDegree < j := by
    rw [hloadEq]
    dsimp only [j]
    compute_degree
    omega
  rw [hcore, coeff_eq_zero_of_natDegree_lt hremdeg,
    coeff_eq_zero_of_natDegree_lt hloaddeg] at hrowCoeff
  simp only [add_zero] at hrowCoeff
  have hnCast : (n : k) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  exact (mul_eq_zero.mp hrowCoeff).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) hnCast) ha)

set_option maxHeartbeats 18000000 in
/-- Sharp source-level classification supplied by I4, I3, and the terminal
row in `5n < 2g ≤ 6n`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_topClassification68
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
    let a := Ae.coeff (2 * n)
    let b := Be.coeff (3 * n - g)
    let c := ce.coeff (4 * n - g)
    let d := De.coeff (5 * n - g)
    let e := ee.coeff (6 * n - g)
    (e = 0 ∧ a * b = 3 * d) ∨
      (e = 0 ∧ c = 0 ∧ a * b = d) ∨
      (b = 0 ∧ c = 0 ∧ d = 0) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let a := Ae.coeff (2 * n)
  let b := Be.coeff (3 * n - g)
  let c := ce.coeff (4 * n - g)
  let d := De.coeff (5 * n - g)
  let e := ee.coeff (6 * n - g)
  change 5 * n < 2 * g ∧ 2 * g ≤ 6 * n at hwindow
  change (e = 0 ∧ a * b = 3 * d) ∨
    (e = 0 ∧ c = 0 ∧ a * b = d) ∨
    (b = 0 ∧ c = 0 ∧ d = 0)
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hn : 0 < n := data.hn
  have hinv :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_invariantFaces68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change firstSecondaryFour68 a b c d e = 0 ∧
    firstSecondaryThree68 a b c d e = 0 at hinv
  have hgt3 : 3 * n < 2 * g := by omega
  have hlbeta :=
    maximalExpandedIntegratedPolynomialLowerSystem_l_beta_eq_zero_of_threeRadius_lt_twoGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgt3)
  have hl : l = 0 := hlbeta.1
  have hbeta : beta = 0 := hlbeta.2
  obtain ⟨i4, hI4raw⟩ := data.invariant
  have hI4 := hI4raw
  rw [hl, hbeta] at hI4
  have hdelta :=
    cubicFirstIntegralFourPolynomial68_forces_delta_eq_zero_of_l_beta
      gamma delta epsilon zeta i4 Ae Be ce De ee n g hn data.hg
      hwindow.1 data.hA data.hB data.hc data.hD data.he data.ha hI4
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using cubicEDefectPolynomial68_eq_cubicCoordinates
      Ae Ce Ee
  have hrowZero : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee =
      C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowZeroPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have hnTen : 10 ≤ n := by
    simpa only [n] using weightedRadius68_ge_ten A B C0 D E hn
  have hidx : 59 < 13 * n - 2 * g - 1 := by omega
  have hzeroCoeff :=
    expand_lowerRowZeroPolynomial68_coeff_eq_zero_of_index_gt
      terminal
      (integratedUPolynomial68 l alpha beta gamma delta zeta
        Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee (13 * n - 2 * g - 1) hrowZero hidx
  rw [hl, hbeta, hdelta, hCrec, hErec] at hzeroCoeff
  have hzero :=
    lowerRowZeroPolynomial68_fiveToSix_forces_firstSecondaryZero
      alpha gamma epsilon zeta eta Ae Be ce De ee n g hn hwindow
      data.hA data.ha data.hB data.hc data.hD data.he hzeroCoeff
  change firstSecondaryZero68 a b c d e = 0 at hzero
  exact firstSecondaryFourThreeZero68_classify
    a b c d e data.ha hinv.1 hinv.2 hzero

end LaterDeepFiveToSix68

#print axioms lowerRowZeroPolynomial68_fiveToSix_forces_firstSecondaryZero
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_topClassification68

end Max11DegreeRoutes
