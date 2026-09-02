import Sol68FiveToSixUniformLoadFreeStrideScratch

/-! # Symbolic terminal load for the five-to-six stride

At `r = 7n-2g`, the I4 coefficient has index `2n` and acquires exactly the
load `zeta*A_top`; I3 remains ordinary at index `3n`.  The independent
row-zero coefficient is always `6n-1`.  Its exact load eliminates `zeta`
uniformly, after which the terminal edge is either zero or the preserved
all-nonzero cusp.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixTerminalLoadStride68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Exact loaded I4 coefficient at `s=7n-2g`. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_terminalLoad_fiveToSix
    (gamma epsilon zeta : k) (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n)
    (he : e.natDegree ≤ g - n) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (2 * n) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (g - n) +
          c.coeff (4 * n - g) * d.coeff (g - 2 * n)) +
        zeta * A.coeff (2 * n) := by
  have hB3 : (B ^ 3).natDegree < 2 * n := by
    compute_degree
    omega
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g) (g - n) hB he
  have hBei : (3 * n - g) + (g - n) = 2 * n := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g) (g - 2 * n) hc hd
  have hcdi : (4 * n - g) + (g - 2 * n) = 2 * n := by omega
  rw [hcdi] at hcd
  have hres : (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
      (2 * n) = (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (g - n) +
          c.coeff (4 * n - g) * d.coeff (g - 2 * n)) := by
    simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
      coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3, hBe, hcd]
    ring
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates,
    coeff_add, coeff_add, coeff_add, hres]
  have hloadB : ((2 * epsilon : k) • B).natDegree < 2 * n := by
    compute_degree
    omega
  have hloadd : ((4 * gamma : k) • d).natDegree < 2 * n := by
    compute_degree
    omega
  rw [coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadd, coeff_smul, smul_eq_mul]
  ring

/-- I3 remains ordinary at the terminal I4 load. -/
theorem cubicFirstIntegralThreePolynomial68_coeff_terminalLoad_fiveToSix
    (gamma epsilon zeta : k) (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n)
    (he : e.natDegree ≤ g - n) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (3 * n) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (g - 2 * n)) +
          3 * c.coeff (4 * n - g) * e.coeff (g - n)) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n)
    (3 * n - g) (g - 2 * n) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (g - 2 * n) = 3 * n := by omega
  rw [hABdi] at hABd
  have hB2c : (B ^ 2 * c).natDegree < 3 * n := by
    compute_degree
    omega
  have hce := coeff_mul_at_bounds68 c e (4 * n - g) (g - n) hc he
  have hcei : (4 * n - g) + (g - n) = 3 * n := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 3 * n := by
    compute_degree
    omega
  have hres : (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
      (3 * n) = (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (g - 2 * n)) +
          3 * c.coeff (4 * n - g) * e.coeff (g - n)) := by
    simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
      coeff_sub, coeff_smul, smul_eq_mul, hABd,
      coeff_eq_zero_of_natDegree_lt hB2c, hce,
      coeff_eq_zero_of_natDegree_lt hd2]
    ring
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates,
    coeff_sub, coeff_add, coeff_add, coeff_add, hres]
  have hloadB : (zeta • B).natDegree < 3 * n := by
    compute_degree
    omega
  have hloadc : ((2 * epsilon : k) • c).natDegree < 3 * n := by
    compute_degree
    omega
  have hloade : ((4 * gamma : k) • e).natDegree < 3 * n := by
    compute_degree
    omega
  have hloadB2 : ((2 / 3 * gamma : k) • B ^ 2).natDegree < 3 * n := by
    compute_degree
    omega
  rw [coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadc,
    coeff_eq_zero_of_natDegree_lt hloade,
    coeff_eq_zero_of_natDegree_lt hloadB2]
  ring

/-- Homogeneous terminal row-zero coefficient. -/
theorem secondaryResidualRowZeroPolynomial68_coeff_terminalLoad_fiveToSix
    (A B c d e : k[X]) (n g : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n)
    (he : e.natDegree ≤ g - n) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff (6 * n - 1) =
      (-8 / 27 : k) * (n : k) * A.coeff (2 * n) ^ 2 *
        (B.coeff (3 * n - g) * e.coeff (g - n) +
          c.coeff (4 * n - g) * d.coeff (g - 2 * n)) := by
  have h1raw := coeff_mul_mul_mul_derivative_at_bounds68 A B e A
    (2 * n) (3 * n - g) (g - n) (2 * n) (by omega)
    hA hB he hA
  have hi1 : 2 * n + (3 * n - g) + (g - n) + 2 * n - 1 =
      6 * n - 1 := by omega
  rw [hi1] at h1raw
  have h1 : (A * derivative A * B * e).coeff (6 * n - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) *
        B.coeff (3 * n - g) * e.coeff (g - n) *
          (((2 * n : ℕ) : k)) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h1raw
  have h2raw := coeff_mul_mul_mul_derivative_at_bounds68 A c d A
    (2 * n) (4 * n - g) (g - 2 * n) (2 * n) (by omega)
    hA hc hd hA
  have hi2 : 2 * n + (4 * n - g) + (g - 2 * n) + 2 * n - 1 =
      6 * n - 1 := by omega
  rw [hi2] at h2raw
  have h2 : (A * derivative A * c * d).coeff (6 * n - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) *
        c.coeff (4 * n - g) * d.coeff (g - 2 * n) *
          (((2 * n : ℕ) : k)) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2raw
  have hlow1 : (A * B ^ 2 * derivative d).natDegree < 6 * n - 1 := by
    compute_degree; omega
  have hlow2 : (A * B * derivative B * d).natDegree < 6 * n - 1 := by
    compute_degree; omega
  have hlow3 : (derivative A * B * c ^ 2).natDegree < 6 * n - 1 := by
    compute_degree; omega
  have hlow4 : (derivative A * d * e).natDegree < 6 * n - 1 := by
    compute_degree; omega
  have hlow5 : (B * c * derivative e).natDegree < 6 * n - 1 := by
    compute_degree; omega
  have hlow6 : (B * d * derivative d).natDegree < 6 * n - 1 := by
    compute_degree; omega
  have hlow7 : (derivative B * d ^ 2).natDegree < 6 * n - 1 := by
    compute_degree; omega
  have hlow8 : (c * derivative c * d).natDegree < 6 * n - 1 := by
    compute_degree; omega
  simp only [secondaryResidualRowZeroPolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1, h2,
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7,
    coeff_eq_zero_of_natDegree_lt hlow8, smul_eq_mul]
  push_cast
  ring

/-- The only terminal row-zero load is the displayed `zeta*A_top^3` term. -/
theorem cubicLoadRowZeroPolynomial68_coeff_terminalLoad_fiveToSix
    (alpha gamma epsilon zeta eta : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ g - 2 * n)
    (he : e.natDegree ≤ g - n) :
    (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (6 * n - 1) =
      (2 / 9 : k) * (n : k) * zeta * A.coeff (2 * n) ^ 3 := by
  let D0 : k[X] := (1 / 3 : k) • (A * B) + d
  let E0 : k[X] :=
    (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let R : k[X] :=
    (2 / 9 * gamma : k) • (B * derivative A * c) +
      (2 / 3 * gamma : k) • (B * derivative e) -
      (2 / 9 * gamma : k) • (A * derivative A * d) -
      (2 / 3 * gamma : k) • (d * derivative c) -
      (1 / 3 * epsilon : k) • (D0 * derivative A)
  have hloadEq :
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A B c D0 e = zeta • derivative E0 + R := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [cubicLoadRowZeroPolynomial68, cubicLoadUPolynomial68,
      cubicLoadVPolynomial68, D0, E0, R,
      zero_mul, zero_smul, smul_zero, add_zero, zero_add, sub_zero,
      derivative_add, derivative_sub, derivative_mul, derivative_pow,
      derivative_smul, derivative_C, one_mul, Polynomial.smul_eq_C_mul,
      map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
      RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
    ring
  have hD0 : D0.natDegree ≤ 5 * n - g := by
    simp only [D0]
    compute_degree
    omega
  have hRdeg : R.natDegree < 6 * n - 1 := by
    simp only [R]
    compute_degree
    omega
  have hA3 : (A ^ 3).coeff (6 * n) = A.coeff (2 * n) ^ 3 := by
    have h := coeff_pow_at_bound68 A (2 * n) 3 hA
    have hi : 3 * (2 * n) = 6 * n := by omega
    simpa only [hi] using h
  have hAclt : (A * c).natDegree < 6 * n := by
    compute_degree
    omega
  have helt : e.natDegree < 6 * n := by omega
  have hEtop : E0.coeff (6 * n) =
      (1 / 27 : k) * A.coeff (2 * n) ^ 3 := by
    simp only [E0, coeff_add, coeff_smul, smul_eq_mul, hA3,
      coeff_eq_zero_of_natDegree_lt hAclt,
      coeff_eq_zero_of_natDegree_lt helt, mul_zero, add_zero]
  have hEder := coeff_derivative_at_bound68 E0 (6 * n) (by omega)
  rw [hEtop] at hEder
  rw [hloadEq, coeff_add, coeff_smul, smul_eq_mul,
    coeff_eq_zero_of_natDegree_lt hRdeg, add_zero, hEder]
  push_cast
  ring

/-- Full source backwire at the symbolic load wall.  Row zero eliminates
`zeta`, leaving the honest zero-edge/all-nonzero-cusp dichotomy. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_terminalLoad68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hnLower : 10 < weightedRadius68 A B C0 D E)
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
      5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hdrop :
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
      d.natDegree ≤ g - 2 * n ∧ ee.natDegree ≤ g - n) :
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
    zeta = 0 ∧
      ((d.coeff (g - 2 * n) = 0 ∧ ee.coeff (g - n) = 0) ∨
        (Be.coeff (3 * n - g) ≠ 0 ∧
          ce.coeff (4 * n - g) ≠ 0 ∧
          d.coeff (g - 2 * n) ≠ 0 ∧ ee.coeff (g - n) ≠ 0 ∧
          Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
            3 * ce.coeff (4 * n - g) ^ 2 = 0)) := by
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
  change 10 < n at hnLower
  change 5 * n < 2 * g ∧ 2 * g ≤ 6 * n at hwindow
  change d.natDegree ≤ g - 2 * n ∧ ee.natDegree ≤ g - n at hdrop
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hgt3 : 3 * n < 2 * g := by omega
  have hlbeta :=
    maximalExpandedIntegratedPolynomialLowerSystem_l_beta_eq_zero_of_threeRadius_lt_twoGap68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hgt3)
  have hl : l = 0 := hlbeta.1
  have hbeta : beta = 0 := hlbeta.2
  obtain ⟨i4, hI4raw⟩ := data.invariant
  have hI4 := hI4raw
  rw [hl, hbeta] at hI4
  have hdelta :=
    cubicFirstIntegralFourPolynomial68_forces_delta_eq_zero_of_l_beta
      gamma delta epsilon zeta i4 Ae Be ce De ee n g data.hn data.hg
      hwindow.1 data.hA data.hB data.hc data.hD data.he data.ha hI4
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  obtain ⟨i3, hi3raw⟩ := hsys.firstThree
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3raw
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hl, hbeta, hdelta] at hi3e
  rw [hdelta] at hI4
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  rw [hDrec] at hI4 hi3e
  have hcoeff4 := congrArg (fun p : k[X] => p.coeff (2 * n)) hI4
  rw [cubicFirstIntegralFourPolynomial68_coeff_terminalLoad_fiveToSix
    gamma epsilon zeta Ae Be ce d ee n g data.hn hwindow
    data.hA data.hB data.hc hdrop.1 hdrop.2] at hcoeff4
  have hi4idx : 2 * n ≠ 0 := by omega
  simp only [coeff_C, if_neg hi4idx] at hcoeff4
  have hcoeff3 := congrArg (fun p : k[X] => p.coeff (3 * n)) hi3e
  rw [cubicFirstIntegralThreePolynomial68_coeff_terminalLoad_fiveToSix
    gamma epsilon zeta Ae Be ce d ee n g data.hn hwindow
    data.hA data.hB data.hc hdrop.1 hdrop.2] at hcoeff3
  have hi3idx : 3 * n ≠ 0 := by omega
  simp only [coeff_C, if_neg hi3idx] at hcoeff3
  have hrowZero : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee =
      C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowZeroPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have hzeroCoeff :=
    expand_lowerRowZeroPolynomial68_coeff_eq_zero_of_index_gt terminal
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee (6 * n - 1) hrowZero (by
          omega)
  rw [hl, hbeta, hdelta, hCrec, hErec, hDrec,
    cubicRowZeroPolynomial68_offsetSixty_residualSplit, coeff_add] at hzeroCoeff
  rw [secondaryResidualRowZeroPolynomial68_coeff_terminalLoad_fiveToSix
      Ae Be ce d ee n g data.hn hwindow data.hA data.hB data.hc
      hdrop.1 hdrop.2,
    cubicLoadRowZeroPolynomial68_coeff_terminalLoad_fiveToSix
      alpha gamma epsilon zeta eta Ae Be ce d ee n g data.hn hwindow
      data.hA data.hB data.hc hdrop.1 hdrop.2] at hzeroCoeff
  have hzetaCube : (n : k) * zeta * Ae.coeff (2 * n) ^ 3 = 0 := by
    linear_combination 3 * hzeroCoeff +
      (1 / 3 : k) * (n : k) * Ae.coeff (2 * n) ^ 2 * hcoeff4
  have hncast : (n : k) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt data.hn)
  have hzetaCube' : (n : k) *
      (zeta * Ae.coeff (2 * n) ^ 3) = 0 := by
    simpa only [mul_assoc] using hzetaCube
  have hza3 : zeta * Ae.coeff (2 * n) ^ 3 = 0 :=
    (mul_eq_zero.mp hzetaCube').resolve_left hncast
  have hzeta : zeta = 0 :=
    (mul_eq_zero.mp hza3).resolve_right (pow_ne_zero 3 data.ha)
  have hfour : Be.coeff (3 * n - g) * ee.coeff (g - n) +
      ce.coeff (4 * n - g) * d.coeff (g - 2 * n) = 0 := by
    rw [hzeta, zero_mul, add_zero] at hcoeff4
    exact (mul_eq_zero.mp hcoeff4).resolve_left (by norm_num)
  have hthree : -Ae.coeff (2 * n) * Be.coeff (3 * n - g) *
      d.coeff (g - 2 * n) +
      3 * ce.coeff (4 * n - g) * ee.coeff (g - n) = 0 := by
    have hz := (mul_eq_zero.mp hcoeff3).resolve_left (by norm_num)
    linear_combination hz
  have hmain :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_mainFamily68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change ee.coeff (6 * n - g) = 0 ∧
    Ae.coeff (2 * n) * Be.coeff (3 * n - g) =
      3 * De.coeff (5 * n - g) at hmain
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧
    ce.natDegree ≤ 4 * n - g ∧ De.natDegree ≤ 5 * n - g ∧
    ee.natDegree ≤ 6 * n - g ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0 ∨
      De.coeff (5 * n - g) ≠ 0 ∨ ee.coeff (6 * n - g) ≠ 0) at hsecondary
  have hold := firstSecondary_mainFamily_attainment_split68
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
    (ee.coeff (6 * n - g)) data.ha hmain hsecondary.2.2.2.2.2
  have hface : SecondaryResidualBetweenFace68
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (g - 2 * n))
      (ee.coeff (g - n)) := ⟨hfour, hthree⟩
  exact ⟨hzeta, firstSecondary_mainFamily_gapSucc_classify68
    (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
    (ee.coeff (6 * n - g)) (d.coeff (g - 2 * n))
    (ee.coeff (g - n)) data.ha hold hface⟩

/-- The apparent `(120,330)` radius alternative is impossible already at
the top face: both possible attained indices are outside expansion support. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_oneTwenty_threeThirty_impossible68
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
      n = 120 ∧ g = 330) : False := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change n = 120 ∧ g = 330 at hwall
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n := by omega
  have htop :=
    maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_B_or_c_top68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0 at htop
  have hBzero : Be.coeff (3 * n - g) = 0 := by
    simp only [Be, hwall.1, hwall.2]
    rw [coeff_expand (by norm_num : 0 < 60), if_neg]
    norm_num
  have hcexpand : ce = expand k 60 (cubicCDefectPolynomial68 A C0) := by
    simpa only [ce, Ae, Ce] using expand_cubicCDefectPolynomial68 60 A C0
  have hczero : ce.coeff (4 * n - g) = 0 := by
    rw [hcexpand]
    simp only [hwall.1, hwall.2]
    rw [coeff_expand (by norm_num : 0 < 60), if_neg]
    norm_num
  exact htop.elim (fun h => h hBzero) (fun h => h hczero)

/-- Refined global inventory: the offset-120 closure deletes `(120,360)`
and expansion support deletes `(120,330)`. -/
theorem integratedPolynomialLowerSystem68_global_terminalLoad_inventory
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
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
    FiveToSixGlobalResidual68 zeta Ae Be ce De ee d n g ∧
      ((n = 60 ∧ g = 180 ∧ 7 * n - 2 * g = 60) ∨
        (n = 90 ∧ g = 240 ∧ 7 * n - 2 * g = 150) ∨
        (n = 90 ∧ g = 270 ∧ 7 * n - 2 * g = 90) ∨ 120 < n) := by
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
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  change FiveToSixGlobalResidual68 zeta Ae Be ce De ee d n g at hglobal
  have hcases := hglobal.2.2.2.2.2.2.2.2.2.2.2.2
  change (n = 60 ∧ g = 180) ∨
    (n = 90 ∧ (g = 240 ∨ g = 270)) ∨
    (n = 120 ∧ g = 330) ∨ 120 < n at hcases
  refine ⟨hglobal, ?_⟩
  rcases hcases with h60 | h90 | h120 | hbig
  · obtain ⟨hn60, hg180⟩ := h60
    have hr60 : 7 * n - 2 * g = 60 := by omega
    left
    exact ⟨hn60, hg180, hr60⟩
  · obtain ⟨hn90, hg240 | hg270⟩ := h90
    · have hr150 : 7 * n - 2 * g = 150 := by omega
      right; left
      exact ⟨hn90, hg240, hr150⟩
    · have hr90 : 7 * n - 2 * g = 90 := by omega
      right; right; left
      exact ⟨hn90, hg270, hr90⟩
  · exact False.elim
      (maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_oneTwenty_threeThirty_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using h120))
  · right; right; right; exact hbig

#print axioms cubicFirstIntegralFourPolynomial68_coeff_terminalLoad_fiveToSix
#print axioms cubicFirstIntegralThreePolynomial68_coeff_terminalLoad_fiveToSix
#print axioms secondaryResidualRowZeroPolynomial68_coeff_terminalLoad_fiveToSix
#print axioms cubicLoadRowZeroPolynomial68_coeff_terminalLoad_fiveToSix
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_terminalLoad68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_oneTwenty_threeThirty_impossible68
#print axioms integratedPolynomialLowerSystem68_global_terminalLoad_inventory

end FiveToSixTerminalLoadStride68

end Max11DegreeRoutes
