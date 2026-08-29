import LowScale68SecondaryLaterDeepLoadCascade

/-! # The mixed degree-`2n` face in the later `(6,8)` deep chamber

For `8n ≤ 2g`, the secondary bounds clamp both `B` and `c` to constants.
The cubic invariant at degree `4n` first forces `B=0`; the quartic invariant
at degree `2n` then forces `zeta=0`, including the wall contribution `B*e`
when `2g=8n`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepMixedTwoNFace68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- In the clamped chamber the only degree-`4n` term in I3 is
`(4/9) A²B²`. -/
theorem cubicFirstIntegralThreePolynomial68_coeff_fourRadius_of_clamped
    (gamma epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hdeep : 8 * n ≤ 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
      A B c D e).coeff (4 * n) =
      (4 / 9 : k) * A.coeff (2 * n) ^ 2 * B.coeff 0 ^ 2 := by
  have hB0 : B.natDegree ≤ 0 := by omega
  have hc0 : c.natDegree ≤ 0 := by omega
  have hA2 : (A ^ 2).natDegree ≤ 4 * n := by
    compute_degree
    omega
  have hB2 : (B ^ 2).natDegree ≤ 0 := by
    compute_degree
    omega
  have hA2B2 : (A ^ 2 * B ^ 2).coeff (4 * n) =
      A.coeff (2 * n) ^ 2 * B.coeff 0 ^ 2 := by
    have h := coeff_mul_at_bounds68 (A ^ 2) (B ^ 2) (4 * n) 0 hA2 hB2
    have hAcoeff : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
      have hp := coeff_pow_at_bound68 A (2 * n) 2 hA
      have hfour : 2 * (2 * n) = 4 * n := by omega
      rw [hfour] at hp
      exact hp
    have hBcoeff : (B ^ 2).coeff 0 = B.coeff 0 ^ 2 := by
      simpa only [Nat.mul_zero] using coeff_pow_at_bound68 B 0 2 hB0
    rw [hAcoeff, hBcoeff] at h
    simpa only [Nat.add_zero, Nat.mul_zero] using h
  have lower (p : k[X]) (hp : p.natDegree < 4 * n) :
      p.coeff (4 * n) = 0 := coeff_eq_zero_of_natDegree_lt hp
  have hABD : (A * B * D).natDegree < 4 * n := by
    compute_degree
    omega
  have hB2c : (B ^ 2 * c).natDegree < 4 * n := by
    compute_degree
    omega
  have hD2 : (D ^ 2).natDegree < 4 * n := by
    compute_degree
    omega
  have hce : (c * e).natDegree < 4 * n := by
    compute_degree
    omega
  have hload : (secondaryLoadInvariantThreePolynomial68
      0 0 gamma 0 epsilon zeta A B c D e).natDegree < 4 * n := by
    simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, mul_zero,
      zero_smul, smul_zero, add_zero, sub_zero]
    compute_degree
    omega
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit, coeff_add,
    coeff_eq_zero_of_natDegree_lt hload, add_zero]
  simp only [cubicFirstIntegralThreePolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero, coeff_add, coeff_sub,
    coeff_smul, hA2B2, lower _ hABD, lower _ hB2c, lower _ hD2,
    lower _ hce, smul_eq_mul]
  ring

/-- Exact degree-`2n` I4 coefficient.  The `B*e` term is retained, so the
same formula covers both `2g=8n` and the strict chamber beyond it. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_twoRadius_of_clamped
    (gamma epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hdeep : 8 * n ≤ 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c D e).coeff (2 * n) =
      (-8 / 9 : k) * A.coeff (2 * n) * B.coeff 0 * c.coeff 0 +
        (8 / 3 : k) * B.coeff 0 * e.coeff (2 * n) +
        zeta * A.coeff (2 * n) -
        (4 / 3 * gamma : k) * A.coeff (2 * n) * B.coeff 0 := by
  have hB0 : B.natDegree ≤ 0 := by omega
  have hc0 : c.natDegree ≤ 0 := by omega
  have hABC : (A * B * c).coeff (2 * n) =
      A.coeff (2 * n) * B.coeff 0 * c.coeff 0 := by
    have h := coeff_mul_mul_at_bounds68 A B c (2 * n) 0 0 hA hB0 hc0
    simpa only [add_zero] using h
  have hBe : (B * e).coeff (2 * n) =
      B.coeff 0 * e.coeff (2 * n) := by
    have h := coeff_mul_at_bounds68 B e 0 (2 * n) hB0
      (he.trans (by omega))
    simpa only [zero_add] using h
  have hAB : (A * B).coeff (2 * n) =
      A.coeff (2 * n) * B.coeff 0 := by
    have h := coeff_mul_at_bounds68 A B (2 * n) 0 hA hB0
    simpa only [add_zero] using h
  have hB3 : (B ^ 3).natDegree < 2 * n := by
    compute_degree
    omega
  have hDc : (D * c).natDegree < 2 * n := by
    compute_degree
    omega
  have hBload : B.natDegree < 2 * n := hB0.trans_lt (by omega)
  have hDload : D.natDegree < 2 * n := by omega
  simp only [cubicFirstIntegralFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero, coeff_add, coeff_sub,
    coeff_smul, hABC, hBe, hAB, coeff_eq_zero_of_natDegree_lt hB3,
    coeff_eq_zero_of_natDegree_lt hDc,
    coeff_eq_zero_of_natDegree_lt hBload,
    coeff_eq_zero_of_natDegree_lt hDload, smul_eq_mul]
  ring

/-- The two exact invariants force the next two loads to vanish in the whole
clamped chamber. -/
theorem cubicInvariants68_clamped_force_B_zeta_zero
    (gamma epsilon zeta i4 i3 : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hdeep : 8 * n ≤ 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hI4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A B c D e = C i4)
    (hI3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon zeta A B c D e = C i3) :
    B = 0 ∧ zeta = 0 := by
  have hcoeff3 := congrArg (fun p : k[X] => p.coeff (4 * n)) hI3
  rw [cubicFirstIntegralThreePolynomial68_coeff_fourRadius_of_clamped
    gamma epsilon zeta A B c D e n g hn hdeep hA hB hc hD he] at hcoeff3
  have hi4n : 4 * n ≠ 0 := by omega
  simp only [coeff_C, if_neg hi4n] at hcoeff3
  have ha2 : A.coeff (2 * n) ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have hb2 : B.coeff 0 ^ 2 = 0 := by
    have hs : (4 / 9 : k) * A.coeff (2 * n) ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) ha2
    exact (mul_eq_zero.mp hcoeff3).resolve_left hs
  have hb0 : B.coeff 0 = 0 := eq_zero_of_pow_eq_zero hb2
  have hBdeg : B.natDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    omega
  obtain ⟨b, hBconst⟩ := natDegree_eq_zero.mp hBdeg
  have hb : b = 0 := by
    have := congrArg (fun p : k[X] => p.coeff 0) hBconst
    simpa [coeff_C] using this.trans hb0
  have hBzero : B = 0 := by
    calc
      B = C b := hBconst.symm
      _ = 0 := by rw [hb, C_0]
  have hcoeff4 := congrArg (fun p : k[X] => p.coeff (2 * n)) hI4
  rw [cubicFirstIntegralFourPolynomial68_coeff_twoRadius_of_clamped
    gamma epsilon zeta A B c D e n g hn hdeep hA hB hc hD he] at hcoeff4
  have hi2n : 2 * n ≠ 0 := by omega
  simp only [coeff_C, if_neg hi2n, hBzero, coeff_zero, mul_zero,
    zero_mul, zero_add, add_zero, sub_zero] at hcoeff4
  exact ⟨hBzero, (mul_eq_zero.mp hcoeff4).resolve_right ha⟩

set_option maxHeartbeats 6000000 in
/-- Canonical expanded endpoint for the mixed degree-`2n` face. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_clamped_B_zeta_zero68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hdeep :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      8 * n ≤ 2 * g) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    l = 0 ∧ beta = 0 ∧ delta = 0 ∧ Be = 0 ∧ zeta = 0 := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 8 * n ≤ 2 * g at hdeep
  change l = 0 ∧ beta = 0 ∧ delta = 0 ∧ Be = 0 ∧ zeta = 0
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hn : 0 < n := data.hn
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
      gamma delta epsilon zeta i4 Ae Be ce De ee n g data.hn data.hg
      (by omega) data.hA data.hB data.hc data.hD data.he data.ha hI4
  rw [hdelta] at hI4
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using cubicEDefectPolynomial68_eq_cubicCoordinates
      Ae Ce Ee
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hl, hbeta, hdelta] at hi3e
  have hvanish := cubicInvariants68_clamped_force_B_zeta_zero
    gamma epsilon zeta i4 i3 Ae Be ce De ee n g data.hn hdeep
    data.hA data.hB data.hc data.hD data.he data.ha hI4 hi3e
  exact ⟨hl, hbeta, hdelta, hvanish.1, hvanish.2⟩

end LaterDeepMixedTwoNFace68

#print axioms cubicFirstIntegralThreePolynomial68_coeff_fourRadius_of_clamped
#print axioms cubicFirstIntegralFourPolynomial68_coeff_twoRadius_of_clamped
#print axioms cubicInvariants68_clamped_force_B_zeta_zero
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_clamped_B_zeta_zero68

end Max11DegreeRoutes
