import LowScale68SecondaryLaterDeepPreclampedLowerEndgame

/-! # The lower coefficient in the strict six-to-seven chamber

After the first secondary packet leaves only `c_top`, the exact I4 identity
drops `D` to degree `g-2n`.  The next I3 and row-one coefficients kill that
new edge; I4 then forces `zeta=0` and `D=0`, contradicting the nonzero
terminal row.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepSixToSevenLowerCoefficient68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 10000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Once I4 has dropped `D` to `g-2n`, I3 drops `e` to `3g-8n`. -/
theorem cubicFirstIntegralThreePolynomial68_c_top_forces_e_degree_drop
    (gamma epsilon zeta i3 : k) (A c D e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 6 * n < 2 * g ∧ 2 * g < 7 * n)
    (hc : c.natDegree ≤ 4 * n - g)
    (hcTop : c.coeff (4 * n - g) ≠ 0)
    (hD : D.natDegree ≤ g - 2 * n)
    (hI3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon zeta A 0 c D e = C i3) :
    e.natDegree ≤ 3 * g - 8 * n := by
  let m := 4 * n - g
  let s : k[X] := (2 / 3 : k) • c + C gamma
  have hm : 0 < m := by dsimp only [m]; omega
  have hsle : s.natDegree ≤ m := by
    simp only [s]
    compute_degree
    omega
  have hscoeff : s.coeff m = (2 / 3 : k) * c.coeff m := by
    simp only [s, coeff_add, coeff_smul, coeff_C,
      if_neg (Nat.ne_of_gt hm), add_zero, smul_eq_mul]
  have hscoeff0 : s.coeff m ≠ 0 := by
    rw [hscoeff]
    exact mul_ne_zero (by norm_num) (by simpa only [m] using hcTop)
  have hsdeg : s.natDegree = m :=
    natDegree_eq_of_le_of_coeff_ne_zero hsle hscoeff0
  have hs0 : s ≠ 0 := by
    intro hz
    rw [hz, coeff_zero] at hscoeff0
    exact hscoeff0 rfl
  by_cases he0 : e = 0
  · rw [he0, natDegree_zero]
    omega
  · have hEq : (4 : k) • (s * e) =
        C i3 - (4 / 3 : k) • D ^ 2 - (2 * epsilon : k) • c := by
      rw [← hI3]
      apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
      simp only [s, cubicFirstIntegralThreePolynomial68,
        Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
        map_neg, map_zero, RatFunc.algebraMap_C]
      simp only [map_div₀, map_ofNat, map_natCast, map_one]
      ring
    have hrhs :
        (C i3 - (4 / 3 : k) • D ^ 2 - (2 * epsilon : k) • c).natDegree ≤
          2 * g - 4 * n := by
      compute_degree
      omega
    have hdegree : m + e.natDegree ≤ 2 * g - 4 * n := by
      calc
        m + e.natDegree = (s * e).natDegree := by
          rw [natDegree_mul hs0 he0, hsdeg]
        _ = ((4 : k) • (s * e)).natDegree := by
          rw [natDegree_smul _ (by norm_num : (4 : k) ≠ 0)]
        _ = (C i3 - (4 / 3 : k) • D ^ 2 -
              (2 * epsilon : k) • c).natDegree := congrArg natDegree hEq
        _ ≤ 2 * g - 4 * n := hrhs
    dsimp only [m] at hdegree
    omega

/-- The next I3 coefficient after the degree drops. -/
theorem cubicFirstIntegralThreePolynomial68_sixToSeven_lower_edge
    (gamma epsilon zeta i3 : k) (A c D e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 6 * n < 2 * g ∧ 2 * g < 7 * n)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ g - 2 * n)
    (he : e.natDegree ≤ 3 * g - 8 * n)
    (hI3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon zeta A 0 c D e = C i3) :
    D.coeff (g - 2 * n) ^ 2 +
      2 * c.coeff (4 * n - g) * e.coeff (3 * g - 8 * n) = 0 := by
  let j := 2 * g - 4 * n
  have hD2 : (D ^ 2).coeff j = D.coeff (g - 2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 D (g - 2 * n) 2 hD
    have hj : 2 * (g - 2 * n) = j := by dsimp only [j]; omega
    simpa only [hj] using h
  have hce : (c * e).coeff j =
      c.coeff (4 * n - g) * e.coeff (3 * g - 8 * n) := by
    have h := coeff_mul_at_bounds68 c e (4 * n - g)
      (3 * g - 8 * n) hc he
    have hj : (4 * n - g) + (3 * g - 8 * n) = j := by
      dsimp only [j]
      omega
    simpa only [hj] using h
  have hclt : c.natDegree < j := by dsimp only [j]; omega
  have helt : e.natDegree < j := by dsimp only [j]; omega
  have hcoeff := congrArg (fun p : k[X] ↦ p.coeff j) hI3
  have hzero2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by norm_num)
  simp only [cubicFirstIntegralThreePolynomial68, hzero2, zero_smul,
    smul_zero, zero_mul, mul_zero, add_zero, zero_add, sub_zero,
    coeff_add, coeff_sub, coeff_smul, hD2, hce,
    coeff_eq_zero_of_natDegree_lt hclt,
    coeff_eq_zero_of_natDegree_lt helt, smul_eq_mul] at hcoeff
  have hj0 : j ≠ 0 := by dsimp only [j]; omega
  simp only [coeff_C, if_neg hj0] at hcoeff
  linear_combination (3 / 4 : k) * hcoeff

/-- Row one at the same lower edge. -/
theorem lowerRowOnePolynomial68_sixToSeven_lower_edge
    (alpha gamma epsilon zeta eta : k) (A c D e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 6 * n < 2 * g ∧ 2 * g < 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ g - 2 * n)
    (he : e.natDegree ≤ 3 * g - 8 * n)
    (hrow : lowerRowOnePolynomial68
      (integratedTPolynomial68 0 alpha 0 gamma epsilon A 0
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedUPolynomial68 0 alpha 0 gamma 0 zeta A 0
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta A 0
        ((1 / 3 : k) • A ^ 2 + c) D
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
      ((1 / 3 : k) • A ^ 2 + c) D
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) = 0) :
    (8 / 9 : k) * A.coeff (2 * n) * c.coeff (4 * n - g) *
        e.coeff (3 * g - 8 * n) * (((3 * g - 8 * n : ℕ) : k)) +
      (8 / 9 : k) * A.coeff (2 * n) * e.coeff (3 * g - 8 * n) *
        c.coeff (4 * n - g) * (((4 * n - g : ℕ) : k)) -
      (4 / 9 : k) * D.coeff (g - 2 * n) ^ 2 *
        A.coeff (2 * n) * (((2 * n : ℕ) : k)) = 0 := by
  let j := 2 * g - 2 * n - 1
  have hcpos : 0 < 4 * n - g := by omega
  have hepos : 0 < 3 * g - 8 * n := by omega
  have hApos : 0 < 2 * n := by omega
  have hAce : (A * c * derivative e).coeff j =
      A.coeff (2 * n) * c.coeff (4 * n - g) *
        e.coeff (3 * g - 8 * n) * (((3 * g - 8 * n : ℕ) : k)) := by
    have h := coeff_mul_mul_derivative_at_bounds68 A c e (2 * n)
      (4 * n - g) (3 * g - 8 * n) hepos hA hc he
    have hj : 2 * n + (4 * n - g) + (3 * g - 8 * n) - 1 = j := by
      dsimp only [j]
      omega
    simpa only [hj, mul_assoc] using h
  have hAec : (A * e * derivative c).coeff j =
      A.coeff (2 * n) * e.coeff (3 * g - 8 * n) *
        c.coeff (4 * n - g) * (((4 * n - g : ℕ) : k)) := by
    have h := coeff_mul_mul_derivative_at_bounds68 A e c (2 * n)
      (3 * g - 8 * n) (4 * n - g) hcpos hA he hc
    have hj : 2 * n + (3 * g - 8 * n) + (4 * n - g) - 1 = j := by
      dsimp only [j]
      omega
    simpa only [hj, mul_assoc] using h
  have hD2A : (D ^ 2 * derivative A).coeff j =
      D.coeff (g - 2 * n) ^ 2 * A.coeff (2 * n) *
        (((2 * n : ℕ) : k)) := by
    have h := coeff_mul_mul_derivative_at_bounds68 D D A (g - 2 * n)
      (g - 2 * n) (2 * n) hApos hD hD hA
    have hj : (g - 2 * n) + (g - 2 * n) + 2 * n - 1 = j := by
      dsimp only [j]
      omega
    simpa only [hj, pow_two, mul_assoc] using h
  have lower (p : k[X]) (hp : p.natDegree < j) : p.coeff j = 0 :=
    coeff_eq_zero_of_natDegree_lt hp
  have hAc : (A * derivative c).natDegree < j := by compute_degree; omega
  have hAe : (A * derivative e).natDegree < j := by compute_degree; omega
  have hc2c : (c ^ 2 * derivative c).natDegree < j := by
    compute_degree
    omega
  have hcc : (c * derivative c).natDegree < j := by compute_degree; omega
  have hee : (e * derivative e).natDegree < j := by compute_degree; omega
  have hDder : (derivative D).natDegree < j := by compute_degree; omega
  have heder : (derivative e).natDegree < j := by compute_degree; omega
  have hcoeff := congrArg (fun p : k[X] ↦ p.coeff j) hrow
  rw [lowerRowOnePolynomial68_B_zero_exact] at hcoeff
  simp only [coeff_add, coeff_sub, coeff_smul, hAce, hAec, hD2A,
    lower _ hAc, lower _ hAe, lower _ hc2c, lower _ hcc,
    lower _ hee, lower _ hDder, lower _ heder,
    smul_eq_mul, zero_add, add_zero, zero_sub, sub_zero, coeff_zero]
      at hcoeff
  simpa only [mul_zero, zero_mul, zero_add, add_zero, sub_zero,
    mul_assoc] using hcoeff

/-- The I3 and row-one lower-edge scalars force the new `D` edge to
vanish. -/
theorem sixToSeven_i3_rowOne_forces_D_lower_top_zero68
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 6 * n < 2 * g ∧ 2 * g < 7 * n)
    (a c d e : k) (ha : a ≠ 0) (hc : c ≠ 0)
    (hi3 : d ^ 2 + 2 * c * e = 0)
    (hrow :
      (8 / 9 : k) * a * c * e * (((3 * g - 8 * n : ℕ) : k)) +
        (8 / 9 : k) * a * e * c * (((4 * n - g : ℕ) : k)) -
        (4 / 9 : k) * d ^ 2 * a * (((2 * n : ℕ) : k)) = 0) :
    d = 0 := by
  have h8 : 8 * n ≤ 3 * g := by omega
  have hg4 : g ≤ 4 * n := by omega
  have h2 : 2 * n ≤ g := by omega
  have hnG : n ≤ g := by omega
  rw [Nat.cast_sub h8, Nat.cast_sub hg4] at hrow
  push_cast at hrow
  have hfactor : (-8 / 9 : k) * a * d ^ 2 *
      (((g - n : ℕ) : k)) = 0 := by
    rw [Nat.cast_sub hnG]
    push_cast
    linear_combination hrow -
      (8 / 9 : k) * a * ((g : k) - 2 * (n : k)) * hi3
  have hgn : (((g - n : ℕ) : k)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < g - n))
  have hd2 : d ^ 2 = 0 := by
    rcases mul_eq_zero.mp hfactor with hnum | hgn0
    · rcases mul_eq_zero.mp hnum with hratA | hd2
      · rcases mul_eq_zero.mp hratA with hrat | ha'
        · exact (by norm_num at hrat)
        · exact (ha ha').elim
      · exact hd2
    · exact (hgn hgn0).elim
  exact eq_zero_of_pow_eq_zero hd2

/-- Once the new `D` edge vanishes, the degree-`2n` I4 coefficient forces
the remaining load `zeta` to vanish. -/
theorem cubicFirstIntegralFourPolynomial68_sixToSeven_forces_zeta_zero
    (gamma epsilon zeta i4 : k) (A c D e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 6 * n < 2 * g ∧ 2 * g < 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (ha : A.coeff (2 * n) ≠ 0)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ g - 2 * n)
    (hDTop : D.coeff (g - 2 * n) = 0)
    (hI4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A 0 c D e = C i4) :
    zeta = 0 := by
  have hrpos : 0 < g - 2 * n := by omega
  have hD' : D.natDegree < g - 2 * n :=
    natDegree_lt_of_le_of_coeff_eq_zero68 D (g - 2 * n) hrpos hD hDTop
  have hDc : (D * c).natDegree < 2 * n := by
    compute_degree
    omega
  have hDlt : D.natDegree < 2 * n := by omega
  have hcoeff := congrArg (fun p : k[X] ↦ p.coeff (2 * n)) hI4
  have hzero3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by norm_num)
  simp only [cubicFirstIntegralFourPolynomial68, hzero3, zero_smul,
    smul_zero, zero_mul, mul_zero, add_zero, zero_add, sub_zero,
    coeff_add, coeff_sub, coeff_smul,
    coeff_eq_zero_of_natDegree_lt hDc,
    coeff_eq_zero_of_natDegree_lt hDlt, smul_eq_mul] at hcoeff
  have hi : 2 * n ≠ 0 := by omega
  simp only [coeff_C, if_neg hi, mul_zero, zero_mul, zero_add, add_zero]
    at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_right ha

/-- With `zeta=0`, exact I4 says that `D` times the nonconstant polynomial
`(2/3)c+gamma` is constant, hence `D=0`. -/
theorem cubicFirstIntegralFourPolynomial68_sixToSeven_forces_D_zero
    (gamma epsilon i4 : k) (A c D e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 6 * n < 2 * g ∧ 2 * g < 7 * n)
    (hc : c.natDegree ≤ 4 * n - g)
    (hcTop : c.coeff (4 * n - g) ≠ 0)
    (hI4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon 0 A 0 c D e = C i4) :
    D = 0 := by
  let m := 4 * n - g
  let s : k[X] := (2 / 3 : k) • c + C gamma
  have hm : 0 < m := by dsimp only [m]; omega
  have hsle : s.natDegree ≤ m := by
    simp only [s]
    compute_degree
    omega
  have hscoeff : s.coeff m = (2 / 3 : k) * c.coeff m := by
    simp only [s, coeff_add, coeff_smul, coeff_C,
      if_neg (Nat.ne_of_gt hm), add_zero, smul_eq_mul]
  have hscoeff0 : s.coeff m ≠ 0 := by
    rw [hscoeff]
    exact mul_ne_zero (by norm_num) (by simpa only [m] using hcTop)
  have hsdeg : s.natDegree = m :=
    natDegree_eq_of_le_of_coeff_ne_zero hsle hscoeff0
  have hs0 : s ≠ 0 := by
    intro hz
    rw [hz, coeff_zero] at hscoeff0
    exact hscoeff0 rfl
  by_contra hD0
  have hEq : (4 : k) • (D * s) = C i4 := by
    rw [← hI4]
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [s, cubicFirstIntegralFourPolynomial68,
      Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
      map_neg, map_zero, RatFunc.algebraMap_C]
    simp only [map_div₀, map_ofNat, map_natCast, map_one]
    ring
  have hdegree : D.natDegree + m ≤ 0 := by
    calc
      D.natDegree + m = (D * s).natDegree := by
        rw [natDegree_mul hD0 hs0, hsdeg]
      _ = ((4 : k) • (D * s)).natDegree := by
        rw [natDegree_smul _ (by norm_num : (4 : k) ≠ 0)]
      _ = (C i4).natDegree := congrArg natDegree hEq
      _ ≤ 0 := by compute_degree
  omega

set_option maxHeartbeats 16000000 in
/-- The strict chamber `6n < 2g < 7n` is empty. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_sixToSeven_empty68
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
      6 * n < 2 * g ∧ 2 * g < 7 * n) : False := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 6 * n < 2 * g ∧ 2 * g < 7 * n at hwindow
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hclass :=
    maximalExpandedIntegratedPolynomialLowerSystem_sixToSeven_c_only_top68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwindow)
  change Be = 0 ∧ ce.coeff (4 * n - g) ≠ 0 ∧
    De.coeff (5 * n - g) = 0 ∧ ee.coeff (6 * n - g) = 0 at hclass
  have hBe : Be = 0 := hclass.1
  have hcTop : ce.coeff (4 * n - g) ≠ 0 := hclass.2.1
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
  rw [hdelta, hBe] at hI4
  have hDnew : De.natDegree ≤ g - 2 * n := by
    by_cases hD0 : De = 0
    · rw [hD0, natDegree_zero]
      omega
    · exact cubicFirstIntegralFourPolynomial68_c_top_forces_D_degree_drop
        gamma epsilon zeta i4 Ae ce De ee n g data.hn hwindow data.hA
        data.hc hcTop hD0 hI4
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec : Ee = (1 / 27 : k) • Ae ^ 3 +
      (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using cubicEDefectPolynomial68_eq_cubicCoordinates
      Ae Ce Ee
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hl, hbeta, hdelta, hBe] at hi3e
  have heNew :=
    cubicFirstIntegralThreePolynomial68_c_top_forces_e_degree_drop
      gamma epsilon zeta i3 Ae ce De ee n g data.hn hwindow data.hc
      hcTop hDnew hi3e
  have hface3 := cubicFirstIntegralThreePolynomial68_sixToSeven_lower_edge
    gamma epsilon zeta i3 Ae ce De ee n g data.hn hwindow data.hc
    hDnew heNew hi3e
  have hrowOne : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowOnePolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hl, hbeta, hdelta, hBe, hCrec, hErec] at hrowOne
  have hrowFace := lowerRowOnePolynomial68_sixToSeven_lower_edge
    alpha gamma epsilon zeta eta Ae ce De ee n g data.hn hwindow data.hA
    data.hc hDnew heNew hrowOne
  have hDTop : De.coeff (g - 2 * n) = 0 :=
    sixToSeven_i3_rowOne_forces_D_lower_top_zero68 n g data.hn hwindow
      (Ae.coeff (2 * n)) (ce.coeff (4 * n - g))
      (De.coeff (g - 2 * n)) (ee.coeff (3 * g - 8 * n))
      data.ha hcTop hface3 hrowFace
  have hzeta :=
    cubicFirstIntegralFourPolynomial68_sixToSeven_forces_zeta_zero
      gamma epsilon zeta i4 Ae ce De ee n g data.hn hwindow data.hA data.ha
      data.hc hDnew hDTop hI4
  rw [hzeta] at hI4
  have hDzero :=
    cubicFirstIntegralFourPolynomial68_sixToSeven_forces_D_zero
      gamma epsilon i4 Ae ce De ee n g data.hn hwindow data.hc hcTop hI4
  have hrowZero : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee =
      C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowZeroPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hl, hbeta, hdelta, hzeta, hBe, hDzero] at hrowZero
  simp only [integratedUPolynomial68, lowerRowZeroPolynomial68, zero_smul,
    smul_zero, zero_mul, mul_zero, add_zero, zero_add, sub_zero, C_0]
      at hrowZero
  have hrhs : C terminal * (60 * (X ^ 59 : k[X])) ≠ 0 := by
    apply mul_ne_zero
    · simpa only [C_ne_zero] using hterminal
    · exact mul_ne_zero (by norm_num) (pow_ne_zero 59 X_ne_zero)
  exact hrhs hrowZero.symm

end LaterDeepSixToSevenLowerCoefficient68

#print axioms cubicFirstIntegralThreePolynomial68_c_top_forces_e_degree_drop
#print axioms cubicFirstIntegralThreePolynomial68_sixToSeven_lower_edge
#print axioms lowerRowOnePolynomial68_sixToSeven_lower_edge
#print axioms sixToSeven_i3_rowOne_forces_D_lower_top_zero68
#print axioms cubicFirstIntegralFourPolynomial68_sixToSeven_forces_zeta_zero
#print axioms cubicFirstIntegralFourPolynomial68_sixToSeven_forces_D_zero
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_sixToSeven_empty68

end Max11DegreeRoutes
