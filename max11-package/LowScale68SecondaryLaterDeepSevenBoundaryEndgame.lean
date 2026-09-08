import LowScale68SecondaryLaterDeepSixToSevenLowerCoefficient

/-! # The exact seven-radius boundary

This file adds the terminal-row scalar to the existing I4/I3/row-one wall
packet at `2g=7n`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepSevenBoundary68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 12000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The terminal row at degree `6n-1` on `2g=7n`.  All alpha pieces
cancel; the only load contribution is the top of `zeta * E'`. -/
theorem lowerRowZeroPolynomial68_sevenRadiusWall_relation
    (alpha gamma epsilon zeta eta : k) (A c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hwall : 2 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hrowCoeff :
      (lowerRowZeroPolynomial68
        (integratedUPolynomial68 0 alpha 0 gamma 0 zeta A 0
          ((1 / 3 : k) • A ^ 2 + c) D
          ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
        (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta A 0
          ((1 / 3 : k) • A ^ 2 + c) D
          ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e))
        D ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).coeff
          (6 * n - 1) = 0) :
    (4 / 81 : k) *
        (-3 * A.coeff (2 * n) * D.coeff (5 * n - g) *
            c.coeff (4 * n - g) * A.coeff (2 * n) *
              (((2 * n : ℕ) : k)) -
          9 * D.coeff (5 * n - g) * e.coeff (6 * n - g) *
            A.coeff (2 * n) * (((2 * n : ℕ) : k))) +
      (1 / 27 : k) * zeta * A.coeff (2 * n) ^ 3 *
        (((6 * n : ℕ) : k)) = 0 := by
  let E0 : k[X] :=
    (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let W : k[X] :=
    (1 / 9 * gamma : k) • A ^ 2 + (2 / 3 * gamma : k) • c +
      (1 / 3 * epsilon : k) • A + C eta
  have hcoords := integratedPolynomial68_cubicCoordinates
    (0 : k) alpha 0 gamma 0 epsilon zeta eta A 0 c D e
  have hu := hcoords.u_eq
  have hv := hcoords.v_eq
  change integratedUPolynomial68 0 alpha 0 gamma 0 zeta A 0
      ((1 / 3 : k) • A ^ 2 + c) D E0 = _ at hu
  change integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta A 0
      ((1 / 3 : k) • A ^ 2 + c) D E0 = _ at hv
  change (lowerRowZeroPolynomial68 _ _ D E0).coeff (6 * n - 1) = 0
    at hrowCoeff
  rw [hu, hv, cubicRowZeroPolynomial68_split,
    cubicHomogeneousRowZeroPolynomial68_eq_expanded,
    cubicHomogeneousRowZeroExpandedPolynomial68, coeff_add, coeff_add]
      at hrowCoeff
  have hApos : 0 < 2 * n := by omega
  have hADcA : (A * D * c * derivative A).coeff (6 * n - 1) =
      A.coeff (2 * n) * D.coeff (5 * n - g) *
        c.coeff (4 * n - g) * A.coeff (2 * n) *
          (((2 * n : ℕ) : k)) := by
    have h := coeff_mul_mul_mul_derivative_at_bounds68 A D c A
      (2 * n) (5 * n - g) (4 * n - g) (2 * n) hApos hA hD hc hA
    have hi : 2 * n + (5 * n - g) + (4 * n - g) + 2 * n - 1 =
        6 * n - 1 := by omega
    simpa only [hi] using h
  have hDeA : (D * e * derivative A).coeff (6 * n - 1) =
      D.coeff (5 * n - g) * e.coeff (6 * n - g) *
        A.coeff (2 * n) * (((2 * n : ℕ) : k)) := by
    have h := coeff_mul_mul_derivative_at_bounds68 D e A
      (5 * n - g) (6 * n - g) (2 * n) hApos hD he hA
    have hi : (5 * n - g) + (6 * n - g) + 2 * n - 1 =
        6 * n - 1 := by omega
    simpa only [hi] using h
  have hcore :
      (firstSecondaryCoreRowZeroPolynomial68 A 0 c D e).coeff (6 * n - 1) =
        (4 / 81 : k) *
          (-3 * A.coeff (2 * n) * D.coeff (5 * n - g) *
              c.coeff (4 * n - g) * A.coeff (2 * n) *
                (((2 * n : ℕ) : k)) -
            9 * D.coeff (5 * n - g) * e.coeff (6 * n - g) *
              A.coeff (2 * n) * (((2 * n : ℕ) : k))) := by
    simp only [firstSecondaryCoreRowZeroPolynomial68, zero_mul, mul_zero,
      zero_smul, zero_add, coeff_smul, coeff_sub, hADcA, hDeA,
      smul_eq_mul, coeff_zero]
    ring
  have hremdeg :
      (cubicRemainderRowZeroPolynomial68 A 0 c D e).natDegree <
        6 * n - 1 := by
    simp only [cubicRemainderRowZeroPolynomial68, zero_mul, mul_zero,
      zero_smul, smul_zero, zero_pow, add_zero, zero_add, sub_zero]
    compute_degree
    omega
  have hUl : cubicLoadUPolynomial68 0 alpha 0 gamma 0 zeta
      A 0 c D e = alpha • D + C zeta := by
    simp [cubicLoadUPolynomial68]
  have hVl : cubicLoadVPolynomial68 0 alpha 0 gamma 0 epsilon eta
      A 0 c D e = alpha • E0 + W := by
    simp only [E0, W, cubicLoadVPolynomial68, zero_mul, zero_smul,
      smul_zero, zero_add, add_zero]
    module
  have hloadEq :
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A 0 c D e = zeta • derivative E0 - D * derivative W := by
    rw [cubicLoadRowZeroPolynomial68, hUl, hVl]
    change (alpha • D + C zeta) * derivative E0 -
      D * derivative (alpha • E0 + W) =
        zeta • derivative E0 - D * derivative W
    simp only [derivative_add]
    simp only [derivative_smul]
    simp only [Polynomial.smul_eq_C_mul]
    ring
  have hWdeg : (D * derivative W).natDegree < 6 * n - 1 := by
    have hW : W.natDegree ≤ 4 * n := by
      simp only [W]
      compute_degree
      omega
    have hWder : (derivative W).natDegree < 4 * n := by
      compute_degree
      omega
    compute_degree
    omega
  have hA3 : (A ^ 3).coeff (6 * n) = A.coeff (2 * n) ^ 3 := by
    have h := coeff_pow_at_bound68 A (2 * n) 3 hA
    have hi : 3 * (2 * n) = 6 * n := by omega
    simpa only [hi] using h
  have hAclt : (A * c).natDegree < 6 * n := by compute_degree; omega
  have helt : e.natDegree < 6 * n := by omega
  have hEcoeff : E0.coeff (6 * n) =
      (1 / 27 : k) * A.coeff (2 * n) ^ 3 := by
    simp only [E0, coeff_add, coeff_smul, hA3,
      coeff_eq_zero_of_natDegree_lt hAclt,
      coeff_eq_zero_of_natDegree_lt helt, smul_eq_mul, add_zero, mul_zero]
  have hEder := coeff_derivative_at_bound68 E0 (6 * n) (by omega)
  rw [hEcoeff] at hEder
  have hload :
      (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A 0 c D e).coeff (6 * n - 1) =
        (1 / 27 : k) * zeta * A.coeff (2 * n) ^ 3 *
          (((6 * n : ℕ) : k)) := by
    rw [hloadEq, coeff_sub, coeff_smul,
      coeff_eq_zero_of_natDegree_lt hWdeg, sub_zero, hEder]
    simp only [smul_eq_mul]
    ring
  rw [hcore, coeff_eq_zero_of_natDegree_lt hremdeg, hload] at hrowCoeff
  simpa only [add_zero] using hrowCoeff

/-- The nonzero-`e` branch of the four wall scalars is inconsistent. -/
theorem sevenRadiusWall_scalar_packet_inconsistent_of_e_ne_zero68
    (n : ℕ) (hn : 0 < n) (a c d e zeta : k)
    (ha : a ≠ 0) (he : e ≠ 0)
    (hi3 : d ^ 2 + 2 * c * e = 0)
    (hi4 : (8 / 3 : k) * d * c + zeta * a = 0)
    (hrow : e * (2 * a * c + 3 * e) = 0)
    (hzero :
      (4 / 81 : k) *
          (-3 * a * d * c * a * (((2 * n : ℕ) : k)) -
            9 * d * e * a * (((2 * n : ℕ) : k))) +
        (1 / 27 : k) * zeta * a ^ 3 * (((6 * n : ℕ) : k)) = 0) :
    False := by
  push_cast at hzero
  have hfactor : d * (a * c + e) = 0 := by
    have hscaled : (-8 / 9 : k) * (n : k) * a *
        (d * (a * c + e)) = 0 := by
      linear_combination hzero -
        (2 / 9 : k) * (n : k) * a ^ 2 * hi4
    have hnCast : (n : k) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    rcases mul_eq_zero.mp hscaled with hnum | hrest
    · rcases mul_eq_zero.mp hnum with hratN | ha0
      · rcases mul_eq_zero.mp hratN with hrat | hn0
        · norm_num at hrat
        · exact (hnCast hn0).elim
      · exact (ha ha0).elim
    · exact hrest
  have hlin : 2 * a * c + 3 * e = 0 :=
    (mul_eq_zero.mp hrow).resolve_left he
  have hc0 : c ≠ 0 := by
    intro hz
    rw [hz] at hlin
    simp only [mul_zero, zero_add] at hlin
    exact he ((mul_eq_zero.mp hlin).resolve_left (by norm_num))
  rcases mul_eq_zero.mp hfactor with hd0 | hace
  · rw [hd0, zero_pow (by norm_num), zero_add] at hi3
    have hce : c * e = 0 := by
      have htwo : (2 : k) * (c * e) = 0 := by
        simpa only [mul_assoc] using hi3
      exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
    exact he ((mul_eq_zero.mp hce).resolve_left hc0)
  · have hae : a * c + e = 0 := hace
    have he0 : e = 0 := by
      linear_combination hlin - 2 * hae
    exact he he0

/-- At the wall, if `zeta=0` and `c` attains its positive edge, exact I4
again forces the whole polynomial `D` to vanish. -/
theorem cubicFirstIntegralFourPolynomial68_sevenRadiusWall_forces_D_zero
    (gamma epsilon i4 : k) (A c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hwall : 2 * g = 7 * n)
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

set_option maxHeartbeats 18000000 in
/-- The exact boundary `2g=7n` is empty. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_sevenRadiusWall_empty68
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
      2 * g = 7 * n) : False := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 2 * g = 7 * n at hwall
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hn : 0 < n := data.hn
  have hpacket :=
    maximalExpandedIntegratedPolynomialLowerSystem_sevenRadiusWall_packet68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  change Be = 0 ∧
      De.coeff (5 * n - g) ^ 2 +
        2 * ce.coeff (4 * n - g) * ee.coeff (6 * n - g) = 0 ∧
      (8 / 3 : k) * De.coeff (5 * n - g) * ce.coeff (4 * n - g) +
        zeta * Ae.coeff (2 * n) = 0 ∧
      ee.coeff (6 * n - g) *
        (2 * Ae.coeff (2 * n) * ce.coeff (4 * n - g) +
          3 * ee.coeff (6 * n - g)) = 0 at hpacket
  have hBe := hpacket.1
  have hface3 := hpacket.2.1
  have hface4 := hpacket.2.2.1
  have hrowFace := hpacket.2.2.2
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
      (by omega) data.hA data.hB data.hc data.hD data.he data.ha hI4
  rw [hdelta, hBe] at hI4
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
  by_cases heTop : ee.coeff (6 * n - g) = 0
  · have hDTop : De.coeff (5 * n - g) = 0 := by
      rw [heTop] at hface3
      simp only [mul_zero, add_zero] at hface3
      exact eq_zero_of_pow_eq_zero hface3
    have hsecondary :=
      maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
    change 0 < g ∧ Be.natDegree ≤ 3 * n - g ∧
      ce.natDegree ≤ 4 * n - g ∧ De.natDegree ≤ 5 * n - g ∧
      ee.natDegree ≤ 6 * n - g ∧
      (Be.coeff (3 * n - g) ≠ 0 ∨
        ce.coeff (4 * n - g) ≠ 0 ∨
        De.coeff (5 * n - g) ≠ 0 ∨
        ee.coeff (6 * n - g) ≠ 0) at hsecondary
    have hcTop : ce.coeff (4 * n - g) ≠ 0 := by
      rcases hsecondary.2.2.2.2.2 with hBt | hct | hdt | het
      · exact (hBt (by rw [hBe, coeff_zero])).elim
      · exact hct
      · exact (hdt hDTop).elim
      · exact (het heTop).elim
    have hzeta : zeta = 0 := by
      rw [hDTop] at hface4
      simp only [mul_zero, zero_mul, zero_add] at hface4
      exact (mul_eq_zero.mp hface4).resolve_right data.ha
    rw [hzeta] at hI4
    have hDzero :=
      cubicFirstIntegralFourPolynomial68_sevenRadiusWall_forces_D_zero
        gamma epsilon i4 Ae ce De ee n g hn hwall data.hc hcTop hI4
    rw [hl, hbeta, hdelta, hzeta, hBe, hDzero] at hrowZero
    simp only [integratedUPolynomial68, lowerRowZeroPolynomial68, zero_smul,
      smul_zero, zero_mul, mul_zero, add_zero, zero_add, sub_zero, C_0]
        at hrowZero
    have hrhs : C terminal * (60 * (X ^ 59 : k[X])) ≠ 0 := by
      apply mul_ne_zero
      · simpa only [C_ne_zero] using hterminal
      · exact mul_ne_zero (by norm_num) (pow_ne_zero 59 X_ne_zero)
    exact hrhs hrowZero.symm
  · have hnTen : 10 ≤ n := by
      simpa only [n] using weightedRadius68_ge_ten A B C0 D E hn
    have hnGt : 10 < n := by
      by_contra hnot
      have hnEq : n = 10 := by omega
      have hgEq : g = 35 := by omega
      have heexpand : ee =
          expand k 60 (cubicEDefectPolynomial68 A C0 E) := by
        simpa only [ee, Ae, Ce, Ee] using
          expand_cubicEDefectPolynomial68 60 A C0 E
      have hezero : ee.coeff (6 * n - g) = 0 := by
        rw [hnEq, hgEq]
        change ee.coeff 25 = 0
        rw [heexpand, coeff_expand (by norm_num)]
        norm_num
      exact heTop hezero
    have hidx : 59 < 6 * n - 1 := by omega
    have hzeroCoeff :=
      expand_lowerRowZeroPolynomial68_coeff_eq_zero_of_index_gt
        terminal
        (integratedUPolynomial68 l alpha beta gamma delta zeta
          Ae Be Ce De Ee)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          Ae Be Ce De Ee) De Ee (6 * n - 1) hrowZero hidx
    rw [hl, hbeta, hdelta, hBe, hCrec, hErec] at hzeroCoeff
    have hterminalFace :=
      lowerRowZeroPolynomial68_sevenRadiusWall_relation
        alpha gamma epsilon zeta eta Ae ce De ee n g hn hwall
        data.hA data.hc data.hD data.he hzeroCoeff
    exact sevenRadiusWall_scalar_packet_inconsistent_of_e_ne_zero68
      n hn (Ae.coeff (2 * n)) (ce.coeff (4 * n - g))
      (De.coeff (5 * n - g)) (ee.coeff (6 * n - g)) zeta
      data.ha heTop hface3 hface4 hrowFace hterminalFace

end LaterDeepSevenBoundary68

#print axioms lowerRowZeroPolynomial68_sevenRadiusWall_relation
#print axioms sevenRadiusWall_scalar_packet_inconsistent_of_e_ne_zero68
#print axioms cubicFirstIntegralFourPolynomial68_sevenRadiusWall_forces_D_zero
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_sevenRadiusWall_empty68

end Max11DegreeRoutes
