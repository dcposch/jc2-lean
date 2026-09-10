import LowScale68SecondaryResidualSelector

/-! # Complementary chamber `n ≤ 3g` after the residual small-gap endgame

The tracked theorem
`maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualSmallChamber_impossible68`
excludes `3g < n`.  This scratch treats the complementary chamber `n ≤ 3g`.

The quartic invariant load `A^4` lives at degree `8n`.  It sits strictly
above the first secondary face `9n-2g` precisely when `n < 2g`, and it
meets or exceeds the residual double face `9n-3g` throughout `n ≤ 3g`.
Consequently:

* In `n < 2g` the constant quartic invariant forces the Jacobian scalar
  `l` to vanish.  If also `3n < 2g`, the next load `A^3` forces `beta = 0`.
* In the remaining window `2g < n ≤ 3g` the first secondary face is still
  load-free, so `e_top = 0` and `A_top B_top = 3 D_top` remain available.
  After the residual degree drop, the load-free residual window shrinks
  from `g < h < 2g` to `g < h` and `g+h < n`.  On that shrunk face the
  same two invariant equations survive.
* If instead `n < g+h` and `n < 3g`, residual `I4` drops below `A^4` and
  again `l = 0`.

Remaining walls: `n = 2g`, `n = 3g`, the residual collision `g+h = n`,
and the one-form analysis on the shrunk middle face.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section Grok68LargeGap

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## Quartic-invariant load versus the first secondary face -/

set_option maxHeartbeats 2000000 in
/-- Every constant-load term of the quartic invariant is at most degree
`8n`, the old weight of `A^4`. -/
theorem secondaryLoadInvariantFourPolynomial68_degree_le_eightRadius
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantFourPolynomial68 l beta gamma delta epsilon zeta
      A B c D e).natDegree ≤ 8 * n := by
  simp only [secondaryLoadInvariantFourPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
/-- In the strict large-gap chamber `n < 2g`, the load-free quartic
invariant lies strictly below `A^4`. -/
theorem cubicHomogeneousFirstIntegralFourPolynomial68_degree_lt_eightRadius
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hlarge : n < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e).natDegree <
      8 * n := by
  simp only [cubicFirstIntegralFourPolynomial68, mul_zero, zero_mul,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 3000000 in
/-- The quartic-invariant load contributes exactly `(35/1728) l a^4` at
degree `8n`.  Every other load monomial is strictly lower once `g > 0`. -/
theorem secondaryLoadInvariantFourPolynomial68_coeff_eightRadius
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantFourPolynomial68 l beta gamma delta epsilon zeta
      A B c D e).coeff (8 * n) =
      (35 / 1728 : k) * l * A.coeff (2 * n) ^ 4 := by
  have lower (p : k[X]) (hp : p.natDegree < 8 * n) :
      p.coeff (8 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt hp
  have hA4 := coeff_pow_at_bound68 A (2 * n) 4 hA
  have hA4i : 4 * (2 * n) = 8 * n := by omega
  rw [hA4i] at hA4
  have hA1 : A.coeff (8 * n) = 0 := lower _ (by omega)
  have hB1 : B.coeff (8 * n) = 0 := lower _ (by omega)
  have hA2 : (A ^ 2).coeff (8 * n) = 0 := lower _ (by compute_degree; omega)
  have hc1 : c.coeff (8 * n) = 0 := lower _ (by omega)
  have hD1 : D.coeff (8 * n) = 0 := lower _ (by omega)
  have hAB : (A * B).coeff (8 * n) = 0 := lower _ (by compute_degree; omega)
  have he1 : e.coeff (8 * n) = 0 := lower _ (by omega)
  have hAc : (A * c).coeff (8 * n) = 0 := lower _ (by compute_degree; omega)
  have hB2 : (B ^ 2).coeff (8 * n) = 0 := lower _ (by compute_degree; omega)
  have hA3 : (A ^ 3).coeff (8 * n) = 0 := lower _ (by compute_degree; omega)
  have hA2c : (A ^ 2 * c).coeff (8 * n) = 0 := lower _ (by compute_degree; omega)
  have hAB2 : (A * B ^ 2).coeff (8 * n) = 0 := lower _ (by compute_degree; omega)
  have hAe : (A * e).coeff (8 * n) = 0 := lower _ (by compute_degree; omega)
  have hBD : (B * D).coeff (8 * n) = 0 := lower _ (by compute_degree; omega)
  have hc2 : (c ^ 2).coeff (8 * n) = 0 := lower _ (by compute_degree; omega)
  simp only [secondaryLoadInvariantFourPolynomial68, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul, hA1, hB1, hA2, hc1, hD1, hAB, he1, hAc, hB2,
    hA3, hA4, hA2c, hAB2, hAe, hBD, hc2, mul_zero, add_zero, sub_zero]
  ring

set_option maxHeartbeats 2000000 in
/-- In `n < 2g` the constant quartic invariant reads only the `A^4` load
at degree `8n`. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_eightRadius_of_n_lt_two_mul_gap
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hlarge : n < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B c D e).coeff (8 * n) =
      (35 / 1728 : k) * l * A.coeff (2 * n) ^ 4 := by
  have hhom := cubicHomogeneousFirstIntegralFourPolynomial68_degree_lt_eightRadius
    A B c D e n g hn hlarge hA hB hc hD he
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit, coeff_add,
    coeff_eq_zero_of_natDegree_lt hhom, zero_add,
    secondaryLoadInvariantFourPolynomial68_coeff_eightRadius
      l beta gamma delta epsilon zeta A B c D e n g hn hg hA hB hc hD he]

/-- A constant quartic invariant in `n < 2g` with nonzero leading `A`
forces the Jacobian scalar `l` to vanish. -/
theorem cubicFirstIntegralFourPolynomial68_imp_loadL_eq_zero_of_n_lt_two_mul_gap
    (l beta gamma delta epsilon zeta i4 : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hlarge : n < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B c D e = C i4) :
    l = 0 := by
  have hz := congrArg (fun p : k[X] => p.coeff (8 * n)) hi4
  rw [cubicFirstIntegralFourPolynomial68_coeff_eightRadius_of_n_lt_two_mul_gap
    l beta gamma delta epsilon zeta A B c D e n g hn hg hlarge
    hA hB hc hD he] at hz
  have hindex : 8 * n ≠ 0 := by omega
  simp only [coeff_C, if_neg hindex] at hz
  have hprod : (35 / 1728 : k) * (l * A.coeff (2 * n) ^ 4) = 0 := by
    linear_combination hz
  have hla : l * A.coeff (2 * n) ^ 4 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (by norm_num)
  exact (mul_eq_zero.mp hla).resolve_right (pow_ne_zero 4 ha)

set_option maxHeartbeats 4000000 in
/-- On a maximal expanded polynomial lower system, the strict large-gap
chamber `n < 2g` forces `l = 0`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_largeGap_loadL_eq_zero68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hlarge :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n < 2 * g) :
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
  change n < 2 * g at hlarge
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
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.2.1
  have hD : De.natDegree ≤ 5 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.1
  have he : ee.natDegree ≤ 6 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.2.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
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
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    have hx := congrArg (expand k 60) hi4
    simpa [Ae, Be, Ce, De, Ee, expand_firstIntegralFourPolynomial68] using hx
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates] at hi4c
  exact cubicFirstIntegralFourPolynomial68_imp_loadL_eq_zero_of_n_lt_two_mul_gap
    l beta gamma delta epsilon zeta i4 Ae Be ce De ee n g hn hg hlarge
    hA hB hc hD he ha hi4c

/-! ## Next vanishing: `beta = 0` once `3n < 2g` -/

set_option maxHeartbeats 2000000 in
/-- After `l = 0`, the remaining quartic-invariant load is at most degree
`6n`, the old weight of `beta A^3`. -/
theorem secondaryLoadInvariantFourPolynomial68_degree_le_sixRadius_of_loadL
    (beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hvery : 3 * n < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantFourPolynomial68 0 beta gamma delta epsilon zeta
      A B c D e).natDegree ≤ 6 * n := by
  simp only [secondaryLoadInvariantFourPolynomial68, mul_zero, zero_mul,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 3000000 in
theorem secondaryLoadInvariantFourPolynomial68_coeff_sixRadius_of_loadL
    (beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantFourPolynomial68 0 beta gamma delta epsilon zeta
      A B c D e).coeff (6 * n) =
      (5 / 72 : k) * beta * A.coeff (2 * n) ^ 3 := by
  have lower (p : k[X]) (hp : p.natDegree < 6 * n) :
      p.coeff (6 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt hp
  have hA3 := coeff_pow_at_bound68 A (2 * n) 3 hA
  have hA3i : 3 * (2 * n) = 6 * n := by omega
  rw [hA3i] at hA3
  have hA1 : A.coeff (6 * n) = 0 := lower _ (by omega)
  have hB1 : B.coeff (6 * n) = 0 := lower _ (by omega)
  have hA2 : (A ^ 2).coeff (6 * n) = 0 := lower _ (by compute_degree; omega)
  have hc1 : c.coeff (6 * n) = 0 := lower _ (by omega)
  have hD1 : D.coeff (6 * n) = 0 := lower _ (by omega)
  have hAB : (A * B).coeff (6 * n) = 0 := lower _ (by compute_degree; omega)
  have he1 : e.coeff (6 * n) = 0 := lower _ (by omega)
  have hAc : (A * c).coeff (6 * n) = 0 := lower _ (by compute_degree; omega)
  have hB2 : (B ^ 2).coeff (6 * n) = 0 := lower _ (by compute_degree; omega)
  simp only [secondaryLoadInvariantFourPolynomial68, mul_zero, zero_mul,
    zero_smul, smul_zero, add_zero, sub_zero, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul, hA1, hB1, hA2, hc1, hD1, hAB, he1, hAc, hB2,
    hA3, mul_zero]
  ring

/-- Once `l = 0` and `3n < 2g`, the constant quartic invariant forces
`beta = 0`. -/
theorem cubicFirstIntegralFourPolynomial68_imp_beta_eq_zero_of_three_mul_radius_lt
    (beta gamma delta epsilon zeta i4 : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hlarge : n < 2 * g) (hvery : 3 * n < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 beta gamma delta epsilon zeta
      A B c D e = C i4) :
    beta = 0 := by
  have hhomlt : (cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0
      A B c D e).natDegree < 6 * n := by
    simp only [cubicFirstIntegralFourPolynomial68, mul_zero, zero_mul,
      zero_smul, smul_zero, add_zero, sub_zero]
    compute_degree
    omega
  have hz := congrArg (fun p : k[X] => p.coeff (6 * n)) hi4
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit, coeff_add,
    coeff_eq_zero_of_natDegree_lt hhomlt, zero_add,
    secondaryLoadInvariantFourPolynomial68_coeff_sixRadius_of_loadL
      beta gamma delta epsilon zeta A B c D e n g hn hg hA hB hc hD he] at hz
  have hindex : 6 * n ≠ 0 := by omega
  simp only [coeff_C, if_neg hindex] at hz
  have hprod : (5 / 72 : k) * (beta * A.coeff (2 * n) ^ 3) = 0 := by
    linear_combination hz
  have hba : beta * A.coeff (2 * n) ^ 3 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (by norm_num)
  exact (mul_eq_zero.mp hba).resolve_right (pow_ne_zero 3 ha)

set_option maxHeartbeats 4000000 in
/-- On a maximal expanded system in `n < 2g` and `3n < 2g`, both `l` and
`beta` vanish. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_veryLargeGap_loadL_beta_eq_zero68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hlarge :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n < 2 * g ∧ 3 * n < 2 * g) :
    l = 0 ∧ beta = 0 := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change n < 2 * g ∧ 3 * n < 2 * g at hlarge
  have hl :=
    maximalExpandedIntegratedPolynomialLowerSystem_largeGap_loadL_eq_zero68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlarge.1)
  refine ⟨hl, ?_⟩
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
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.2.1
  have hD : De.natDegree ≤ 5 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.1
  have he : ee.natDegree ≤ 6 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.2.2.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
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
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    have hx := congrArg (expand k 60) hi4
    simpa [Ae, Be, Ce, De, Ee, expand_firstIntegralFourPolynomial68] using hx
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates] at hi4c
  have hi4c0 :
      cubicFirstIntegralFourPolynomial68 0 beta gamma delta epsilon zeta
        Ae Be ce De ee = C i4 := by
    simpa [hl] using hi4c
  exact cubicFirstIntegralFourPolynomial68_imp_beta_eq_zero_of_three_mul_radius_lt
    beta gamma delta epsilon zeta i4 Ae Be ce De ee n g hn hg hlarge.1
    hlarge.2 hA hB hc hD he ha hi4c0

/-! ## Residual gap after the first secondary face, without `3g < n` -/

/-- Strict residual degree drops already force the selected residual gap
above `g`.  The old hypothesis `3g < n` is unnecessary. -/
theorem secondaryResidualGap68_gt_of_strictDrops
    (n g : ℕ) (d e : k[X])
    (hd : d.natDegree < 5 * n - g)
    (he : e.natDegree < 6 * n - g) :
    g < secondaryResidualGap68 n d e := by
  apply lt_min
  · by_cases hd0 : d = 0
    · simp [polynomialGap68, hd0]
      have : 0 < 5 * n - g := by
        have := hd
        simp only [hd0, natDegree_zero] at this
        exact this
      omega
    · simp only [polynomialGap68, if_neg hd0]
      omega
  · by_cases he0 : e = 0
    · simp [polynomialGap68, he0]
      have : 0 < 6 * n - g := by
        have := he
        simp only [he0, natDegree_zero] at this
        exact this
      omega
    · simp only [polynomialGap68, if_neg he0]
      omega

/-! ## Shrunk residual window `g < h` and `g+h < n` inside `n ≤ 3g` -/

set_option maxHeartbeats 2000000 in
/-- Inside `n ≤ 3g`, the comparison `g+h < n` puts every quartic-invariant
load strictly below the residual middle face `9n-g-h`. -/
theorem secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_loadWindow
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hgh : g < h) (hwin : g + h < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantFourPolynomial68
      l beta gamma delta epsilon zeta A B c D e).natDegree <
        9 * n - g - h := by
  simp only [secondaryLoadInvariantFourPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
/-- The corresponding cubic-invariant load cutoff.  The heaviest remaining
load is `l A^3 B` at `9n-g`, which stays below `10n-g-h` once `h < n`. -/
theorem secondaryLoadInvariantThreePolynomial68_degree_lt_middle_of_loadWindow
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hwin : g + h < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryLoadInvariantThreePolynomial68
      l beta gamma delta epsilon zeta A B c D e).natDegree <
        10 * n - g - h := by
  simp only [secondaryLoadInvariantThreePolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
/-- Load-free residual quartic coefficient on the shrunk middle face.
The `B^3` term is lower because `h < 2g` follows from `g+h < n ≤ 3g`. -/
theorem secondaryResidualInvariantFourPolynomial68_coeff_middle_of_loadWindow
    (B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hlarge : n ≤ 3 * g) (hwin : g + h < n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
        (9 * n - g - h) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - h) +
          c.coeff (4 * n - g) * d.coeff (5 * n - h)) := by
  have hB3 : (B ^ 3).natDegree < 9 * n - g - h := by
    compute_degree
    omega
  have hBe := coeff_mul_at_bounds68 B e (3 * n - g) (6 * n - h) hB he
  have hBei : (3 * n - g) + (6 * n - h) = 9 * n - g - h := by omega
  rw [hBei] at hBe
  have hcd := coeff_mul_at_bounds68 c d (4 * n - g) (5 * n - h) hc hd
  have hcdi : (4 * n - g) + (5 * n - h) = 9 * n - g - h := by omega
  rw [hcdi] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3, hBe, hcd]
  ring

set_option maxHeartbeats 2000000 in
theorem secondaryResidualInvariantThreePolynomial68_coeff_middle_of_loadWindow
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hlarge : n ≤ 3 * g) (hwin : g + h < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (10 * n - g - h) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - h)) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - h)) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n)
    (3 * n - g) (5 * n - h) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (5 * n - h) =
      10 * n - g - h := by omega
  rw [hABdi] at hABd
  have hB2c : (B ^ 2 * c).natDegree < 10 * n - g - h := by
    compute_degree
    omega
  have hce := coeff_mul_at_bounds68 c e (4 * n - g) (6 * n - h) hc he
  have hcei : (4 * n - g) + (6 * n - h) = 10 * n - g - h := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 10 * n - g - h := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd,
    coeff_eq_zero_of_natDegree_lt hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralFourPolynomial68_coeff_residualMiddle_of_loadWindow
    (l beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hgh : g < h)
    (hlarge : n ≤ 3 * g) (hwin : g + h < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (9 * n - g - h) =
      (8 / 3 : k) *
        (B.coeff (3 * n - g) * e.coeff (6 * n - h) +
          c.coeff (4 * n - g) * d.coeff (5 * n - h)) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload := secondaryLoadInvariantFourPolynomial68_degree_lt_middle_of_loadWindow
    l beta gamma delta epsilon zeta A B c D e n g h hg hgh hwin
    hA hB hc hD he
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantFourPolynomial68 B c d e by
      simpa only [D] using
        cubicFirstIntegralFourPolynomial68_residualCoordinates A B c d e,
    coeff_add,
    secondaryResidualInvariantFourPolynomial68_coeff_middle_of_loadWindow
      B c d e n g h hg hgh hlarge hwin hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hload, add_zero]

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralThreePolynomial68_coeff_residualMiddle_of_loadWindow
    (l beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hg : 0 < g) (hgh : g < h)
    (hlarge : n ≤ 3 * g) (hwin : g + h < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicFirstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (10 * n - g - h) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - h)) +
          3 * c.coeff (4 * n - g) * e.coeff (6 * n - h)) := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have hload := secondaryLoadInvariantThreePolynomial68_degree_lt_middle_of_loadWindow
    l beta gamma delta epsilon zeta A B c D e n g h hg hwin
    hA hB hc hD he
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit,
    show cubicFirstIntegralThreePolynomial68 0 0 0 0 0 0 A B c D e =
        secondaryResidualInvariantThreePolynomial68 A B c d e by
      simpa only [D] using
        cubicFirstIntegralThreePolynomial68_residualCoordinates A B c d e,
    coeff_add,
    secondaryResidualInvariantThreePolynomial68_coeff_middle_of_loadWindow
      A B c d e n g h hg hgh hlarge hwin hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt hload, add_zero]

/-- The two constant invariants still select the abstract residual middle
face on the shrunk load-free window `g < h` and `g+h < n` inside `n ≤ 3g`. -/
theorem polynomialSecondaryResidualBetweenFace68_of_loadWindow
    (l beta gamma delta epsilon zeta i4 i3 : k)
    (A B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hgh : g < h) (hlarge : n ≤ 3 * g) (hwin : g + h < n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (hi4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      l beta gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3) :
    SecondaryResidualBetweenFace68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (e.coeff (6 * n - h)) := by
  constructor
  · have hz := congrArg (fun p : k[X] => p.coeff (9 * n - g - h)) hi4
    rw [cubicFirstIntegralFourPolynomial68_coeff_residualMiddle_of_loadWindow
      l beta gamma delta epsilon zeta A B c d e n g h hg hgh hlarge hwin
      hA hB hc hd he] at hz
    have hindex : 9 * n - g - h ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · have hz := congrArg (fun p : k[X] => p.coeff (10 * n - g - h)) hi3
    rw [cubicFirstIntegralThreePolynomial68_coeff_residualMiddle_of_loadWindow
      l beta gamma delta epsilon zeta A B c d e n g h hg hgh hlarge hwin
      hA hB hc hd he] at hz
    have hindex : 10 * n - g - h ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    have hzero := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    linear_combination hzero

set_option maxHeartbeats 4000000 in
/-- On a maximal expanded system in `n ≤ 3g`, a residual gap in the
load-free window `g < h` and `g+h < n` supplies the residual middle face. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_largeGapResidualMiddleFace68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (h : ℕ) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hlarge :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n ≤ 3 * g)
    (hgh :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      g < h)
    (hwin :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      g + h < n)
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
      d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h) :
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
    SecondaryResidualBetweenFace68
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g)) (d.coeff (5 * n - h))
      (ee.coeff (6 * n - h)) := by
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
  change n ≤ 3 * g at hlarge
  change g < h at hgh
  change g + h < n at hwin
  change d.natDegree ≤ 5 * n - h ∧
    ee.natDegree ≤ 6 * n - h at hmiddle
  have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
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
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
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
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
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
  exact polynomialSecondaryResidualBetweenFace68_of_loadWindow
    l beta gamma delta epsilon zeta i4 i3 Ae Be ce d ee n g h
    hg hgh hlarge hwin hA hB hc hmiddle.1 hmiddle.2 hi4c hi3c

/-! ## Residual `A^4` collision when `n < g+h` and `n < 3g` -/

set_option maxHeartbeats 2000000 in
/-- If the residual gap overshoots the load window and we are still
strictly below the double wall `n = 3g`, residual `I4` lies below `A^4`. -/
theorem secondaryResidualInvariantFourPolynomial68_degree_lt_eightRadius
    (B c d e : k[X]) (n g h : ℕ)
    (hg : 0 < g) (hn : 0 < n) (hstrict : n < 3 * g) (hover : n < g + h)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).natDegree <
      8 * n := by
  simp only [secondaryResidualInvariantFourPolynomial68]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralFourPolynomial68_coeff_eightRadius_of_residualOvershoot
    (l beta gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hover : n < g + h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff (8 * n) =
      (35 / 1728 : k) * l * A.coeff (2 * n) ^ 4 := by
  let D := (1 / 3 : k) • (A * B) + d
  have hD : D.natDegree ≤ 5 * n - g := by
    simp only [D]
    compute_degree
    omega
  have he' : e.natDegree ≤ 6 * n - g := by omega
  have hhom :
      (cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e).natDegree <
        8 * n := by
    have hres :
        (secondaryResidualInvariantFourPolynomial68 B c d e).natDegree <
          8 * n :=
      secondaryResidualInvariantFourPolynomial68_degree_lt_eightRadius
        B c d e n g h hg hn hstrict hover hB hc hd he
    have hident :
        cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e =
          secondaryResidualInvariantFourPolynomial68 B c d e := by
      simpa only [D] using
        cubicFirstIntegralFourPolynomial68_residualCoordinates A B c d e
    simpa only [hident] using hres
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit, coeff_add,
    coeff_eq_zero_of_natDegree_lt hhom, zero_add,
    secondaryLoadInvariantFourPolynomial68_coeff_eightRadius
      l beta gamma delta epsilon zeta A B c D e n g hn hg hA hB hc hD he']

/-- Residual overshoot `n < g+h` inside `n < 3g` again forces `l = 0`. -/
theorem cubicFirstIntegralFourPolynomial68_imp_loadL_eq_zero_of_residualOvershoot
    (l beta gamma delta epsilon zeta i4 : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g) (hgh : g < h)
    (hsmall : 2 * g < n) (hstrict : n < 3 * g) (hover : n < g + h)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h)
    (ha : A.coeff (2 * n) ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e = C i4) :
    l = 0 := by
  have hz := congrArg (fun p : k[X] => p.coeff (8 * n)) hi4
  rw [cubicFirstIntegralFourPolynomial68_coeff_eightRadius_of_residualOvershoot
    l beta gamma delta epsilon zeta A B c d e n g h hn hg hgh
    hsmall hstrict hover hA hB hc hd he] at hz
  have hindex : 8 * n ≠ 0 := by omega
  simp only [coeff_C, if_neg hindex] at hz
  have hprod : (35 / 1728 : k) * (l * A.coeff (2 * n) ^ 4) = 0 := by
    linear_combination hz
  have hla : l * A.coeff (2 * n) ^ 4 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (by norm_num)
  exact (mul_eq_zero.mp hla).resolve_right (pow_ne_zero 4 ha)

set_option maxHeartbeats 4000000 in
/-- On a maximal expanded system in `2g < n < 3g`, a residual gap with
`n < g+h` forces `l = 0`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_residualOvershoot_loadL_eq_zero68
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
      2 * g < n ∧ n < 3 * g)
    (hover :
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
      n < g + h) :
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
  change 2 * g < n ∧ n < 3 * g at hchamber
  change n < g + h at hover
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
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.2.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hdrops :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualDegreeDrops68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber.1)
  change d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g at hdrops
  have hgh : g < h := by
    simpa only [h] using secondaryResidualGap68_gt_of_strictDrops n g d ee
      hdrops.1 hdrops.2
  have hdbase : d.natDegree < 5 * n := by omega
  have hebase : ee.natDegree < 6 * n := by omega
  have hbounds : d.natDegree ≤ 5 * n - h ∧
      ee.natDegree ≤ 6 * n - h := by
    simpa only [h] using secondaryResidualGap68_degreeBounds n d ee
      hdbase hebase
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
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
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    have hx := congrArg (expand k 60) hi4
    simpa [Ae, Be, Ce, De, Ee, expand_firstIntegralFourPolynomial68] using hx
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec] at hi4c
  exact cubicFirstIntegralFourPolynomial68_imp_loadL_eq_zero_of_residualOvershoot
    l beta gamma delta epsilon zeta i4 Ae Be ce d ee n g h hn hg hgh
    hchamber.1 hchamber.2 hover hA hB hc hbounds.1 hbounds.2 ha hi4c

end Grok68LargeGap

#print axioms maximalExpandedIntegratedPolynomialLowerSystem_largeGap_loadL_eq_zero68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_veryLargeGap_loadL_beta_eq_zero68
#print axioms secondaryResidualGap68_gt_of_strictDrops
#print axioms polynomialSecondaryResidualBetweenFace68_of_loadWindow
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_largeGapResidualMiddleFace68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_residualOvershoot_loadL_eq_zero68

end Max11DegreeRoutes
