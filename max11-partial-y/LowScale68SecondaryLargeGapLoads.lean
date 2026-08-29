import LowScale68SecondaryResidualExtraction

/-! # The first loaded `(6,8)` large-gap chamber

When the secondary defect is below the first unclassified wall, `n < 2g`,
the old-weight quartic load `l*A^4` occurs strictly above every transverse
cubic term.  The constant quartic invariant therefore forces `l=0`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section SecondaryLargeGapLoads68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantFourPolynomial68_coeff_eightRadius
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantFourPolynomial68
      l beta gamma delta epsilon zeta A B c D e).coeff (8 * n) =
      (35 / 1728 * l : k) * A.coeff (2 * n) ^ 4 := by
  let q := zeta • A + (2 * epsilon : k) • B +
    (1 / 4 * delta : k) • A ^ 2 + (3 * delta : k) • c +
    (4 * gamma : k) • D - (4 / 3 * gamma : k) • (A * B) +
    (5 * beta : k) • e + (5 / 6 * beta : k) • (A * c) -
    (5 / 12 * beta : k) • B ^ 2 +
    (5 / 72 * beta : k) • A ^ 3 +
    (7 / 24 * l : k) • (A ^ 2 * c) -
    (35 / 72 * l : k) • (A * B ^ 2) +
    (7 / 6 * l : k) • (A * e) +
    (7 / 6 * l : k) • (B * D) + (7 / 12 * l : k) • c ^ 2
  have hq : q.natDegree < 8 * n := by
    simp only [q]
    compute_degree
    omega
  have hA4 := coeff_pow_at_bound68 A (2 * n) 4 hA
  have hi : 4 * (2 * n) = 8 * n := by omega
  rw [hi] at hA4
  have hsplit :
      secondaryLoadInvariantFourPolynomial68
          l beta gamma delta epsilon zeta A B c D e =
        q + (35 / 1728 * l : k) • A ^ 4 := by
    simp only [q, secondaryLoadInvariantFourPolynomial68]
    module
  rw [hsplit, coeff_add, coeff_eq_zero_of_natDegree_lt hq, zero_add,
    coeff_smul, hA4, smul_eq_mul]

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralFourPolynomial68_coeff_eightRadius_of_radius_lt_twoGap
    (l beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hlarge : n < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      A B c D e).coeff (8 * n) =
      (35 / 1728 * l : k) * A.coeff (2 * n) ^ 4 := by
  let q := (-8 / 27 : k) • B ^ 3 - (8 / 9 : k) • (A * B * c) +
    (8 / 3 : k) • (B * e) + (8 / 3 : k) • (D * c)
  have hq : q.natDegree < 8 * n := by
    simp only [q]
    compute_degree
    omega
  have hqeq :
      cubicFirstIntegralFourPolynomial68 0 0 0 0 0 0 A B c D e = q := by
    simp [q, cubicFirstIntegralFourPolynomial68]
  rw [cubicFirstIntegralFourPolynomial68_secondaryLoadSplit, coeff_add,
    hqeq, coeff_eq_zero_of_natDegree_lt hq, zero_add]
  exact secondaryLoadInvariantFourPolynomial68_coeff_eightRadius
    l beta gamma delta epsilon zeta A B c D e n g hn hg hA hB hc hD he

set_option maxHeartbeats 2000000 in
theorem cubicFirstIntegralFourPolynomial68_forces_l_eq_zero_of_radius_lt_twoGap
    (l beta gamma delta epsilon zeta i4 : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hg : 0 < g) (hlarge : n < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hI4 : cubicFirstIntegralFourPolynomial68
      l beta gamma delta epsilon zeta A B c D e = C i4) :
    l = 0 := by
  have hcoeff := congrArg (fun p : k[X] => p.coeff (8 * n)) hI4
  rw [cubicFirstIntegralFourPolynomial68_coeff_eightRadius_of_radius_lt_twoGap
      l beta gamma delta epsilon zeta A B c D e n g hn hg hlarge
      hA hB hc hD he] at hcoeff
  have hi : 8 * n ≠ 0 := by omega
  simp only [coeff_C, if_neg hi] at hcoeff
  have hscalar : (35 / 1728 : k) ≠ 0 := by norm_num
  have hpow : A.coeff (2 * n) ^ 4 ≠ 0 := pow_ne_zero 4 ha
  have hsl : (35 / 1728 * l : k) = 0 :=
    (mul_eq_zero.mp hcoeff).resolve_right hpow
  exact (mul_eq_zero.mp hsl).resolve_left hscalar

set_option maxHeartbeats 4000000 in
/-- In the strict loaded chamber, the canonical quartic invariant first sees
the pure `l*A^4` load, so its coefficient `l` must vanish. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_l_eq_zero_of_radius_lt_twoGap68
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
    have h := congrArg (expand k 60) hi4
    simpa [Ae, Be, Ce, De, Ee, expand_firstIntegralFourPolynomial68] using h
  rw [hCrec, hErec,
    firstIntegralFourPolynomial68_cubicCoordinates] at hi4e
  exact cubicFirstIntegralFourPolynomial68_forces_l_eq_zero_of_radius_lt_twoGap
    l beta gamma delta epsilon zeta i4 Ae Be ce De ee n g hn hg hlarge
    hA hB hc hD he ha hi4e

end SecondaryLargeGapLoads68

#print axioms secondaryLoadInvariantFourPolynomial68_coeff_eightRadius
#print axioms cubicFirstIntegralFourPolynomial68_coeff_eightRadius_of_radius_lt_twoGap
#print axioms cubicFirstIntegralFourPolynomial68_forces_l_eq_zero_of_radius_lt_twoGap
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_l_eq_zero_of_radius_lt_twoGap68

end Max11DegreeRoutes
