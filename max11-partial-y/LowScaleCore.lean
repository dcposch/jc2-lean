import EndpointGCDRoute

/-! # Common-core normalization for the first low-scale leaf

The smallest remaining gcd-two leaf has partial degrees `(4,6)`.  Its top
weighted-Wronskian row has reduced weights `(2,3)`, so the two leading
coefficients are scalar multiples of a square and cube of one common
polynomial.  This module derives that factorization from a genuine Keller
pair, tracks the common core's exact degree, and removes both scalar factors
by invertible target rescalings.

The resulting source interface simultaneously covers the two residual common
scales `H = 0` and `H = 2`; proving that normalized interface is still a
mathematical input.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-- The square/cube common-core theorem with the weighted relation written in
its reduced `(2,3)` form. -/
theorem commonCore_of_reducedWeightedWronskian_23 {K : Type*}
    [Field K] [CharZero K] {A B : K[X]} (hA : A ≠ 0) (hB : B ≠ 0)
    (hweighted :
      Polynomial.C (3 : K) * B * A.derivative =
        Polynomial.C (2 : K) * A * B.derivative) :
    ∃ (alpha beta : K) (h : K[X]),
      alpha ≠ 0 ∧ beta ≠ 0 ∧ h ≠ 0 ∧
        A = Polynomial.C alpha * h ^ 2 ∧
        B = Polynomial.C beta * h ^ 3 := by
  have hC33 : Polynomial.C (3 : K) * Polynomial.C (3 : K) =
      Polynomial.C (9 : K) := by
    rw [← Polynomial.C_mul]
    norm_num
  have hC32 : Polynomial.C (3 : K) * Polynomial.C (2 : K) =
      Polynomial.C (6 : K) := by
    rw [← Polynomial.C_mul]
    norm_num
  apply commonCore_of_weightedWronskian_69 hA hB
  calc
    Polynomial.C (9 : K) * B * A.derivative =
        Polynomial.C (3 : K) *
          (Polynomial.C (3 : K) * B * A.derivative) := by
      rw [← hC33]
      ring
    _ = Polynomial.C (3 : K) *
          (Polynomial.C (2 : K) * A * B.derivative) := by rw [hweighted]
    _ = Polynomial.C (6 : K) * A * B.derivative := by
      rw [← hC32]
      ring

/-- UFD extraction once two nonzero polynomials satisfy consecutive coprime
power equality, up to a nonzero scalar. -/
theorem commonCore_of_consecutivePowerRelation {K : Type*}
    [Field K] {A B : K[X]} (r : ℕ) (_hr : 0 < r)
    (_hA : A ≠ 0) (hB : B ≠ 0) (c : K) (hc : c ≠ 0)
    (hpowers : A ^ (r + 1) = Polynomial.C c * B ^ r) :
    ∃ (alpha beta : K) (h : K[X]),
      alpha ≠ 0 ∧ beta ≠ 0 ∧ h ≠ 0 ∧
        A = Polynomial.C alpha * h ^ r ∧
        B = Polynomial.C beta * h ^ (r + 1) := by
  classical
  letI := EuclideanDomain.gcdMonoid K[X]
  let d := gcd A B
  let A' := A / d
  let B' := B / d
  have hd : d ≠ 0 := gcd_ne_zero_of_right hB
  have hdA : d * A' = A :=
    EuclideanDomain.mul_div_cancel' hd (gcd_dvd_left A B)
  have hdB : d * B' = B :=
    EuclideanDomain.mul_div_cancel' hd (gcd_dvd_right A B)
  have hB' : B' ≠ 0 := by
    intro hB'zero
    apply hB
    rw [← hdB, hB'zero, mul_zero]
  have hcop : IsCoprime A' B' := isCoprime_div_gcd_div_gcd hB
  have hreduced : d * A' ^ (r + 1) = Polynomial.C c * B' ^ r := by
    apply mul_left_cancel₀ (pow_ne_zero r hd)
    calc
      d ^ r * (d * A' ^ (r + 1)) = (d * A') ^ (r + 1) := by
        rw [mul_pow, pow_succ d r]
        ring
      _ = A ^ (r + 1) := by rw [hdA]
      _ = Polynomial.C c * B ^ r := hpowers
      _ = Polynomial.C c * (d * B') ^ r := by rw [hdB]
      _ = d ^ r * (Polynomial.C c * B' ^ r) := by
        rw [mul_pow]
        ring
  have hCunit : IsUnit (Polynomial.C c) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
  have hA'dvd : A' ∣ Polynomial.C c * B' ^ r := by
    refine ⟨d * A' ^ r, ?_⟩
    rw [← hreduced, pow_succ]
    ac_rfl
  have hA'unit : IsUnit A' := by
    apply isUnit_of_dvd_unit
      (hcop.pow_right.dvd_of_dvd_mul_right hA'dvd) hCunit
  have hdassoc : Associated d (B' ^ r) :=
    (associated_mul_unit_left d (A' ^ (r + 1)) (hA'unit.pow (r + 1))).symm |>.trans
      (Associated.of_eq hreduced) |>.trans
        (associated_unit_mul_left (B' ^ r) (Polynomial.C c) hCunit)
  have hAassoc : Associated A (B' ^ r) :=
    (Associated.of_eq hdA.symm).trans
      ((associated_mul_unit_left d A' hA'unit).trans hdassoc)
  have hBassoc : Associated B (B' ^ (r + 1)) := by
    apply (Associated.of_eq hdB.symm).trans
    have hmul := hdassoc.mul_right B'
    exact hmul.trans (Associated.of_eq (by rw [pow_succ]))
  obtain ⟨uA, huA⟩ := hAassoc.symm
  obtain ⟨uB, huB⟩ := hBassoc.symm
  obtain ⟨alpha, halphaUnit, halpha⟩ :=
    Polynomial.isUnit_iff.mp uA.isUnit
  obtain ⟨beta, hbetaUnit, hbeta⟩ :=
    Polynomial.isUnit_iff.mp uB.isUnit
  refine ⟨alpha, beta, B', isUnit_iff_ne_zero.mp halphaUnit,
    isUnit_iff_ne_zero.mp hbetaUnit, hB', ?_, ?_⟩
  · calc
      A = B' ^ r * (uA : K[X]) := huA.symm
      _ = Polynomial.C alpha * B' ^ r := by rw [halpha]; ring
  · calc
      B = B' ^ (r + 1) * (uB : K[X]) := huB.symm
      _ = Polynomial.C beta * B' ^ (r + 1) := by rw [hbeta]; ring

/-- The reduced `(3,4)` weighted Wronskian forces a cube/fourth-power
common core. -/
theorem commonCore_of_reducedWeightedWronskian_34 {K : Type*}
    [Field K] [CharZero K] {A B : K[X]} (hA : A ≠ 0) (hB : B ≠ 0)
    (hweighted :
      Polynomial.C (4 : K) * B * A.derivative =
        Polynomial.C (3 : K) * A * B.derivative) :
    ∃ (alpha beta : K) (h : K[X]),
      alpha ≠ 0 ∧ beta ≠ 0 ∧ h ≠ 0 ∧
        A = Polynomial.C alpha * h ^ 3 ∧
        B = Polynomial.C beta * h ^ 4 := by
  have hW : Polynomial.wronskian (A ^ 4) (B ^ 3) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      A ^ 4 * (Polynomial.C (3 : K) * B ^ (3 - 1) * B.derivative) -
          (Polynomial.C (4 : K) * A ^ (4 - 1) * A.derivative) * B ^ 3 =
          A ^ 3 * B ^ 2 *
            (Polynomial.C (3 : K) * A * B.derivative -
              Polynomial.C (4 : K) * B * A.derivative) := by ring
      _ = 0 := by rw [hweighted, sub_self, mul_zero]
  obtain ⟨c, hpowers⟩ :=
    eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 3 hB) hW
  have hc : c ≠ 0 := by
    intro hczero
    apply pow_ne_zero 4 hA
    rw [hpowers, hczero, Polynomial.C_0, zero_mul]
  simpa only [Nat.reduceAdd] using
    commonCore_of_consecutivePowerRelation 3 (by norm_num) hA hB c hc hpowers

/-- The reduced `(4,5)` weighted Wronskian forces a fourth/fifth-power
common core. -/
theorem commonCore_of_reducedWeightedWronskian_45 {K : Type*}
    [Field K] [CharZero K] {A B : K[X]} (hA : A ≠ 0) (hB : B ≠ 0)
    (hweighted :
      Polynomial.C (5 : K) * B * A.derivative =
        Polynomial.C (4 : K) * A * B.derivative) :
    ∃ (alpha beta : K) (h : K[X]),
      alpha ≠ 0 ∧ beta ≠ 0 ∧ h ≠ 0 ∧
        A = Polynomial.C alpha * h ^ 4 ∧
        B = Polynomial.C beta * h ^ 5 := by
  have hW : Polynomial.wronskian (A ^ 5) (B ^ 4) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      A ^ 5 * (Polynomial.C (4 : K) * B ^ (4 - 1) * B.derivative) -
          (Polynomial.C (5 : K) * A ^ (5 - 1) * A.derivative) * B ^ 4 =
          A ^ 4 * B ^ 3 *
            (Polynomial.C (4 : K) * A * B.derivative -
              Polynomial.C (5 : K) * B * A.derivative) := by ring
      _ = 0 := by rw [hweighted, sub_self, mul_zero]
  obtain ⟨c, hpowers⟩ :=
    eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 4 hB) hW
  have hc : c ≠ 0 := by
    intro hczero
    apply pow_ne_zero 5 hA
    rw [hpowers, hczero, Polynomial.C_0, zero_mul]
  simpa only [Nat.reduceAdd] using
    commonCore_of_consecutivePowerRelation 4 (by norm_num) hA hB c hc hpowers

/-- UFD extraction for the coprime reduced weights `(2,5)`.  After removing
the gcd of `A,B`, the residual cube/square relation is reduced to the already
proved square/cube common-core lemma. -/
theorem commonCore_of_powerRelation_25 {K : Type*}
    [Field K] [CharZero K] {A B : K[X]} (_hA : A ≠ 0) (hB : B ≠ 0)
    (c : K) (hc : c ≠ 0)
    (hpowers : A ^ 5 = Polynomial.C c * B ^ 2) :
    ∃ (alpha beta : K) (h : K[X]),
      alpha ≠ 0 ∧ beta ≠ 0 ∧ h ≠ 0 ∧
        A = Polynomial.C alpha * h ^ 2 ∧
        B = Polynomial.C beta * h ^ 5 := by
  classical
  letI := EuclideanDomain.gcdMonoid K[X]
  let d := gcd A B
  let A' := A / d
  let B' := B / d
  have hd : d ≠ 0 := gcd_ne_zero_of_right hB
  have hdA : d * A' = A :=
    EuclideanDomain.mul_div_cancel' hd (gcd_dvd_left A B)
  have hdB : d * B' = B :=
    EuclideanDomain.mul_div_cancel' hd (gcd_dvd_right A B)
  have hB' : B' ≠ 0 := by
    intro hzero
    apply hB
    rw [← hdB, hzero, mul_zero]
  have hcop : IsCoprime A' B' := isCoprime_div_gcd_div_gcd hB
  have hreduced : d ^ 3 * A' ^ 5 = Polynomial.C c * B' ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hd)
    calc
      d ^ 2 * (d ^ 3 * A' ^ 5) = (d * A') ^ 5 := by ring
      _ = A ^ 5 := by rw [hdA]
      _ = Polynomial.C c * B ^ 2 := hpowers
      _ = Polynomial.C c * (d * B') ^ 2 := by rw [hdB]
      _ = d ^ 2 * (Polynomial.C c * B' ^ 2) := by ring
  have hCunit : IsUnit (Polynomial.C c) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
  have hA'dvd : A' ∣ Polynomial.C c * B' ^ 2 := by
    refine ⟨d ^ 3 * A' ^ 4, ?_⟩
    rw [← hreduced]
    ring
  have hA'unit : IsUnit A' := by
    apply isUnit_of_dvd_unit
      (hcop.pow_right.dvd_of_dvd_mul_right hA'dvd) hCunit
  have hdpowassoc : Associated (d ^ 3) (B' ^ 2) :=
    (associated_mul_unit_left (d ^ 3) (A' ^ 5) (hA'unit.pow 5)).symm |>.trans
      (Associated.of_eq hreduced) |>.trans
        (associated_unit_mul_left (B' ^ 2) (Polynomial.C c) hCunit)
  obtain ⟨u, hu⟩ := hdpowassoc.symm
  obtain ⟨gamma, _hgammaUnit, hgamma⟩ :=
    Polynomial.isUnit_iff.mp u.isUnit
  have hdpower : d ^ 3 = Polynomial.C gamma * B' ^ 2 := by
    calc
      d ^ 3 = B' ^ 2 * (u : K[X]) := hu.symm
      _ = Polynomial.C gamma * B' ^ 2 := by rw [← hgamma]; ring
  have hW : Polynomial.wronskian (d ^ 3) (B' ^ 2) = 0 := by
    rw [hdpower, Polynomial.wronskian, Polynomial.derivative_mul]
    simp only [Polynomial.derivative_C, zero_mul, zero_add]
    ring
  have hfactor :
      d ^ 2 * B' *
        (Polynomial.C (2 : K) * d * B'.derivative -
          Polynomial.C (3 : K) * B' * d.derivative) = 0 := by
    calc
      d ^ 2 * B' *
          (Polynomial.C (2 : K) * d * B'.derivative -
            Polynomial.C (3 : K) * B' * d.derivative) =
          Polynomial.wronskian (d ^ 3) (B' ^ 2) := by
        rw [Polynomial.wronskian, Polynomial.derivative_pow,
          Polynomial.derivative_pow]
        ring_nf
      _ = 0 := hW
  have hinner :
      Polynomial.C (2 : K) * d * B'.derivative -
        Polynomial.C (3 : K) * B' * d.derivative = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left
      (mul_ne_zero (pow_ne_zero 2 hd) hB')
  have hweighted :
      Polynomial.C (3 : K) * B' * d.derivative =
        Polynomial.C (2 : K) * d * B'.derivative :=
    (sub_eq_zero.mp hinner).symm
  obtain ⟨delta, epsilon, h, hdelta, hepsilon, hh, hdcore, hB'core⟩ :=
    commonCore_of_reducedWeightedWronskian_23 hd hB' hweighted
  obtain ⟨a0, ha0unit, ha0⟩ := Polynomial.isUnit_iff.mp hA'unit
  refine ⟨delta * a0, delta * epsilon, h,
    mul_ne_zero hdelta (isUnit_iff_ne_zero.mp ha0unit),
    mul_ne_zero hdelta hepsilon, hh, ?_, ?_⟩
  · calc
      A = d * A' := hdA.symm
      _ = (Polynomial.C delta * h ^ 2) * Polynomial.C a0 := by
        rw [hdcore, ha0]
      _ = Polynomial.C (delta * a0) * h ^ 2 := by
        rw [Polynomial.C_mul]
        ring_nf
  · calc
      B = d * B' := hdB.symm
      _ = (Polynomial.C delta * h ^ 2) *
          (Polynomial.C epsilon * h ^ 3) := by rw [hdcore, hB'core]
      _ = Polynomial.C (delta * epsilon) * h ^ 5 := by
        rw [Polynomial.C_mul]
        ring

/-- UFD extraction for the coprime reduced weights `(3,5)`.  The quotient
after removing the gcd satisfies a square/cube relation in the opposite
orientation, again reducing to the `(2,3)` lemma. -/
theorem commonCore_of_powerRelation_35 {K : Type*}
    [Field K] [CharZero K] {A B : K[X]} (_hA : A ≠ 0) (hB : B ≠ 0)
    (c : K) (hc : c ≠ 0)
    (hpowers : A ^ 5 = Polynomial.C c * B ^ 3) :
    ∃ (alpha beta : K) (h : K[X]),
      alpha ≠ 0 ∧ beta ≠ 0 ∧ h ≠ 0 ∧
        A = Polynomial.C alpha * h ^ 3 ∧
        B = Polynomial.C beta * h ^ 5 := by
  classical
  letI := EuclideanDomain.gcdMonoid K[X]
  let d := gcd A B
  let A' := A / d
  let B' := B / d
  have hd : d ≠ 0 := gcd_ne_zero_of_right hB
  have hdA : d * A' = A :=
    EuclideanDomain.mul_div_cancel' hd (gcd_dvd_left A B)
  have hdB : d * B' = B :=
    EuclideanDomain.mul_div_cancel' hd (gcd_dvd_right A B)
  have hB' : B' ≠ 0 := by
    intro hzero
    apply hB
    rw [← hdB, hzero, mul_zero]
  have hcop : IsCoprime A' B' := isCoprime_div_gcd_div_gcd hB
  have hreduced : d ^ 2 * A' ^ 5 = Polynomial.C c * B' ^ 3 := by
    apply mul_left_cancel₀ (pow_ne_zero 3 hd)
    calc
      d ^ 3 * (d ^ 2 * A' ^ 5) = (d * A') ^ 5 := by ring
      _ = A ^ 5 := by rw [hdA]
      _ = Polynomial.C c * B ^ 3 := hpowers
      _ = Polynomial.C c * (d * B') ^ 3 := by rw [hdB]
      _ = d ^ 3 * (Polynomial.C c * B' ^ 3) := by ring
  have hCunit : IsUnit (Polynomial.C c) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
  have hA'dvd : A' ∣ Polynomial.C c * B' ^ 3 := by
    refine ⟨d ^ 2 * A' ^ 4, ?_⟩
    rw [← hreduced]
    ring
  have hA'unit : IsUnit A' := by
    apply isUnit_of_dvd_unit
      (hcop.pow_right.dvd_of_dvd_mul_right hA'dvd) hCunit
  have hdpowassoc : Associated (d ^ 2) (B' ^ 3) :=
    (associated_mul_unit_left (d ^ 2) (A' ^ 5) (hA'unit.pow 5)).symm |>.trans
      (Associated.of_eq hreduced) |>.trans
        (associated_unit_mul_left (B' ^ 3) (Polynomial.C c) hCunit)
  obtain ⟨u, hu⟩ := hdpowassoc
  obtain ⟨gamma, _hgammaUnit, hgamma⟩ :=
    Polynomial.isUnit_iff.mp u.isUnit
  have hdpower : B' ^ 3 = Polynomial.C gamma * d ^ 2 := by
    calc
      B' ^ 3 = d ^ 2 * (u : K[X]) := hu.symm
      _ = Polynomial.C gamma * d ^ 2 := by rw [← hgamma]; ring
  have hW : Polynomial.wronskian (B' ^ 3) (d ^ 2) = 0 := by
    rw [hdpower, Polynomial.wronskian, Polynomial.derivative_mul]
    simp only [Polynomial.derivative_C, zero_mul, zero_add]
    ring
  have hfactor :
      B' ^ 2 * d *
        (Polynomial.C (2 : K) * B' * d.derivative -
          Polynomial.C (3 : K) * d * B'.derivative) = 0 := by
    calc
      B' ^ 2 * d *
          (Polynomial.C (2 : K) * B' * d.derivative -
            Polynomial.C (3 : K) * d * B'.derivative) =
          Polynomial.wronskian (B' ^ 3) (d ^ 2) := by
        rw [Polynomial.wronskian, Polynomial.derivative_pow,
          Polynomial.derivative_pow]
        ring_nf
      _ = 0 := hW
  have hinner :
      Polynomial.C (2 : K) * B' * d.derivative -
        Polynomial.C (3 : K) * d * B'.derivative = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left
      (mul_ne_zero (pow_ne_zero 2 hB') hd)
  have hweighted :
      Polynomial.C (3 : K) * d * B'.derivative =
        Polynomial.C (2 : K) * B' * d.derivative :=
    (sub_eq_zero.mp hinner).symm
  obtain ⟨delta, epsilon, h, hdelta, hepsilon, hh, hB'core, hdcore⟩ :=
    commonCore_of_reducedWeightedWronskian_23 hB' hd hweighted
  obtain ⟨a0, ha0unit, ha0⟩ := Polynomial.isUnit_iff.mp hA'unit
  refine ⟨epsilon * a0, epsilon * delta, h,
    mul_ne_zero hepsilon (isUnit_iff_ne_zero.mp ha0unit),
    mul_ne_zero hepsilon hdelta, hh, ?_, ?_⟩
  · calc
      A = d * A' := hdA.symm
      _ = (Polynomial.C epsilon * h ^ 3) * Polynomial.C a0 := by
        rw [hdcore, ha0]
      _ = Polynomial.C (epsilon * a0) * h ^ 3 := by
        rw [Polynomial.C_mul]
        ring
  · calc
      B = d * B' := hdB.symm
      _ = (Polynomial.C epsilon * h ^ 3) *
          (Polynomial.C delta * h ^ 2) := by rw [hdcore, hB'core]
      _ = Polynomial.C (epsilon * delta) * h ^ 5 := by
        rw [Polynomial.C_mul]
        ring

/-- The reduced `(2,5)` weighted Wronskian forces a square/fifth-power
common core. -/
theorem commonCore_of_reducedWeightedWronskian_25 {K : Type*}
    [Field K] [CharZero K] {A B : K[X]} (hA : A ≠ 0) (hB : B ≠ 0)
    (hweighted :
      Polynomial.C (5 : K) * B * A.derivative =
        Polynomial.C (2 : K) * A * B.derivative) :
    ∃ (alpha beta : K) (h : K[X]),
      alpha ≠ 0 ∧ beta ≠ 0 ∧ h ≠ 0 ∧
        A = Polynomial.C alpha * h ^ 2 ∧
        B = Polynomial.C beta * h ^ 5 := by
  have hW : Polynomial.wronskian (A ^ 5) (B ^ 2) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      A ^ 5 * (Polynomial.C (2 : K) * B ^ (2 - 1) * B.derivative) -
          (Polynomial.C (5 : K) * A ^ (5 - 1) * A.derivative) * B ^ 2 =
          A ^ 4 * B *
            (Polynomial.C (2 : K) * A * B.derivative -
              Polynomial.C (5 : K) * B * A.derivative) := by ring
      _ = 0 := by rw [hweighted, sub_self, mul_zero]
  obtain ⟨c, hpowers⟩ :=
    eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 2 hB) hW
  have hc : c ≠ 0 := by
    intro hczero
    apply pow_ne_zero 5 hA
    rw [hpowers, hczero, Polynomial.C_0, zero_mul]
  exact commonCore_of_powerRelation_25 hA hB c hc hpowers

/-- The reduced `(3,5)` weighted Wronskian forces a cube/fifth-power
common core. -/
theorem commonCore_of_reducedWeightedWronskian_35 {K : Type*}
    [Field K] [CharZero K] {A B : K[X]} (hA : A ≠ 0) (hB : B ≠ 0)
    (hweighted :
      Polynomial.C (5 : K) * B * A.derivative =
        Polynomial.C (3 : K) * A * B.derivative) :
    ∃ (alpha beta : K) (h : K[X]),
      alpha ≠ 0 ∧ beta ≠ 0 ∧ h ≠ 0 ∧
        A = Polynomial.C alpha * h ^ 3 ∧
        B = Polynomial.C beta * h ^ 5 := by
  have hW : Polynomial.wronskian (A ^ 5) (B ^ 3) = 0 := by
    rw [Polynomial.wronskian, Polynomial.derivative_pow,
      Polynomial.derivative_pow]
    calc
      A ^ 5 * (Polynomial.C (3 : K) * B ^ (3 - 1) * B.derivative) -
          (Polynomial.C (5 : K) * A ^ (5 - 1) * A.derivative) * B ^ 3 =
          A ^ 4 * B ^ 2 *
            (Polynomial.C (3 : K) * A * B.derivative -
              Polynomial.C (5 : K) * B * A.derivative) := by ring
      _ = 0 := by rw [hweighted, sub_self, mul_zero]
  obtain ⟨c, hpowers⟩ :=
    eq_C_mul_of_wronskian_eq_zero (pow_ne_zero 3 hB) hW
  have hc : c ≠ 0 := by
    intro hczero
    apply pow_ne_zero 5 hA
    rw [hpowers, hczero, Polynomial.C_0, zero_mul]
  exact commonCore_of_powerRelation_35 hA hB c hc hpowers

/-- The `(4,6)` leading row reduces from weights `(4,6)` to `(2,3)`. -/
theorem reducedLeadingCoefficientWeightedWronskian_46 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 6)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    Polynomial.C (3 : K) * q.coeff 6 * (p.coeff 4).derivative =
      Polynomial.C (2 : K) * p.coeff 4 * (q.coeff 6).derivative := by
  have hweighted := leadingCoefficient_weightedWronskian
    hp hq (by norm_num) (by norm_num) hjac
  have hC2 : Polynomial.C (2 : K) ≠ 0 := by norm_num
  have hC23 : Polynomial.C (2 : K) * Polynomial.C (3 : K) =
      Polynomial.C (6 : K) := by
    rw [← Polynomial.C_mul]
    norm_num
  have hC22 : Polynomial.C (2 : K) * Polynomial.C (2 : K) =
      Polynomial.C (4 : K) := by
    rw [← Polynomial.C_mul]
    norm_num
  apply mul_left_cancel₀ hC2
  calc
    Polynomial.C (2 : K) *
        (Polynomial.C (3 : K) * q.coeff 6 * (p.coeff 4).derivative) =
        Polynomial.C (6 : K) * q.coeff 6 *
          (p.coeff 4).derivative := by
      rw [← hC23]
      ring
    _ = Polynomial.C (4 : K) * p.coeff 4 *
          (q.coeff 6).derivative := hweighted
    _ = Polynomial.C (2 : K) *
        (Polynomial.C (2 : K) * p.coeff 4 *
          (q.coeff 6).derivative) := by
      rw [← hC22]
      ring

/-- The `(6,8)` leading row reduces from weights `(6,8)` to `(3,4)`. -/
theorem reducedLeadingCoefficientWeightedWronskian_68 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    Polynomial.C (4 : K) * q.coeff 8 * (p.coeff 6).derivative =
      Polynomial.C (3 : K) * p.coeff 6 * (q.coeff 8).derivative := by
  have hweighted := leadingCoefficient_weightedWronskian
    hp hq (by norm_num) (by norm_num) hjac
  have hC2 : Polynomial.C (2 : K) ≠ 0 := by norm_num
  have hC24 : Polynomial.C (2 : K) * Polynomial.C (4 : K) =
      Polynomial.C (8 : K) := by
    rw [← Polynomial.C_mul]
    norm_num
  have hC23 : Polynomial.C (2 : K) * Polynomial.C (3 : K) =
      Polynomial.C (6 : K) := by
    rw [← Polynomial.C_mul]
    norm_num
  apply mul_left_cancel₀ hC2
  calc
    Polynomial.C (2 : K) *
        (Polynomial.C (4 : K) * q.coeff 8 * (p.coeff 6).derivative) =
        Polynomial.C (8 : K) * q.coeff 8 *
          (p.coeff 6).derivative := by rw [← hC24]; ring
    _ = Polynomial.C (6 : K) * p.coeff 6 *
          (q.coeff 8).derivative := hweighted
    _ = Polynomial.C (2 : K) *
        (Polynomial.C (3 : K) * p.coeff 6 *
          (q.coeff 8).derivative) := by rw [← hC23]; ring

/-- The `(8,10)` leading row reduces from weights `(8,10)` to `(4,5)`. -/
theorem reducedLeadingCoefficientWeightedWronskian_810 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    Polynomial.C (5 : K) * q.coeff 10 * (p.coeff 8).derivative =
      Polynomial.C (4 : K) * p.coeff 8 * (q.coeff 10).derivative := by
  have hweighted := leadingCoefficient_weightedWronskian
    hp hq (by norm_num) (by norm_num) hjac
  have hC2 : Polynomial.C (2 : K) ≠ 0 := by norm_num
  have hC25 : Polynomial.C (2 : K) * Polynomial.C (5 : K) =
      Polynomial.C (10 : K) := by
    rw [← Polynomial.C_mul]
    norm_num
  have hC24 : Polynomial.C (2 : K) * Polynomial.C (4 : K) =
      Polynomial.C (8 : K) := by
    rw [← Polynomial.C_mul]
    norm_num
  apply mul_left_cancel₀ hC2
  calc
    Polynomial.C (2 : K) *
        (Polynomial.C (5 : K) * q.coeff 10 * (p.coeff 8).derivative) =
        Polynomial.C (10 : K) * q.coeff 10 *
          (p.coeff 8).derivative := by rw [← hC25]; ring
    _ = Polynomial.C (8 : K) * p.coeff 8 *
          (q.coeff 10).derivative := hweighted
    _ = Polynomial.C (2 : K) *
        (Polynomial.C (4 : K) * p.coeff 8 *
          (q.coeff 10).derivative) := by rw [← hC24]; ring

/-- The `(4,10)` leading row reduces from weights `(4,10)` to `(2,5)`. -/
theorem reducedLeadingCoefficientWeightedWronskian_410 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    Polynomial.C (5 : K) * q.coeff 10 * (p.coeff 4).derivative =
      Polynomial.C (2 : K) * p.coeff 4 * (q.coeff 10).derivative := by
  have hweighted := leadingCoefficient_weightedWronskian
    hp hq (by norm_num) (by norm_num) hjac
  have hC2 : Polynomial.C (2 : K) ≠ 0 := by norm_num
  have hC25 : Polynomial.C (2 : K) * Polynomial.C (5 : K) =
      Polynomial.C (10 : K) := by rw [← Polynomial.C_mul]; norm_num
  have hC22 : Polynomial.C (2 : K) * Polynomial.C (2 : K) =
      Polynomial.C (4 : K) := by rw [← Polynomial.C_mul]; norm_num
  apply mul_left_cancel₀ hC2
  calc
    Polynomial.C (2 : K) *
        (Polynomial.C (5 : K) * q.coeff 10 * (p.coeff 4).derivative) =
        Polynomial.C (10 : K) * q.coeff 10 *
          (p.coeff 4).derivative := by rw [← hC25]; ring
    _ = Polynomial.C (4 : K) * p.coeff 4 *
          (q.coeff 10).derivative := hweighted
    _ = Polynomial.C (2 : K) *
        (Polynomial.C (2 : K) * p.coeff 4 *
          (q.coeff 10).derivative) := by rw [← hC22]; ring

/-- The `(6,10)` leading row reduces from weights `(6,10)` to `(3,5)`. -/
theorem reducedLeadingCoefficientWeightedWronskian_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    Polynomial.C (5 : K) * q.coeff 10 * (p.coeff 6).derivative =
      Polynomial.C (3 : K) * p.coeff 6 * (q.coeff 10).derivative := by
  have hweighted := leadingCoefficient_weightedWronskian
    hp hq (by norm_num) (by norm_num) hjac
  have hC2 : Polynomial.C (2 : K) ≠ 0 := by norm_num
  have hC25 : Polynomial.C (2 : K) * Polynomial.C (5 : K) =
      Polynomial.C (10 : K) := by rw [← Polynomial.C_mul]; norm_num
  have hC23 : Polynomial.C (2 : K) * Polynomial.C (3 : K) =
      Polynomial.C (6 : K) := by rw [← Polynomial.C_mul]; norm_num
  apply mul_left_cancel₀ hC2
  calc
    Polynomial.C (2 : K) *
        (Polynomial.C (5 : K) * q.coeff 10 * (p.coeff 6).derivative) =
        Polynomial.C (10 : K) * q.coeff 10 *
          (p.coeff 6).derivative := by rw [← hC25]; ring
    _ = Polynomial.C (6 : K) * p.coeff 6 *
          (q.coeff 10).derivative := hweighted
    _ = Polynomial.C (2 : K) *
        (Polynomial.C (3 : K) * p.coeff 6 *
          (q.coeff 10).derivative) := by rw [← hC23]; ring

/-- A genuine partial-degree `(4,6)` Keller pair has a nonzero square/cube
common leading core. -/
theorem planeKellerPair_46_commonCore {K : Type*}
    [Field K] [CharZero K] {P Q : MvPolynomial (Fin 2) K}
    (hP : degreeOf 1 P = 4) (hQ : degreeOf 1 Q = 6)
    (hKeller : IsPlaneKellerPair P Q) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (alpha beta : K) (h : K[X]),
      alpha ≠ 0 ∧ beta ≠ 0 ∧ h ≠ 0 ∧
        p.coeff 4 = Polynomial.C alpha * h ^ 2 ∧
        q.coeff 6 = Polynomial.C beta * h ^ 3 := by
  dsimp only
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hpdegree : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hP
  have hqdegree : q.natDegree = 6 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQ
  have hp : p ≠ 0 := by
    intro hpzero
    rw [hpzero, Polynomial.natDegree_zero] at hpdegree
    omega
  have hq : q ≠ 0 := by
    intro hqzero
    rw [hqzero, Polynomial.natDegree_zero] at hqdegree
    omega
  have hA : p.coeff 4 ≠ 0 := by
    rw [← hpdegree, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have hB : q.coeff 6 ≠ 0 := by
    rw [← hqdegree, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hq
  obtain ⟨j, -, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  exact commonCore_of_reducedWeightedWronskian_23 hA hB
    (reducedLeadingCoefficientWeightedWronskian_46 hpdegree hqdegree hjac)

/-- A genuine partial-degree `(6,8)` Keller pair has a nonzero cube/fourth-
power common leading core. -/
theorem planeKellerPair_68_commonCore {K : Type*}
    [Field K] [CharZero K] {P Q : MvPolynomial (Fin 2) K}
    (hP : degreeOf 1 P = 6) (hQ : degreeOf 1 Q = 8)
    (hKeller : IsPlaneKellerPair P Q) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (alpha beta : K) (h : K[X]),
      alpha ≠ 0 ∧ beta ≠ 0 ∧ h ≠ 0 ∧
        p.coeff 6 = Polynomial.C alpha * h ^ 3 ∧
        q.coeff 8 = Polynomial.C beta * h ^ 4 := by
  dsimp only
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hpdegree : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hP
  have hqdegree : q.natDegree = 8 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQ
  have hp : p ≠ 0 := by
    intro hpzero
    rw [hpzero, Polynomial.natDegree_zero] at hpdegree
    omega
  have hq : q ≠ 0 := by
    intro hqzero
    rw [hqzero, Polynomial.natDegree_zero] at hqdegree
    omega
  have hA : p.coeff 6 ≠ 0 := by
    rw [← hpdegree, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have hB : q.coeff 8 ≠ 0 := by
    rw [← hqdegree, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hq
  obtain ⟨j, -, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  exact commonCore_of_reducedWeightedWronskian_34 hA hB
    (reducedLeadingCoefficientWeightedWronskian_68 hpdegree hqdegree hjac)

/-- A genuine partial-degree `(8,10)` Keller pair has a nonzero fourth/fifth-
power common leading core. -/
theorem planeKellerPair_810_commonCore {K : Type*}
    [Field K] [CharZero K] {P Q : MvPolynomial (Fin 2) K}
    (hP : degreeOf 1 P = 8) (hQ : degreeOf 1 Q = 10)
    (hKeller : IsPlaneKellerPair P Q) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (alpha beta : K) (h : K[X]),
      alpha ≠ 0 ∧ beta ≠ 0 ∧ h ≠ 0 ∧
        p.coeff 8 = Polynomial.C alpha * h ^ 4 ∧
        q.coeff 10 = Polynomial.C beta * h ^ 5 := by
  dsimp only
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hpdegree : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hP
  have hqdegree : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQ
  have hp : p ≠ 0 := by
    intro hpzero
    rw [hpzero, Polynomial.natDegree_zero] at hpdegree
    omega
  have hq : q ≠ 0 := by
    intro hqzero
    rw [hqzero, Polynomial.natDegree_zero] at hqdegree
    omega
  have hA : p.coeff 8 ≠ 0 := by
    rw [← hpdegree, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have hB : q.coeff 10 ≠ 0 := by
    rw [← hqdegree, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hq
  obtain ⟨j, -, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  exact commonCore_of_reducedWeightedWronskian_45 hA hB
    (reducedLeadingCoefficientWeightedWronskian_810 hpdegree hqdegree hjac)

/-- A genuine partial-degree `(4,10)` Keller pair has a nonzero square/fifth-
power common leading core. -/
theorem planeKellerPair_410_commonCore {K : Type*}
    [Field K] [CharZero K] {P Q : MvPolynomial (Fin 2) K}
    (hP : degreeOf 1 P = 4) (hQ : degreeOf 1 Q = 10)
    (hKeller : IsPlaneKellerPair P Q) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (alpha beta : K) (h : K[X]),
      alpha ≠ 0 ∧ beta ≠ 0 ∧ h ≠ 0 ∧
        p.coeff 4 = Polynomial.C alpha * h ^ 2 ∧
        q.coeff 10 = Polynomial.C beta * h ^ 5 := by
  dsimp only
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hpdegree : p.natDegree = 4 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hP
  have hqdegree : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQ
  have hp : p ≠ 0 := by
    intro hpzero
    rw [hpzero, Polynomial.natDegree_zero] at hpdegree
    omega
  have hq : q ≠ 0 := by
    intro hqzero
    rw [hqzero, Polynomial.natDegree_zero] at hqdegree
    omega
  have hA : p.coeff 4 ≠ 0 := by
    rw [← hpdegree, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have hB : q.coeff 10 ≠ 0 := by
    rw [← hqdegree, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hq
  obtain ⟨j, -, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  exact commonCore_of_reducedWeightedWronskian_25 hA hB
    (reducedLeadingCoefficientWeightedWronskian_410 hpdegree hqdegree hjac)

/-- A genuine partial-degree `(6,10)` Keller pair has a nonzero cube/fifth-
power common leading core. -/
theorem planeKellerPair_610_commonCore {K : Type*}
    [Field K] [CharZero K] {P Q : MvPolynomial (Fin 2) K}
    (hP : degreeOf 1 P = 6) (hQ : degreeOf 1 Q = 10)
    (hKeller : IsPlaneKellerPair P Q) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ (alpha beta : K) (h : K[X]),
      alpha ≠ 0 ∧ beta ≠ 0 ∧ h ≠ 0 ∧
        p.coeff 6 = Polynomial.C alpha * h ^ 3 ∧
        q.coeff 10 = Polynomial.C beta * h ^ 5 := by
  dsimp only
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hpdegree : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hP
  have hqdegree : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQ
  have hp : p ≠ 0 := by
    intro hpzero
    rw [hpzero, Polynomial.natDegree_zero] at hpdegree
    omega
  have hq : q ≠ 0 := by
    intro hqzero
    rw [hqzero, Polynomial.natDegree_zero] at hqdegree
    omega
  have hA : p.coeff 6 ≠ 0 := by
    rw [← hpdegree, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have hB : q.coeff 10 ≠ 0 := by
    rw [← hqdegree, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hq
  obtain ⟨j, -, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  exact commonCore_of_reducedWeightedWronskian_35 hA hB
    (reducedLeadingCoefficientWeightedWronskian_610 hpdegree hqdegree hjac)

/-- Exact normalized source data for a pair with consecutive reduced weights
`(r,r+1)` and original partial degrees `(2r,2(r+1))`. -/
def NormalizedConsecutiveLeadingCoreSource {K : Type*} [Field K]
    (r : ℕ) (P Q : MvPolynomial (Fin 2) K) (h : K[X]) (H : ℕ) : Prop :=
  h ≠ 0 ∧ h.natDegree = H ∧
  degreeOf 1 P = 2 * r ∧ degreeOf 1 Q = 2 * (r + 1) ∧
  ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff (2 * r) = h ^ r ∧
  ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff (2 * (r + 1)) =
    h ^ (r + 1) ∧
  IsPlaneKellerPair P Q

/-- The unresolved normalized low-scale source for consecutive reduced
weights. -/
def PlaneKellerNormalizedConsecutiveLowScaleRoute
    {K : Type*} [Field K] (r : ℕ) : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (h : K[X]) (H : ℕ),
    (H = 0 ∨ H = 2) → NormalizedConsecutiveLeadingCoreSource r P Q h H →
    PlanePairGenerates P Q

/-- Independent target rescalings remove the two scalar units from any
consecutive-power common core, without changing generation. -/
theorem planeKellerPair_consecutive_normalizeAtScale {K : Type*}
    [Field K] {r H : ℕ} (hr : 0 < r)
    {P Q : MvPolynomial (Fin 2) K}
    (hP : degreeOf 1 P = 2 * r) (hQ : degreeOf 1 Q = 2 * (r + 1))
    (hKeller : IsPlaneKellerPair P Q)
    (hcore : ∃ (alpha beta : K) (h : K[X]),
      alpha ≠ 0 ∧ beta ≠ 0 ∧ h ≠ 0 ∧
      ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff (2 * r) =
        Polynomial.C alpha * h ^ r ∧
      ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff (2 * (r + 1)) =
        Polynomial.C beta * h ^ (r + 1))
    (hAdegree :
      (((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff
        (2 * r)).natDegree = r * H) :
    ∃ (P0 Q0 : MvPolynomial (Fin 2) K) (h : K[X]),
      NormalizedConsecutiveLeadingCoreSource r P0 Q0 h H ∧
      (PlanePairGenerates P0 Q0 ↔ PlanePairGenerates P Q) := by
  obtain ⟨alpha, beta, h, halpha, hbeta, hh, hAtop, hBtop⟩ := hcore
  have hhdegree : h.natDegree = H := by
    have hdegree : r * H = r * h.natDegree := by
      calc
        r * H =
            (((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff
              (2 * r)).natDegree := hAdegree.symm
        _ = (Polynomial.C alpha * h ^ r).natDegree := by rw [hAtop]
        _ = (h ^ r).natDegree := Polynomial.natDegree_C_mul halpha
        _ = r * h.natDegree := Polynomial.natDegree_pow h r
    exact Nat.eq_of_mul_eq_mul_left hr hdegree.symm
  let P0 := targetRescale alpha⁻¹ P
  let Q0 := targetRescale beta⁻¹ Q
  have hP0 : degreeOf 1 P0 = 2 * r := by
    dsimp only [P0]
    rw [targetRescale, MvPolynomial.degreeOf_C_mul 1 alpha⁻¹
      (mem_nonZeroDivisors_iff_ne_zero.mpr (inv_ne_zero halpha)), hP]
  have hQ0 : degreeOf 1 Q0 = 2 * (r + 1) := by
    dsimp only [Q0]
    rw [targetRescale, MvPolynomial.degreeOf_C_mul 1 beta⁻¹
      (mem_nonZeroDivisors_iff_ne_zero.mpr (inv_ne_zero hbeta)), hQ]
  have hP0top :
      ((Polynomial.Bivariate.equivMvPolynomial K).symm P0).coeff (2 * r) =
        h ^ r := by
    dsimp only [P0]
    simp only [targetRescale, map_mul,
      Polynomial.Bivariate.equivMvPolynomial_symm_C,
      Polynomial.coeff_C_mul, hAtop, ← mul_assoc,
      ← Polynomial.C_mul, inv_mul_cancel₀ halpha, Polynomial.C_1, one_mul]
  have hQ0top :
      ((Polynomial.Bivariate.equivMvPolynomial K).symm Q0).coeff (2 * (r + 1)) =
        h ^ (r + 1) := by
    dsimp only [Q0]
    simp only [targetRescale, map_mul,
      Polynomial.Bivariate.equivMvPolynomial_symm_C,
      Polynomial.coeff_C_mul, hBtop, ← mul_assoc,
      ← Polynomial.C_mul, inv_mul_cancel₀ hbeta, Polynomial.C_1, one_mul]
  have hKeller0 : IsPlaneKellerPair P0 Q0 :=
    Max11DegreeRoutes.IsPlaneKellerPair.targetRescale hKeller
      alpha⁻¹ beta⁻¹ (inv_ne_zero halpha) (inv_ne_zero hbeta)
  refine ⟨P0, Q0, h,
    ⟨hh, hhdegree, hP0, hQ0, hP0top, hQ0top, hKeller0⟩, ?_⟩
  exact planePairGenerates_targetRescale_iff alpha⁻¹ beta⁻¹
    (inv_ne_zero halpha) (inv_ne_zero hbeta) P Q

/-- Normalized `(6,8)` source data. -/
abbrev Normalized68LeadingCoreSource {K : Type*} [Field K]
    (P Q : MvPolynomial (Fin 2) K) (h : K[X]) (H : ℕ) : Prop :=
  NormalizedConsecutiveLeadingCoreSource 3 P Q h H

/-- The exact unresolved normalized `(6,8)` source at scales zero and two. -/
abbrev PlaneKellerNormalized68LowScaleRoute
    {K : Type*} [Field K] : Prop :=
  PlaneKellerNormalizedConsecutiveLowScaleRoute (K := K) 3

/-- Normalized `(8,10)` source data. -/
abbrev Normalized810LeadingCoreSource {K : Type*} [Field K]
    (P Q : MvPolynomial (Fin 2) K) (h : K[X]) (H : ℕ) : Prop :=
  NormalizedConsecutiveLeadingCoreSource 4 P Q h H

/-- The exact unresolved normalized `(8,10)` source at scales zero and two. -/
abbrev PlaneKellerNormalized810LowScaleRoute
    {K : Type*} [Field K] : Prop :=
  PlaneKellerNormalizedConsecutiveLowScaleRoute (K := K) 4

/-- Exact normalized source data for arbitrary reduced leading weights
`(r,s)` and original partial degrees `(2r,2s)`. -/
def NormalizedCoprimeLeadingCoreSource {K : Type*} [Field K]
    (r s : ℕ) (P Q : MvPolynomial (Fin 2) K) (h : K[X]) (H : ℕ) : Prop :=
  h ≠ 0 ∧ h.natDegree = H ∧
  degreeOf 1 P = 2 * r ∧ degreeOf 1 Q = 2 * s ∧
  ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff (2 * r) = h ^ r ∧
  ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff (2 * s) = h ^ s ∧
  IsPlaneKellerPair P Q

/-- The unresolved normalized low-scale source for reduced weights `(r,s)`. -/
def PlaneKellerNormalizedCoprimeLowScaleRoute
    {K : Type*} [Field K] (r s : ℕ) : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (h : K[X]) (H : ℕ),
    (H = 0 ∨ H = 2) → NormalizedCoprimeLeadingCoreSource r s P Q h H →
    PlanePairGenerates P Q

/-- Target rescaling normalizes any supplied `(r,s)` common core while
preserving the generated subalgebra. -/
theorem planeKellerPair_coprime_normalizeAtScale {K : Type*}
    [Field K] {r s H : ℕ} (hr : 0 < r)
    {P Q : MvPolynomial (Fin 2) K}
    (hP : degreeOf 1 P = 2 * r) (hQ : degreeOf 1 Q = 2 * s)
    (hKeller : IsPlaneKellerPair P Q)
    (hcore : ∃ (alpha beta : K) (h : K[X]),
      alpha ≠ 0 ∧ beta ≠ 0 ∧ h ≠ 0 ∧
      ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff (2 * r) =
        Polynomial.C alpha * h ^ r ∧
      ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff (2 * s) =
        Polynomial.C beta * h ^ s)
    (hAdegree :
      (((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff
        (2 * r)).natDegree = r * H) :
    ∃ (P0 Q0 : MvPolynomial (Fin 2) K) (h : K[X]),
      NormalizedCoprimeLeadingCoreSource r s P0 Q0 h H ∧
      (PlanePairGenerates P0 Q0 ↔ PlanePairGenerates P Q) := by
  obtain ⟨alpha, beta, h, halpha, hbeta, hh, hAtop, hBtop⟩ := hcore
  have hhdegree : h.natDegree = H := by
    have hdegree : r * H = r * h.natDegree := by
      calc
        r * H =
            (((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff
              (2 * r)).natDegree := hAdegree.symm
        _ = (Polynomial.C alpha * h ^ r).natDegree := by rw [hAtop]
        _ = (h ^ r).natDegree := Polynomial.natDegree_C_mul halpha
        _ = r * h.natDegree := Polynomial.natDegree_pow h r
    exact Nat.eq_of_mul_eq_mul_left hr hdegree.symm
  let P0 := targetRescale alpha⁻¹ P
  let Q0 := targetRescale beta⁻¹ Q
  have hP0 : degreeOf 1 P0 = 2 * r := by
    dsimp only [P0]
    rw [targetRescale, MvPolynomial.degreeOf_C_mul 1 alpha⁻¹
      (mem_nonZeroDivisors_iff_ne_zero.mpr (inv_ne_zero halpha)), hP]
  have hQ0 : degreeOf 1 Q0 = 2 * s := by
    dsimp only [Q0]
    rw [targetRescale, MvPolynomial.degreeOf_C_mul 1 beta⁻¹
      (mem_nonZeroDivisors_iff_ne_zero.mpr (inv_ne_zero hbeta)), hQ]
  have hP0top :
      ((Polynomial.Bivariate.equivMvPolynomial K).symm P0).coeff (2 * r) =
        h ^ r := by
    dsimp only [P0]
    simp only [targetRescale, map_mul,
      Polynomial.Bivariate.equivMvPolynomial_symm_C,
      Polynomial.coeff_C_mul, hAtop, ← mul_assoc,
      ← Polynomial.C_mul, inv_mul_cancel₀ halpha, Polynomial.C_1, one_mul]
  have hQ0top :
      ((Polynomial.Bivariate.equivMvPolynomial K).symm Q0).coeff (2 * s) =
        h ^ s := by
    dsimp only [Q0]
    simp only [targetRescale, map_mul,
      Polynomial.Bivariate.equivMvPolynomial_symm_C,
      Polynomial.coeff_C_mul, hBtop, ← mul_assoc,
      ← Polynomial.C_mul, inv_mul_cancel₀ hbeta, Polynomial.C_1, one_mul]
  have hKeller0 : IsPlaneKellerPair P0 Q0 :=
    Max11DegreeRoutes.IsPlaneKellerPair.targetRescale hKeller
      alpha⁻¹ beta⁻¹ (inv_ne_zero halpha) (inv_ne_zero hbeta)
  refine ⟨P0, Q0, h,
    ⟨hh, hhdegree, hP0, hQ0, hP0top, hQ0top, hKeller0⟩, ?_⟩
  exact planePairGenerates_targetRescale_iff alpha⁻¹ beta⁻¹
    (inv_ne_zero halpha) (inv_ne_zero hbeta) P Q

/-- Normalized `(4,10)` source data. -/
abbrev Normalized410LeadingCoreSource {K : Type*} [Field K]
    (P Q : MvPolynomial (Fin 2) K) (h : K[X]) (H : ℕ) : Prop :=
  NormalizedCoprimeLeadingCoreSource 2 5 P Q h H

/-- The exact unresolved normalized `(4,10)` source at scales zero and two. -/
abbrev PlaneKellerNormalized410LowScaleRoute
    {K : Type*} [Field K] : Prop :=
  PlaneKellerNormalizedCoprimeLowScaleRoute (K := K) 2 5

/-- Normalized `(6,10)` source data. -/
abbrev Normalized610LeadingCoreSource {K : Type*} [Field K]
    (P Q : MvPolynomial (Fin 2) K) (h : K[X]) (H : ℕ) : Prop :=
  NormalizedCoprimeLeadingCoreSource 3 5 P Q h H

/-- The exact unresolved normalized `(6,10)` source at scales zero and two. -/
abbrev PlaneKellerNormalized610LowScaleRoute
    {K : Type*} [Field K] : Prop :=
  PlaneKellerNormalizedCoprimeLowScaleRoute (K := K) 3 5

/-- Exact normalized source data for the `(4,6)` leaf at common scale `H`. -/
def Normalized46LeadingCoreSource {K : Type*} [Field K]
    (P Q : MvPolynomial (Fin 2) K) (h : K[X]) (H : ℕ) : Prop :=
  h ≠ 0 ∧ h.natDegree = H ∧
  degreeOf 1 P = 4 ∧ degreeOf 1 Q = 6 ∧
  ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 4 = h ^ 2 ∧
  ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff 6 = h ^ 3 ∧
  IsPlaneKellerPair P Q

/-- The exact unresolved normalized `(4,6)` source at the two low scales. -/
def PlaneKellerNormalized46LowScaleRoute
    {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (h : K[X]) (H : ℕ),
    (H = 0 ∨ H = 2) → Normalized46LeadingCoreSource P Q h H →
    PlanePairGenerates P Q

/-- A `(4,6)` pair at a specified common scale normalizes by independent
target rescalings, and the extracted common core has exactly that scale. -/
theorem planeKellerPair_46_normalizeAtScale {K : Type*}
    [Field K] [CharZero K] {P Q : MvPolynomial (Fin 2) K} {H : ℕ}
    (hP : degreeOf 1 P = 4) (hQ : degreeOf 1 Q = 6)
    (hKeller : IsPlaneKellerPair P Q)
    (hAdegree :
      (((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 4).natDegree =
        2 * H) :
    ∃ (P0 Q0 : MvPolynomial (Fin 2) K) (h : K[X]),
      Normalized46LeadingCoreSource P0 Q0 h H ∧
      (PlanePairGenerates P0 Q0 ↔ PlanePairGenerates P Q) := by
  obtain ⟨alpha, beta, h, halpha, hbeta, hh, hAtop, hBtop⟩ :=
    planeKellerPair_46_commonCore hP hQ hKeller
  have hhdegree : h.natDegree = H := by
    have hdegree : 2 * H = 2 * h.natDegree := by
      calc
        2 * H =
            (((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 4).natDegree :=
          hAdegree.symm
        _ = (Polynomial.C alpha * h ^ 2).natDegree := by rw [hAtop]
        _ = (h ^ 2).natDegree := Polynomial.natDegree_C_mul halpha
        _ = 2 * h.natDegree := Polynomial.natDegree_pow h 2
    omega
  let P0 := targetRescale alpha⁻¹ P
  let Q0 := targetRescale beta⁻¹ Q
  have hP0 : degreeOf 1 P0 = 4 := by
    dsimp only [P0]
    rw [targetRescale, MvPolynomial.degreeOf_C_mul 1 alpha⁻¹
      (mem_nonZeroDivisors_iff_ne_zero.mpr (inv_ne_zero halpha)), hP]
  have hQ0 : degreeOf 1 Q0 = 6 := by
    dsimp only [Q0]
    rw [targetRescale, MvPolynomial.degreeOf_C_mul 1 beta⁻¹
      (mem_nonZeroDivisors_iff_ne_zero.mpr (inv_ne_zero hbeta)), hQ]
  have hP0top :
      ((Polynomial.Bivariate.equivMvPolynomial K).symm P0).coeff 4 = h ^ 2 := by
    dsimp only [P0]
    simp only [targetRescale, map_mul,
      Polynomial.Bivariate.equivMvPolynomial_symm_C,
      Polynomial.coeff_C_mul, hAtop, ← mul_assoc,
      ← Polynomial.C_mul, inv_mul_cancel₀ halpha, Polynomial.C_1, one_mul]
  have hQ0top :
      ((Polynomial.Bivariate.equivMvPolynomial K).symm Q0).coeff 6 = h ^ 3 := by
    dsimp only [Q0]
    simp only [targetRescale, map_mul,
      Polynomial.Bivariate.equivMvPolynomial_symm_C,
      Polynomial.coeff_C_mul, hBtop, ← mul_assoc,
      ← Polynomial.C_mul, inv_mul_cancel₀ hbeta, Polynomial.C_1, one_mul]
  have hKeller0 : IsPlaneKellerPair P0 Q0 := by
    exact Max11DegreeRoutes.IsPlaneKellerPair.targetRescale hKeller
      alpha⁻¹ beta⁻¹ (inv_ne_zero halpha) (inv_ne_zero hbeta)
  refine ⟨P0, Q0, h,
    ⟨hh, hhdegree, hP0, hQ0, hP0top, hQ0top, hKeller0⟩, ?_⟩
  exact planePairGenerates_targetRescale_iff alpha⁻¹ beta⁻¹
    (inv_ne_zero halpha) (inv_ne_zero hbeta) P Q

/-- The normalized two-scale `(4,6)` route supplies both literal low-scale
leaves required by the endpoint reduction. -/
theorem planeKellerLowEvenLeadingScalesAtDegrees_46_of_normalized
    {K : Type*} [Field K] [CharZero K]
    (hnormalized : PlaneKellerNormalized46LowScaleRoute (K := K)) :
    PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 4 6 := by
  constructor
  · intro P Q hP hQ hKeller hAdegree _hBdegree
    obtain ⟨P0, Q0, h, hsource, hgenerates⟩ :=
      planeKellerPair_46_normalizeAtScale (H := 0) hP hQ hKeller
        (by simpa using hAdegree)
    exact hgenerates.mp (hnormalized P0 Q0 h 0 (Or.inl rfl) hsource)
  · intro P Q hP hQ hKeller hAdegree _hBdegree
    obtain ⟨P0, Q0, h, hsource, hgenerates⟩ :=
      planeKellerPair_46_normalizeAtScale (H := 2) hP hQ hKeller
        (by simpa using hAdegree)
    exact hgenerates.mp (hnormalized P0 Q0 h 2 (Or.inr rfl) hsource)

/-- A `(6,8)` pair at a specified common scale normalizes to exact leading
rows `h^3,h^4`. -/
theorem planeKellerPair_68_normalizeAtScale {K : Type*}
    [Field K] [CharZero K] {P Q : MvPolynomial (Fin 2) K} {H : ℕ}
    (hP : degreeOf 1 P = 6) (hQ : degreeOf 1 Q = 8)
    (hKeller : IsPlaneKellerPair P Q)
    (hAdegree :
      (((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 6).natDegree =
        3 * H) :
    ∃ (P0 Q0 : MvPolynomial (Fin 2) K) (h : K[X]),
      Normalized68LeadingCoreSource P0 Q0 h H ∧
      (PlanePairGenerates P0 Q0 ↔ PlanePairGenerates P Q) := by
  exact planeKellerPair_consecutive_normalizeAtScale (r := 3)
    (by norm_num) (by simpa using hP) (by simpa using hQ) hKeller
    (by simpa using planeKellerPair_68_commonCore hP hQ hKeller)
    (by simpa using hAdegree)

/-- The normalized two-scale `(6,8)` route supplies both literal low-scale
leaves required by the endpoint reduction. -/
theorem planeKellerLowEvenLeadingScalesAtDegrees_68_of_normalized
    {K : Type*} [Field K] [CharZero K]
    (hnormalized : PlaneKellerNormalized68LowScaleRoute (K := K)) :
    PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 6 8 := by
  constructor
  · intro P Q hP hQ hKeller hAdegree _hBdegree
    obtain ⟨P0, Q0, h, hsource, hgenerates⟩ :=
      planeKellerPair_68_normalizeAtScale (H := 0) hP hQ hKeller
        (by simpa using hAdegree)
    exact hgenerates.mp (hnormalized P0 Q0 h 0 (Or.inl rfl) hsource)
  · intro P Q hP hQ hKeller hAdegree _hBdegree
    obtain ⟨P0, Q0, h, hsource, hgenerates⟩ :=
      planeKellerPair_68_normalizeAtScale (H := 2) hP hQ hKeller
        (by simpa using hAdegree)
    exact hgenerates.mp (hnormalized P0 Q0 h 2 (Or.inr rfl) hsource)

/-- An `(8,10)` pair at a specified common scale normalizes to exact leading
rows `h^4,h^5`. -/
theorem planeKellerPair_810_normalizeAtScale {K : Type*}
    [Field K] [CharZero K] {P Q : MvPolynomial (Fin 2) K} {H : ℕ}
    (hP : degreeOf 1 P = 8) (hQ : degreeOf 1 Q = 10)
    (hKeller : IsPlaneKellerPair P Q)
    (hAdegree :
      (((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 8).natDegree =
        4 * H) :
    ∃ (P0 Q0 : MvPolynomial (Fin 2) K) (h : K[X]),
      Normalized810LeadingCoreSource P0 Q0 h H ∧
      (PlanePairGenerates P0 Q0 ↔ PlanePairGenerates P Q) := by
  exact planeKellerPair_consecutive_normalizeAtScale (r := 4)
    (by norm_num) (by simpa using hP) (by simpa using hQ) hKeller
    (by simpa using planeKellerPair_810_commonCore hP hQ hKeller)
    (by simpa using hAdegree)

/-- The normalized two-scale `(8,10)` route supplies both literal low-scale
leaves required by the endpoint reduction. -/
theorem planeKellerLowEvenLeadingScalesAtDegrees_810_of_normalized
    {K : Type*} [Field K] [CharZero K]
    (hnormalized : PlaneKellerNormalized810LowScaleRoute (K := K)) :
    PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 8 10 := by
  constructor
  · intro P Q hP hQ hKeller hAdegree _hBdegree
    obtain ⟨P0, Q0, h, hsource, hgenerates⟩ :=
      planeKellerPair_810_normalizeAtScale (H := 0) hP hQ hKeller
        (by simpa using hAdegree)
    exact hgenerates.mp (hnormalized P0 Q0 h 0 (Or.inl rfl) hsource)
  · intro P Q hP hQ hKeller hAdegree _hBdegree
    obtain ⟨P0, Q0, h, hsource, hgenerates⟩ :=
      planeKellerPair_810_normalizeAtScale (H := 2) hP hQ hKeller
        (by simpa using hAdegree)
    exact hgenerates.mp (hnormalized P0 Q0 h 2 (Or.inr rfl) hsource)

/-- A `(4,10)` pair at a specified common scale normalizes to exact leading
rows `h^2,h^5`. -/
theorem planeKellerPair_410_normalizeAtScale {K : Type*}
    [Field K] [CharZero K] {P Q : MvPolynomial (Fin 2) K} {H : ℕ}
    (hP : degreeOf 1 P = 4) (hQ : degreeOf 1 Q = 10)
    (hKeller : IsPlaneKellerPair P Q)
    (hAdegree :
      (((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 4).natDegree =
        2 * H) :
    ∃ (P0 Q0 : MvPolynomial (Fin 2) K) (h : K[X]),
      Normalized410LeadingCoreSource P0 Q0 h H ∧
      (PlanePairGenerates P0 Q0 ↔ PlanePairGenerates P Q) := by
  exact planeKellerPair_coprime_normalizeAtScale (r := 2) (s := 5)
    (by norm_num) (by simpa using hP) (by simpa using hQ) hKeller
    (by simpa using planeKellerPair_410_commonCore hP hQ hKeller)
    (by simpa using hAdegree)

/-- The normalized two-scale `(4,10)` route supplies both literal low-scale
leaves required by the endpoint reduction. -/
theorem planeKellerLowEvenLeadingScalesAtDegrees_410_of_normalized
    {K : Type*} [Field K] [CharZero K]
    (hnormalized : PlaneKellerNormalized410LowScaleRoute (K := K)) :
    PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 4 10 := by
  constructor
  · intro P Q hP hQ hKeller hAdegree _hBdegree
    obtain ⟨P0, Q0, h, hsource, hgenerates⟩ :=
      planeKellerPair_410_normalizeAtScale (H := 0) hP hQ hKeller
        (by simpa using hAdegree)
    exact hgenerates.mp (hnormalized P0 Q0 h 0 (Or.inl rfl) hsource)
  · intro P Q hP hQ hKeller hAdegree _hBdegree
    obtain ⟨P0, Q0, h, hsource, hgenerates⟩ :=
      planeKellerPair_410_normalizeAtScale (H := 2) hP hQ hKeller
        (by simpa using hAdegree)
    exact hgenerates.mp (hnormalized P0 Q0 h 2 (Or.inr rfl) hsource)

/-- A `(6,10)` pair at a specified common scale normalizes to exact leading
rows `h^3,h^5`. -/
theorem planeKellerPair_610_normalizeAtScale {K : Type*}
    [Field K] [CharZero K] {P Q : MvPolynomial (Fin 2) K} {H : ℕ}
    (hP : degreeOf 1 P = 6) (hQ : degreeOf 1 Q = 10)
    (hKeller : IsPlaneKellerPair P Q)
    (hAdegree :
      (((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 6).natDegree =
        3 * H) :
    ∃ (P0 Q0 : MvPolynomial (Fin 2) K) (h : K[X]),
      Normalized610LeadingCoreSource P0 Q0 h H ∧
      (PlanePairGenerates P0 Q0 ↔ PlanePairGenerates P Q) := by
  exact planeKellerPair_coprime_normalizeAtScale (r := 3) (s := 5)
    (by norm_num) (by simpa using hP) (by simpa using hQ) hKeller
    (by simpa using planeKellerPair_610_commonCore hP hQ hKeller)
    (by simpa using hAdegree)

/-- The normalized two-scale `(6,10)` route supplies both literal low-scale
leaves required by the endpoint reduction. -/
theorem planeKellerLowEvenLeadingScalesAtDegrees_610_of_normalized
    {K : Type*} [Field K] [CharZero K]
    (hnormalized : PlaneKellerNormalized610LowScaleRoute (K := K)) :
    PlaneKellerLowEvenLeadingScalesAtDegrees (K := K) 6 10 := by
  constructor
  · intro P Q hP hQ hKeller hAdegree _hBdegree
    obtain ⟨P0, Q0, h, hsource, hgenerates⟩ :=
      planeKellerPair_610_normalizeAtScale (H := 0) hP hQ hKeller
        (by simpa using hAdegree)
    exact hgenerates.mp (hnormalized P0 Q0 h 0 (Or.inl rfl) hsource)
  · intro P Q hP hQ hKeller hAdegree _hBdegree
    obtain ⟨P0, Q0, h, hsource, hgenerates⟩ :=
      planeKellerPair_610_normalizeAtScale (H := 2) hP hQ hKeller
        (by simpa using hAdegree)
    exact hgenerates.mp (hnormalized P0 Q0 h 2 (Or.inr rfl) hsource)

#print axioms commonCore_of_reducedWeightedWronskian_23
#print axioms commonCore_of_reducedWeightedWronskian_34
#print axioms commonCore_of_reducedWeightedWronskian_45
#print axioms commonCore_of_reducedWeightedWronskian_25
#print axioms commonCore_of_reducedWeightedWronskian_35
#print axioms reducedLeadingCoefficientWeightedWronskian_46
#print axioms reducedLeadingCoefficientWeightedWronskian_68
#print axioms reducedLeadingCoefficientWeightedWronskian_810
#print axioms reducedLeadingCoefficientWeightedWronskian_410
#print axioms reducedLeadingCoefficientWeightedWronskian_610
#print axioms planeKellerPair_46_commonCore
#print axioms planeKellerPair_68_commonCore
#print axioms planeKellerPair_810_commonCore
#print axioms planeKellerPair_410_commonCore
#print axioms planeKellerPair_610_commonCore
#print axioms planeKellerPair_46_normalizeAtScale
#print axioms planeKellerPair_68_normalizeAtScale
#print axioms planeKellerPair_810_normalizeAtScale
#print axioms planeKellerPair_410_normalizeAtScale
#print axioms planeKellerPair_610_normalizeAtScale
#print axioms planeKellerLowEvenLeadingScalesAtDegrees_46_of_normalized
#print axioms planeKellerLowEvenLeadingScalesAtDegrees_68_of_normalized
#print axioms planeKellerLowEvenLeadingScalesAtDegrees_810_of_normalized
#print axioms planeKellerLowEvenLeadingScalesAtDegrees_410_of_normalized
#print axioms planeKellerLowEvenLeadingScalesAtDegrees_610_of_normalized

end Max11DegreeRoutes
