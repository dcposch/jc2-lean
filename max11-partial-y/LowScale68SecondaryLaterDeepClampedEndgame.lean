import LowScale68SecondaryLaterDeepMixedTwoNFace

/-! # Closing the clamped later-deep `(6,8)` chamber

Once `8n ≤ 2g`, the previous mixed-face argument gives `B = 0` and
`zeta = 0`.  The remaining cubic defect `c` is constant.  Writing
`s = (2/3)c₀ + gamma`, I4 makes `D` constant when `s ≠ 0`, while I3
makes `D²`, and hence `D`, constant when `s = 0`.

The first lower row then collapses to `-(4/9)d₀² A' = 0`.  A nonzero
`d₀` contradicts the nonconstant top of `A`; `d₀ = 0` makes the terminal
row vanish, contradicting its nonzero right-hand side.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepClampedEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The secondary bound clamps `c` to a scalar throughout `8n ≤ 2g`. -/
theorem cubicDefectPolynomial68_eq_C_of_clamped
    (c : k[X]) (n g : ℕ) (hdeep : 8 * n ≤ 2 * g)
    (hc : c.natDegree ≤ 4 * n - g) :
    ∃ c0 : k, c = C c0 := by
  have hcdeg : c.natDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    omega
  obtain ⟨c0, hc0⟩ := natDegree_eq_zero.mp hcdeg
  exact ⟨c0, hc0.symm⟩

/-- A scalar multiple of a polynomial which is constant, with nonzero
scalar, makes the polynomial itself constant. -/
theorem eq_C_of_smul_eq_C68 (a r : k) (p : k[X])
    (ha : a ≠ 0) (h : a • p = C r) :
    ∃ p0 : k, p = C p0 := by
  refine ⟨a⁻¹ * r, ?_⟩
  apply Polynomial.ext
  intro m
  have hm := congrArg (fun q : k[X] => q.coeff m) h
  by_cases hzero : m = 0
  · subst m
    simp only [coeff_smul, coeff_C, if_pos rfl, smul_eq_mul] at hm ⊢
    have hmr : a * p.coeff 0 = r := by simpa using hm
    calc
      p.coeff 0 = (a⁻¹ * a) * p.coeff 0 := by rw [inv_mul_cancel₀ ha, one_mul]
      _ = a⁻¹ * (a * p.coeff 0) := by ring
      _ = a⁻¹ * r := by rw [hmr]
  · simp only [coeff_smul, coeff_C, if_neg hzero, smul_eq_mul] at hm ⊢
    exact (mul_eq_zero.mp hm).resolve_left ha

/-- If the square of a polynomial is constant over a characteristic-zero
field, the polynomial is constant. -/
theorem eq_C_of_sq_eq_C68 (p : k[X]) (r : k) (h : p ^ 2 = C r) :
    ∃ p0 : k, p = C p0 := by
  have hdegpow : (p ^ 2).natDegree = 0 := by
    rw [h, natDegree_C]
  rw [natDegree_pow] at hdegpow
  have hdeg : p.natDegree = 0 := by omega
  obtain ⟨p0, hp0⟩ := natDegree_eq_zero.mp hdeg
  exact ⟨p0, hp0.symm⟩

/-- Exact invariant reduction after `B=zeta=0` and `c=C c₀`. -/
theorem cubicFirstIntegrals68_clamped_reduction
    (gamma epsilon i4 i3 c0 : k) (A D e : k[X])
    (hI4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon 0 A 0 (C c0) D e = C i4)
    (hI3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon 0 A 0 (C c0) D e = C i3) :
    let s : k := (2 / 3 : k) * c0 + gamma
    (4 * s : k) • D = C i4 ∧
      (4 / 3 : k) • D ^ 2 + (4 * s : k) • e +
        C ((2 * epsilon : k) * c0) = C i3 := by
  dsimp only
  constructor
  · rw [← hI4]
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [cubicFirstIntegralFourPolynomial68, smul_eq_C_mul,
      map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
      RatFunc.algebraMap_C]
    simp only [map_div₀, map_ofNat, map_natCast, map_one]
    ring
  · rw [← hI3]
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [cubicFirstIntegralThreePolynomial68, smul_eq_C_mul,
      map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
      RatFunc.algebraMap_C]
    simp only [map_div₀, map_ofNat, map_natCast, map_one]
    ring

/-- The `s≠0` / `s=0` invariant split.  Both branches force `D` constant;
the regular branch additionally forces `e` constant. -/
theorem cubicFirstIntegrals68_clamped_constant_split
    (gamma epsilon i4 i3 c0 : k) (A D e : k[X])
    (hI4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon 0 A 0 (C c0) D e = C i4)
    (hI3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon 0 A 0 (C c0) D e = C i3) :
    let s : k := (2 / 3 : k) * c0 + gamma
    (∃ d0 : k, D = C d0) ∧
      (s ≠ 0 → ∃ e0 : k, e = C e0) := by
  let s : k := (2 / 3 : k) * c0 + gamma
  have hred := cubicFirstIntegrals68_clamped_reduction
    gamma epsilon i4 i3 c0 A D e hI4 hI3
  change (4 * s : k) • D = C i4 ∧
    (4 / 3 : k) • D ^ 2 + (4 * s : k) • e +
      C ((2 * epsilon : k) * c0) = C i3 at hred
  by_cases hs : s = 0
  · have hsqsmul : (4 / 3 : k) • D ^ 2 =
        C (i3 - (2 * epsilon : k) * c0) := by
      rw [hs] at hred
      have h := hred.2
      simp only [mul_zero, zero_smul, add_zero] at h
      calc
        (4 / 3 : k) • D ^ 2 = C i3 - C ((2 * epsilon : k) * c0) := by
          rw [← h]
          ring
        _ = C (i3 - (2 * epsilon : k) * c0) := by rw [C_sub]
    obtain ⟨r, hsq⟩ := eq_C_of_smul_eq_C68
      (4 / 3 : k) (i3 - (2 * epsilon : k) * c0) (D ^ 2)
      (by norm_num) hsqsmul
    exact ⟨eq_C_of_sq_eq_C68 D r hsq, fun hsn ↦ (hsn hs).elim⟩
  · have hs4 : (4 * s : k) ≠ 0 := mul_ne_zero (by norm_num) hs
    obtain ⟨d0, hD⟩ := eq_C_of_smul_eq_C68 (4 * s) i4 D hs4 hred.1
    refine ⟨⟨d0, hD⟩, fun _ ↦ ?_⟩
    have hder := congrArg derivative hred.2
    rw [hD] at hder
    simp only [derivative_add, derivative_smul, derivative_pow,
      derivative_C, zero_mul, mul_zero, zero_add, add_zero,
      smul_zero] at hder
    have hde : derivative e = 0 :=
      (smul_eq_zero.mp hder).resolve_left hs4
    exact ⟨e.coeff 0, Polynomial.eq_C_of_derivative_eq_zero hde⟩

/-- Exact terminal-row residual after `B=zeta=0`, `c=C c₀`, and
`D=C d₀`.  This records the remaining scalar equation before row one
closes the chamber. -/
theorem lowerRowZeroPolynomial68_clamped_exact
    (alpha gamma epsilon eta c0 d0 : k) (A e : k[X]) :
    lowerRowZeroPolynomial68
      (integratedUPolynomial68 0 alpha 0 gamma 0 0 A 0
        ((1 / 3 : k) • A ^ 2 + C c0) (C d0)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * C c0) + e))
      (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta A 0
        ((1 / 3 : k) • A ^ 2 + C c0) (C d0)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * C c0) + e))
      (C d0)
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * C c0) + e) =
    (-d0 : k) •
      (((2 / 9 : k) * ((2 / 3 : k) * c0 + gamma)) • A +
        (4 / 9 : k) • e + C ((1 / 3 : k) * epsilon)) * derivative A := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [lowerRowZeroPolynomial68, integratedUPolynomial68,
    integratedVPolynomial68, derivative_add, derivative_sub,
    derivative_smul, derivative_mul, derivative_pow, derivative_C,
    zero_pow, zero_smul, smul_zero, zero_mul, mul_zero, add_zero,
    zero_add, sub_zero, Polynomial.C_eq_natCast, smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
    RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one]
  ring

/-- The first lower row has a universal residual independent of `e` and of
the scalar split. -/
theorem lowerRowOnePolynomial68_clamped_exact
    (alpha gamma epsilon eta c0 d0 : k) (A e : k[X]) :
    lowerRowOnePolynomial68
      (integratedTPolynomial68 0 alpha 0 gamma epsilon A 0
        ((1 / 3 : k) • A ^ 2 + C c0) (C d0)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * C c0) + e))
      (integratedUPolynomial68 0 alpha 0 gamma 0 0 A 0
        ((1 / 3 : k) • A ^ 2 + C c0) (C d0)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * C c0) + e))
      (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta A 0
        ((1 / 3 : k) • A ^ 2 + C c0) (C d0)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * C c0) + e))
      ((1 / 3 : k) • A ^ 2 + C c0) (C d0)
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * C c0) + e) =
    (((4 / 3 : k) * ((2 / 3 : k) * c0 + gamma)) • A +
        (8 / 3 : k) • e + C (2 * epsilon)) * derivative e -
      (4 / 9 * d0 ^ 2 : k) • derivative A := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [lowerRowOnePolynomial68, integratedTPolynomial68,
    integratedUPolynomial68, integratedVPolynomial68, derivative_add,
    derivative_sub, derivative_smul, derivative_mul, derivative_pow,
    derivative_C, zero_pow, zero_smul, smul_zero, zero_mul, mul_zero,
    add_zero, zero_add, sub_zero, Polynomial.C_eq_natCast, smul_eq_C_mul,
    map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
    RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 10000000 in
/-- The canonical expanded clamped chamber is empty. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_clamped_empty68
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
      8 * n ≤ 2 * g) : False := by
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
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hvanish :=
    maximalExpandedIntegratedPolynomialLowerSystem_clamped_B_zeta_zero68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hdeep)
  change l = 0 ∧ beta = 0 ∧ delta = 0 ∧ Be = 0 ∧ zeta = 0 at hvanish
  obtain ⟨hl, hbeta, hdelta, hBe, hzeta⟩ := hvanish
  obtain ⟨c0, hce⟩ := cubicDefectPolynomial68_eq_C_of_clamped
    ce n g hdeep data.hc
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using cubicEDefectPolynomial68_eq_cubicCoordinates
      Ae Ce Ee
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hl, hbeta, hdelta, hzeta, hBe, hce] at hi4e
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hl, hbeta, hdelta, hzeta, hBe, hce] at hi3e
  obtain ⟨⟨d0, hDe⟩, hregular⟩ :=
    cubicFirstIntegrals68_clamped_constant_split
      gamma epsilon i4 i3 c0 Ae De ee hi4e hi3e
  have hrowOne : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowOnePolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have hrowZero : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee =
      C terminal * (60 * (X ^ 59 : k[X])) := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_lowerRowZeroPolynomial68_of_system
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  rw [hl, hbeta, hdelta, hzeta, hBe, hCrec, hce, hErec, hce, hDe] at hrowOne
  rw [lowerRowOnePolynomial68_clamped_exact] at hrowOne
  have hrhs : C terminal * (60 * (X ^ 59 : k[X])) ≠ 0 := by
    apply mul_ne_zero
    · simpa only [C_ne_zero] using hterminal
    · exact mul_ne_zero (by norm_num) (pow_ne_zero 59 X_ne_zero)
  by_cases hd0 : d0 = 0
  · rw [hl, hbeta, hdelta, hzeta, hBe, hCrec, hce, hErec, hce, hDe,
      hd0, lowerRowZeroPolynomial68_clamped_exact, neg_zero, zero_smul]
      at hrowZero
    exact hrhs hrowZero.symm
  · let s : k := (2 / 3 : k) * c0 + gamma
    have hAdeg : Ae.natDegree = 2 * n :=
      natDegree_eq_of_le_of_coeff_ne_zero data.hA data.ha
    have hn : 0 < n := data.hn
    have hAderiv : derivative Ae ≠ 0 := by
      rw [derivative_ne_zero]
      omega
    have close_of_ee_constant (e0 : k) (hee : ee = C e0) : False := by
      have hscaled : (4 / 9 * d0 ^ 2 : k) • derivative Ae = 0 := by
        rw [hee] at hrowOne
        simpa only [derivative_C, mul_zero, zero_mul, zero_sub,
          neg_eq_zero] using hrowOne
      have hscalar : (4 / 9 * d0 ^ 2 : k) ≠ 0 :=
        mul_ne_zero (by norm_num) (pow_ne_zero 2 hd0)
      exact hAderiv ((smul_eq_zero.mp hscaled).resolve_left hscalar)
    by_cases hs : s = 0
    · have hrowZeroSing := hrowZero
      rw [hl, hbeta, hdelta, hzeta, hBe, hCrec, hce, hErec, hce,
        hDe, lowerRowZeroPolynomial68_clamped_exact] at hrowZeroSing
      dsimp only [s] at hs
      rw [hs] at hrowZeroSing
      simp only [mul_zero, zero_smul, zero_add] at hrowZeroSing
      let f : k[X] := (4 / 9 : k) • ee + C ((1 / 3 : k) * epsilon)
      have hrowZeroNormalized : (-d0 : k) • (f * derivative Ae) =
          C terminal * (60 * (X ^ 59 : k[X])) := by
        rw [← smul_mul_assoc]
        simpa only [f] using hrowZeroSing
      have hlhs : (-d0 : k) • (f * derivative Ae) ≠ 0 := by
        rw [hrowZeroNormalized]
        exact hrhs
      have hproduct : f * derivative Ae ≠ 0 := by
        intro hp
        apply hlhs
        rw [hp, smul_zero]
      have hf : f ≠ 0 := by
        intro hf0
        apply hproduct
        rw [hf0, zero_mul]
      have hrhsdeg :
          (C terminal * (60 * (X ^ 59 : k[X]))).natDegree = 59 := by
        compute_degree
        norm_num
        exact hterminal
      have hdeg := congrArg natDegree hrowZeroNormalized
      rw [natDegree_smul _ (neg_ne_zero.mpr hd0),
        natDegree_mul hf hAderiv, natDegree_derivative, hAdeg,
        hrhsdeg] at hdeg
      have hAexpand : A.natDegree * 60 = 2 * n := by
        simpa only [Ae, natDegree_expand] using hAdeg
      have hAoriginal : 0 < A.natDegree := by omega
      have hnlow : 30 ≤ n := by omega
      have hnhigh : n ≤ 30 := by omega
      have hn30 : n = 30 := by omega
      have hfdeg : f.natDegree = 0 := by omega
      obtain ⟨f0, hfC⟩ := natDegree_eq_zero.mp hfdeg
      have heesmul : (4 / 9 : k) • ee =
          C (f0 - (1 / 3 : k) * epsilon) := by
        calc
          (4 / 9 : k) • ee = f - C ((1 / 3 : k) * epsilon) := by
            simp only [f]
            ring
          _ = C f0 - C ((1 / 3 : k) * epsilon) := by rw [← hfC]
          _ = C (f0 - (1 / 3 : k) * epsilon) := by rw [C_sub]
      obtain ⟨e0, hee⟩ := eq_C_of_smul_eq_C68
        (4 / 9 : k) (f0 - (1 / 3 : k) * epsilon) ee
        (by norm_num) heesmul
      exact close_of_ee_constant e0 hee
    · obtain ⟨e0, hee⟩ := hregular (by simpa only [s] using hs)
      exact close_of_ee_constant e0 hee

end LaterDeepClampedEndgame68

#print axioms cubicDefectPolynomial68_eq_C_of_clamped
#print axioms eq_C_of_smul_eq_C68
#print axioms eq_C_of_sq_eq_C68
#print axioms cubicFirstIntegrals68_clamped_reduction
#print axioms cubicFirstIntegrals68_clamped_constant_split
#print axioms lowerRowZeroPolynomial68_clamped_exact
#print axioms lowerRowOnePolynomial68_clamped_exact
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_clamped_empty68

end Max11DegreeRoutes
