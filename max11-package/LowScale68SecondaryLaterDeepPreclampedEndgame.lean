import LowScale68SecondaryLaterDeepClampedEndgame

/-! # The upper preclamped later-deep `(6,8)` chamber

This file closes `7n < 2g < 8n`.  It also records the exact new vanishing
valid already for `6n < 2g`: the cubic invariant forces `B=0` before `c`
itself is clamped.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepPreclampedEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- As soon as `2g>6n`, `B` is constant and the degree-`4n` term of I3 is
only `(4/9)A²B²`; hence `B=0`. -/
theorem cubicFirstIntegralThreePolynomial68_forces_B_zero_of_sixRadius_lt_twoGap
    (gamma epsilon zeta i3 : k) (A B c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hgap : 6 * n < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hI3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma 0 epsilon zeta A B c D e = C i3) :
    B = 0 := by
  have hB0 : B.natDegree ≤ 0 := by omega
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
  have hcoeff := congrArg (fun p : k[X] ↦ p.coeff (4 * n)) hI3
  rw [cubicFirstIntegralThreePolynomial68_secondaryLoadSplit, coeff_add,
    coeff_eq_zero_of_natDegree_lt hload, add_zero] at hcoeff
  simp only [cubicFirstIntegralThreePolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero, coeff_add, coeff_sub,
    coeff_smul, hA2B2, lower _ hABD, lower _ hB2c, lower _ hD2,
    lower _ hce, smul_eq_mul] at hcoeff
  have hi : 4 * n ≠ 0 := by omega
  simp only [coeff_C, if_neg hi] at hcoeff
  have ha2 : A.coeff (2 * n) ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have hb2 : B.coeff 0 ^ 2 = 0 := by
    have hs : (4 / 9 : k) * A.coeff (2 * n) ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) ha2
    exact (mul_eq_zero.mp (by simpa only [mul_assoc] using hcoeff)).resolve_left hs
  have hb0 : B.coeff 0 = 0 := eq_zero_of_pow_eq_zero hb2
  have hBdeg : B.natDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    omega
  obtain ⟨b0, hBC⟩ := natDegree_eq_zero.mp hBdeg
  have hb : b0 = 0 := by
    have h := congrArg (fun p : k[X] ↦ p.coeff 0) hBC
    have h' : b0 = B.coeff 0 := by simpa [coeff_C] using h
    exact h'.trans hb0
  calc
    B = C b0 := hBC.symm
    _ = 0 := by rw [hb, C_0]

/-- Above `2g=7n`, after `B=0`, the degree-`2n` coefficient of I4 is
exactly `zeta*A_top`. -/
theorem cubicFirstIntegralFourPolynomial68_forces_zeta_zero_of_sevenRadius_lt_twoGap
    (gamma epsilon zeta i4 : k) (A c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hgap : 7 * n < 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hI4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A 0 c D e = C i4) :
    zeta = 0 := by
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
  simp only [coeff_C, if_neg hi] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_right ha

/-- With `B=zeta=0`, I4 makes `D*((2/3)c+gamma)` constant.  If `D` is
nonzero, this already forces `c` constant. -/
theorem cubicFirstIntegralFourPolynomial68_forces_c_constant_of_B_zeta_zero
    (gamma epsilon i4 : k) (A c D e : k[X])
    (hD : D ≠ 0)
    (hI4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon 0 A 0 c D e = C i4) :
    ∃ c0 : k, c = C c0 := by
  let s : k[X] := (2 / 3 : k) • c + C gamma
  have hDs : (4 : k) • (D * s) = C i4 := by
    rw [← hI4]
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [s, cubicFirstIntegralFourPolynomial68,
      Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
      map_neg, map_zero, RatFunc.algebraMap_C]
    simp only [map_div₀, map_ofNat, map_natCast, map_one]
    ring
  obtain ⟨r, hprod⟩ := eq_C_of_smul_eq_C68 (4 : k) i4 (D * s)
    (by norm_num) hDs
  by_cases hs : s = 0
  · have hcsmul : (2 / 3 : k) • c = C (-gamma) := by
      simp only [s] at hs
      rw [add_eq_zero_iff_eq_neg] at hs
      calc
        (2 / 3 : k) • c = -C gamma := hs
        _ = C (-gamma) := by rw [map_neg]
    exact eq_C_of_smul_eq_C68 (2 / 3 : k) (-gamma) c (by norm_num) hcsmul
  · have hdegprod : (D * s).natDegree = 0 := by rw [hprod, natDegree_C]
    rw [natDegree_mul hD hs] at hdegprod
    have hsdeg : s.natDegree = 0 := by omega
    obtain ⟨s0, hsC⟩ := natDegree_eq_zero.mp hsdeg
    have hcsmul : (2 / 3 : k) • c = C (s0 - gamma) := by
      calc
        (2 / 3 : k) • c = s - C gamma := by simp only [s]; ring
        _ = C s0 - C gamma := by rw [← hsC]
        _ = C (s0 - gamma) := by rw [C_sub]
    exact eq_C_of_smul_eq_C68 (2 / 3 : k) (s0 - gamma) c
      (by norm_num) hcsmul

set_option maxHeartbeats 12000000 in
/-- The whole open upper-preclamped chamber `7n < 2g < 8n` is empty. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_sevenToEight_empty68
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
      7 * n < 2 * g ∧ 2 * g < 8 * n) : False := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 7 * n < 2 * g ∧ 2 * g < 8 * n at hwindow
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
  have hBe :=
    cubicFirstIntegralThreePolynomial68_forces_B_zero_of_sixRadius_lt_twoGap
      gamma epsilon zeta i3 Ae Be ce De ee n g data.hn (by omega)
      data.hA data.hB data.hc data.hD data.he data.ha hi3e
  rw [hBe] at hI4 hi3e
  have hzeta :=
    cubicFirstIntegralFourPolynomial68_forces_zeta_zero_of_sevenRadius_lt_twoGap
      gamma epsilon zeta i4 Ae ce De ee n g data.hn hwindow.1
      data.hA data.hc data.hD data.he data.ha hI4
  rw [hzeta] at hI4 hi3e
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
  have hrhs : C terminal * (60 * (X ^ 59 : k[X])) ≠ 0 := by
    apply mul_ne_zero
    · simpa only [C_ne_zero] using hterminal
    · exact mul_ne_zero (by norm_num) (pow_ne_zero 59 X_ne_zero)
  by_cases hDe0 : De = 0
  · rw [hl, hbeta, hdelta, hzeta, hBe, hCrec, hErec, hDe0] at hrowZero
    simp only [integratedUPolynomial68, lowerRowZeroPolynomial68,
      zero_pow, zero_smul, smul_zero, zero_mul, mul_zero, add_zero,
      zero_add, sub_zero, C_0] at hrowZero
    exact hrhs hrowZero.symm
  · obtain ⟨c0, hce⟩ :=
      cubicFirstIntegralFourPolynomial68_forces_c_constant_of_B_zeta_zero
        gamma epsilon i4 Ae ce De ee hDe0 hI4
    obtain ⟨⟨d0, hDe⟩, hregular⟩ :=
      cubicFirstIntegrals68_clamped_constant_split
        gamma epsilon i4 i3 c0 Ae De ee (by simpa only [hce] using hI4)
        (by simpa only [hce] using hi3e)
    rw [hl, hbeta, hdelta, hzeta, hBe, hCrec, hce, hErec, hce, hDe]
      at hrowOne
    rw [lowerRowOnePolynomial68_clamped_exact] at hrowOne
    by_cases hd0 : d0 = 0
    · exact hDe0 (hDe.trans (by rw [hd0, C_0]))
    · let s : k := (2 / 3 : k) * c0 + gamma
      have hAdeg : Ae.natDegree = 2 * n :=
        natDegree_eq_of_le_of_coeff_ne_zero data.hA data.ha
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

/-- In `6n < 2g < 7n`, after `B=0`, the next I4 face is exactly `D*c`. -/
theorem cubicFirstIntegralFourPolynomial68_sixToSeven_forces_Dc_face
    (gamma epsilon zeta i4 : k) (A c D e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hwindow : 6 * n < 2 * g ∧ 2 * g < 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hI4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A 0 c D e = C i4) :
    D.coeff (5 * n - g) * c.coeff (4 * n - g) = 0 := by
  let j := 9 * n - 2 * g
  have hDc : (D * c).coeff j =
      D.coeff (5 * n - g) * c.coeff (4 * n - g) := by
    have h := coeff_mul_at_bounds68 D c (5 * n - g) (4 * n - g) hD hc
    have hj : (5 * n - g) + (4 * n - g) = j := by
      simp only [j]
      omega
    simpa only [hj] using h
  have hAlt : A.natDegree < j := by dsimp only [j]; omega
  have hDlt : D.natDegree < j := by dsimp only [j]; omega
  have hcoeff := congrArg (fun p : k[X] ↦ p.coeff j) hI4
  have hzero3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by norm_num)
  simp only [cubicFirstIntegralFourPolynomial68, hzero3, zero_smul,
    smul_zero, zero_mul, mul_zero, add_zero, zero_add, sub_zero,
    coeff_add, coeff_sub, coeff_smul, hDc,
    coeff_eq_zero_of_natDegree_lt hAlt,
    coeff_eq_zero_of_natDegree_lt hDlt, smul_eq_mul] at hcoeff
  have hj0 : j ≠ 0 := by dsimp only [j]; omega
  simp only [coeff_C, if_neg hj0] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_left (by norm_num)

/-- At the wall `2g=7n`, `D*c` ties the `zeta*A` load. -/
theorem cubicFirstIntegralFourPolynomial68_sevenRadiusWall_relation
    (gamma epsilon zeta i4 : k) (A c D e : k[X])
    (n g : ℕ) (hn : 0 < n) (hwall : 2 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g)
    (hI4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma 0 epsilon zeta A 0 c D e = C i4) :
    (8 / 3 : k) * D.coeff (5 * n - g) * c.coeff (4 * n - g) +
      zeta * A.coeff (2 * n) = 0 := by
  have hDc : (D * c).coeff (2 * n) =
      D.coeff (5 * n - g) * c.coeff (4 * n - g) := by
    have h := coeff_mul_at_bounds68 D c (5 * n - g) (4 * n - g) hD hc
    have hj : (5 * n - g) + (4 * n - g) = 2 * n := by omega
    simpa only [hj] using h
  have hDlt : D.natDegree < 2 * n := by omega
  have hcoeff := congrArg (fun p : k[X] ↦ p.coeff (2 * n)) hI4
  have hzero3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by norm_num)
  simp only [cubicFirstIntegralFourPolynomial68, hzero3, zero_smul,
    smul_zero, zero_mul, mul_zero, add_zero, zero_add, sub_zero,
    coeff_add, coeff_sub, coeff_smul, hDc,
    coeff_eq_zero_of_natDegree_lt hDlt, smul_eq_mul] at hcoeff
  have hi : 2 * n ≠ 0 := by omega
  simpa only [coeff_C, if_neg hi, mul_assoc] using hcoeff

set_option maxHeartbeats 10000000 in
/-- Exhaustive sharp output for `5n < 2g < 8n`: the upper open chamber is
empty; below it one gets the ordinary I4 face, the `D*c` face, or the exact
seven-radius tie. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_preclampedSplit68
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
      5 * n < 2 * g ∧ 2 * g < 8 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    (2 * g ≤ 6 * n ∧
      firstSecondaryFour68
        (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
        (ce.coeff (4 * n - g)) (De.coeff (5 * n - g))
        (ee.coeff (6 * n - g)) = 0) ∨
    (6 * n < 2 * g ∧ 2 * g < 7 * n ∧ Be = 0 ∧
      De.coeff (5 * n - g) * ce.coeff (4 * n - g) = 0) ∨
    (2 * g = 7 * n ∧ Be = 0 ∧
      (8 / 3 : k) * De.coeff (5 * n - g) * ce.coeff (4 * n - g) +
        zeta * Ae.coeff (2 * n) = 0) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change 5 * n < 2 * g ∧ 2 * g < 8 * n at hwindow
  change (_ ∧ _) ∨ (_ ∧ _ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _)
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
      hwindow.1 data.hA data.hB data.hc data.hD data.he data.ha hI4
  rw [hdelta] at hI4
  by_cases hle6 : 2 * g ≤ 6 * n
  · left
    exact ⟨hle6,
      cubicFirstIntegralFourPolynomial68_postDelta_forces_face
        gamma epsilon zeta i4 Ae Be ce De ee n g data.hn data.hg
        ⟨hwindow.1, hle6⟩ data.hA data.hB data.hc data.hD data.he hI4⟩
  · have hgt6 : 6 * n < 2 * g := by omega
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
      hl, hbeta, hdelta] at hi3e
    have hBe :=
      cubicFirstIntegralThreePolynomial68_forces_B_zero_of_sixRadius_lt_twoGap
        gamma epsilon zeta i3 Ae Be ce De ee n g data.hn hgt6
        data.hA data.hB data.hc data.hD data.he data.ha hi3e
    rw [hBe] at hI4
    rcases lt_trichotomy (2 * g) (7 * n) with hlt7 | hwall7 | hgt7
    · right; left
      exact ⟨hgt6, hlt7, hBe,
        cubicFirstIntegralFourPolynomial68_sixToSeven_forces_Dc_face
          gamma epsilon zeta i4 Ae ce De ee n g data.hn ⟨hgt6, hlt7⟩
          data.hA data.hc data.hD data.he hI4⟩
    · right; right
      exact ⟨hwall7, hBe,
        cubicFirstIntegralFourPolynomial68_sevenRadiusWall_relation
          gamma epsilon zeta i4 Ae ce De ee n g data.hn hwall7
          data.hA data.hc data.hD data.he hI4⟩
    · exact (maximalExpandedIntegratedPolynomialLowerSystem_sevenToEight_empty68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys (by
          simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
            (⟨hgt7, hwindow.2⟩ : 7 * n < 2 * g ∧ 2 * g < 8 * n))).elim

end LaterDeepPreclampedEndgame68

#print axioms cubicFirstIntegralThreePolynomial68_forces_B_zero_of_sixRadius_lt_twoGap
#print axioms cubicFirstIntegralFourPolynomial68_forces_zeta_zero_of_sevenRadius_lt_twoGap
#print axioms cubicFirstIntegralFourPolynomial68_forces_c_constant_of_B_zeta_zero
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_sevenToEight_empty68
#print axioms cubicFirstIntegralFourPolynomial68_sixToSeven_forces_Dc_face
#print axioms cubicFirstIntegralFourPolynomial68_sevenRadiusWall_relation
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_preclampedSplit68

end Max11DegreeRoutes
