import Grok810ScaleZeroConeExhaustionSpeedReflValDegSplitPart4Scratch

/-! # SPEED: theorems of `Grok810ScaleZeroConeExhaustionSpeedReflValDegScratch`, part 5 of 8, so that no single
module retains all the reflective bridge proof terms at once.
Statements unchanged. -/

noncomputable section

open scoped Polynomial.Bivariate
open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 8000000

section ExhaustImpossible810

variable {k : Type*} [Field k] [CharZero k]

theorem mu_A6_impossible_of_mixedD0
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : A6LeadsMuMixedD0Cone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hlead := muA6Face810_natDegree hA
  have hrest :=
    degreeZeroMuNoA6_natDegree_lt_of_mixedD0 l beta gamma delta epsilon
      zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroMuPolynomial810_eq_A6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega


theorem mu_A6_impossible_of_AE03
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AE03RatioTieCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hlead := muA6Face810_natDegree hA
  have hrest :=
    degreeZeroMuNoA6_natDegree_lt_of_AE03 l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroMuPolynomial810_eq_A6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega


theorem mu_A6_impossible_of_AF07
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AF07RatioTieCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hA : A ≠ 0 := by
    intro hA0
    rcases hcone with ⟨hApos, _⟩
    simp [hA0] at hApos
  have hlead := muA6Face810_natDegree hA
  have hrest :=
    degreeZeroMuNoA6_natDegree_lt_of_AF07 l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroMuPolynomial810_eq_A6_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hApos, _⟩
  omega


set_option maxHeartbeats 16000000 in
theorem mu_xi_AC02_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AC02RatioTieCone810 A B C0 D0 E0 F0 G0)
    (hmuDeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0)
    (hxiDeg :
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hApos : 0 < A.natDegree := hcone.1
  have hCpos : 0 < C0.natDegree := hcone.2.1
  have htie : C0.natDegree = 2 * A.natDegree := hcone.2.2.1
  have hAne : A ≠ 0 := by
    intro hA0
    have : A.natDegree = 0 := by simp [hA0]
    omega
  have hCne : C0 ≠ 0 := by
    intro hC0
    simp [hC0] at hCpos
  have hr : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hs : C0.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  by_cases hmuI : muAC02Inner810 A.leadingCoeff C0.leadingCoeff = 0
  · by_cases hxiI : xiAC02Inner810 A.leadingCoeff C0.leadingCoeff = 0
    · have hs6 :=
        mu_xi_AC02_inner_s_pow A.leadingCoeff C0.leadingCoeff hmuI hxiI
      exact hs ((pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hs6)
    · have hcombdeg :=
        xiAC02Combined810_natDegree_eq_of_coeff_ne hAne hCne htie hxiI
      have hrest :=
        degreeZeroXiNoAC02_natDegree_lt l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 hcone
      rw [degreeZeroXiPolynomial810_eq_AC02_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
        hcombdeg] at hxiDeg
      omega
  · have hcombdeg :=
      muAC02Combined810_natDegree_eq_of_coeff_ne hAne hCne htie hmuI
    have hrest :=
      degreeZeroMuNoAC02_natDegree_lt l beta gamma delta epsilon zeta
        eta theta A B C0 D0 E0 F0 G0 hcone
    rw [degreeZeroMuPolynomial810_eq_AC02_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
      hcombdeg] at hmuDeg
    omega


set_option maxHeartbeats 16000000 in
theorem mu_xi_ABC0_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : ABC0RatioTieCone810 A B C0 D0 E0 F0 G0)
    (hmuDeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0)
    (hxiDeg :
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hApos : 0 < A.natDegree := hcone.1
  have hCpos : 0 < C0.natDegree := hcone.2.2.1
  have htie : C0.natDegree = 2 * A.natDegree := hcone.2.2.2.1
  have hAne : A ≠ 0 := by
    intro hA0
    have : A.natDegree = 0 := by simp [hA0]
    omega
  have hCne : C0 ≠ 0 := by
    intro hC0
    simp [hC0] at hCpos
  have hs : C0.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  by_cases hmuI : muAC02Inner810 A.leadingCoeff C0.leadingCoeff = 0
  · by_cases hxiI : xiAC02Inner810 A.leadingCoeff C0.leadingCoeff = 0
    · have hs6 :=
        mu_xi_AC02_inner_s_pow A.leadingCoeff C0.leadingCoeff hmuI hxiI
      exact hs ((pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hs6)
    · have hcombdeg :=
        xiAC02Combined810_natDegree_eq_of_coeff_ne hAne hCne htie hxiI
      have hrest :=
        degreeZeroXiNoAC02_natDegree_lt_of_ABC0 l beta gamma delta
          epsilon zeta eta theta A B C0 D0 E0 F0 G0 hcone
      rw [degreeZeroXiPolynomial810_eq_AC02_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
        hcombdeg] at hxiDeg
      omega
  · have hcombdeg :=
      muAC02Combined810_natDegree_eq_of_coeff_ne hAne hCne htie hmuI
    have hrest :=
      degreeZeroMuNoAC02_natDegree_lt_of_ABC0 l beta gamma delta epsilon
        zeta eta theta A B C0 D0 E0 F0 G0 hcone
    rw [degreeZeroMuPolynomial810_eq_AC02_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
      hcombdeg] at hmuDeg
    omega


set_option maxHeartbeats 16000000 in
theorem mu_xi_AE06_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AE06RatioTieCone810 A B C0 D0 E0 F0 G0)
    (hmuDeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0)
    (hxiDeg :
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hApos : 0 < A.natDegree := hcone.1
  have hEpos : 0 < E0.natDegree := hcone.2.1
  have htie : E0.natDegree = 3 * A.natDegree := hcone.2.2.1
  have hAne : A ≠ 0 := by
    intro hA0
    have : A.natDegree = 0 := by simp [hA0]
    omega
  have hEne : E0 ≠ 0 := by
    intro hE0
    simp [hE0] at hEpos
  have hv : E0.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  by_cases hmuI : muAE06Inner810 A.leadingCoeff E0.leadingCoeff = 0
  · by_cases hxiI : xiAE06Inner810 A.leadingCoeff E0.leadingCoeff = 0
    · have hv4 :=
        mu_xi_AE06_inner_v_pow A.leadingCoeff E0.leadingCoeff hmuI hxiI
      exact hv ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hv4)
    · have hcombdeg :=
        xiAE06Combined810_natDegree_eq_of_coeff_ne hAne hEne htie hxiI
      have hrest :=
        degreeZeroXiNoAE06_natDegree_lt l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 hcone
      rw [degreeZeroXiPolynomial810_eq_AE06_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
        hcombdeg] at hxiDeg
      omega
  · have hcombdeg :=
      muAE06Combined810_natDegree_eq_of_coeff_ne hAne hEne htie hmuI
    have hrest :=
      degreeZeroMuNoAE06_natDegree_lt l beta gamma delta epsilon zeta
        eta theta A B C0 D0 E0 F0 G0 hcone
    rw [degreeZeroMuPolynomial810_eq_AE06_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
      hcombdeg] at hmuDeg
    omega


set_option maxHeartbeats 16000000 in
theorem mu_omicron_BE02_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BE02RatioTieCone810 A B C0 D0 E0 F0 G0)
    (hmuDeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0)
    (homDeg :
      (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hBpos : 0 < B.natDegree := hcone.1
  have hEpos : 0 < E0.natDegree := hcone.2.1
  have htie : E0.natDegree = 2 * B.natDegree := hcone.2.2.1
  have hBne : B ≠ 0 := by
    intro hB0
    simp [hB0] at hBpos
  have hEne : E0 ≠ 0 := by
    intro hE0
    simp [hE0] at hEpos
  have hw : E0.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  by_cases hmuI : muBE02Inner810 B.leadingCoeff E0.leadingCoeff = 0
  · by_cases homI : omicronBE02Inner810 B.leadingCoeff E0.leadingCoeff = 0
    · have hw4 :=
        mu_omicron_BE02_inner_w_pow B.leadingCoeff E0.leadingCoeff hmuI
          homI
      exact hw ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hw4)
    · have hcombdeg :=
        omicronBE02Combined810_natDegree_eq_of_coeff_ne hBne hEne htie
          homI
      have hrest :=
        degreeZeroOmicronNoBE02_natDegree_lt l beta gamma delta epsilon
          zeta eta theta A B C0 D0 E0 F0 G0 hcone
      rw [degreeZeroOmicronPolynomial810_eq_BE02_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
        hcombdeg] at homDeg
      omega
  · have hcombdeg :=
      muBE02Combined810_natDegree_eq_of_coeff_ne hBne hEne htie hmuI
    have hrest :=
      degreeZeroMuNoBE02_natDegree_lt l beta gamma delta epsilon zeta
        eta theta A B C0 D0 E0 F0 G0 hcone
    rw [degreeZeroMuPolynomial810_eq_BE02_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
      hcombdeg] at hmuDeg
    omega


set_option maxHeartbeats 16000000 in
theorem mu_xi_AD05_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : AD05RatioTieCone810 A B C0 D0 E0 F0 G0)
    (hmuDeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0)
    (hxiDeg :
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hApos : 0 < A.natDegree := hcone.1
  have hDpos : 0 < D0.natDegree := hcone.2.1
  have htie : 5 * A.natDegree = 2 * D0.natDegree := hcone.2.2.1
  have hAne : A ≠ 0 := by
    intro hA0
    have : A.natDegree = 0 := by simp [hA0]
    omega
  have hDne : D0 ≠ 0 := by
    intro hD0
    simp [hD0] at hDpos
  have hr : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  by_cases hmuI : muAD05Inner810 A.leadingCoeff D0.leadingCoeff = 0
  · by_cases hxiI : xiAD05Inner810 A.leadingCoeff D0.leadingCoeff = 0
    · have hr7 :=
        mu_xi_AD05_inner_r_pow A.leadingCoeff D0.leadingCoeff hmuI hxiI
      exact hr ((pow_eq_zero_iff (by decide : (7 : ℕ) ≠ 0)).mp hr7)
    · have hcombdeg :=
        xiAD05Combined810_natDegree_eq_of_coeff_ne hAne hDne htie hxiI
      have hrest :=
        degreeZeroXiNoAD05_natDegree_lt l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 hcone
      rw [degreeZeroXiPolynomial810_eq_AD05_add_rest,
        natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
        hcombdeg] at hxiDeg
      omega
  · have hcombdeg :=
      muAD05Combined810_natDegree_eq_of_coeff_ne hAne hDne htie hmuI
    have hrest :=
      degreeZeroMuNoAD05_natDegree_lt l beta gamma delta epsilon zeta
        eta theta A B C0 D0 E0 F0 G0 hcone
    rw [degreeZeroMuPolynomial810_eq_AD05_add_rest,
      natDegree_add_eq_left_of_natDegree_lt (by rwa [hcombdeg]),
      hcombdeg] at hmuDeg
    omega


theorem xi_C0E0_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : C0E0RatioTieCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hC : C0 ≠ 0 := by
    intro hC0
    rcases hcone with ⟨hCpos, _⟩
    simp [hC0] at hCpos
  have hE : E0 ≠ 0 := by
    intro hE0
    rcases hcone with ⟨_, hEpos, _⟩
    simp [hE0] at hEpos
  have hc : (-(15 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      (xiC0E0Face810 C0 E0).natDegree =
        2 * C0.natDegree + E0.natDegree := by
    simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, xiC0E0Face810]
    rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hC) hE,
      natDegree_pow]
  have hrest :=
    degreeZeroXiNoC0E0_natDegree_lt l beta gamma delta epsilon zeta eta
      theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroXiPolynomial810_eq_C0E0_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hCpos, hEpos, _⟩
  omega


theorem mu_C03_impossible_of_BC03
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BC03RatioTieCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hC : C0 ≠ 0 := by
    intro hC0
    rcases hcone with ⟨_, hCpos, _⟩
    simp [hC0] at hCpos
  have hc : (-(5 / 128 : k)) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (by norm_num) (by norm_num))
  have hlead :
      ((-(5 / 128 : k)) • C0 ^ 3).natDegree = 3 * C0.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroMuNoC03_natDegree_lt_of_BC03 l beta gamma delta epsilon
      zeta eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroMuPolynomial810_eq_C03_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨_, hCpos, _⟩
  omega


theorem mu_B4_impossible_of_BD03
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : BD03RatioTieCone810 A B C0 D0 E0 F0 G0)
    (hdeg :
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0) :
    False := by
  have hB : B ≠ 0 := by
    intro hB0
    rcases hcone with ⟨hBpos, _⟩
    simp [hB0] at hBpos
  have hc : (35 / 2048 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hlead :
      ((35 / 2048 : k) • B ^ 4).natDegree = 4 * B.natDegree := by
    rw [natDegree_smul _ hc, natDegree_pow]
  have hrest :=
    degreeZeroMuNoB4_natDegree_lt_of_BD03 l beta gamma delta epsilon zeta
      eta theta A B C0 D0 E0 F0 G0 hcone
  rw [degreeZeroMuPolynomial810_eq_B4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  rcases hcone with ⟨hBpos, _⟩
  omega


end ExhaustImpossible810

section ExhaustG0Affine810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem rhoBaseG0LinearTerms810_eq_coeff_mul
    (A B C0 D0 E0 F0 G0 : k[X]) :
    rhoBaseG0LinearTerms810 A B C0 D0 E0 F0 G0 =
      rhoBaseG0LinearCoeff810 A B C0 D0 E0 F0 * G0 := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, rhoBaseG0LinearTerms810, rhoBaseG0LinearCoeff810, add_mul,
    sub_mul, neg_mul, ← smul_mul_assoc, mul_assoc]


end ExhaustG0Affine810

end Max11DegreeRoutes

end
