import Grok810ScaleZeroQuarticLoadLadderScratch
import Grok810ScaleZeroQuarticChamberDefs4Scratch
import Grok810ScaleZeroQuarticSigmaLadderScratch

/-! # Two factored Residual7 chambers for `(8,10)` at scale zero

The auxiliary `N₄′ = Π − (1/2) A ο` and polynomial factorisations close
`rEFG0` and `rCEFG3`. All arguments work over a field of characteristic zero.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
/-- The weight-17 carrier `Π − (1/2) A ο`. -/
def degreeZeroN4PrimeQuartic810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G +
    (-(1 / 2) : k) •
      (A * degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G)

set_option maxHeartbeats 64000000 in
/-- Its degree bound follows from the primitive and omicron bounds. -/
theorem degreeZeroN4PrimeQuartic810_natDegree_le
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hApos : 0 < A.natDegree)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0) :
    (degreeZeroN4PrimeQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤
      A.natDegree := by
  have hb0 : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤ A.natDegree := by
    rw [hprim]
    omega
  have hb1 : ((-(1 / 2) : k) • (A * degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G)).natDegree ≤ A.natDegree := by
    refine (natDegree_smul_le810 _ _).trans ?_
    have hmul : (A * degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree ≤
        A.natDegree + (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree := natDegree_mul_le
    rw [homi, add_zero] at hmul
    omega
  exact natDegree_add_le810 hb0 hb1

set_option maxHeartbeats 64000000 in
/-- The sparse mu identity on the `EFG` support. -/
theorem factoredMuEFG810 (gamma epsilon eta : k) (A E F G : k[X]) :
    degreeZeroMuQuartic810 0 0 gamma 0 epsilon 0 eta 0 A 0 0 0 E F G =
      (3 / 4 * gamma : k) • G +
        ((5 / 32 : k) • E ^ 2 + (1 / 2 * epsilon : k) • E) := by
  simp [degreeZeroMuQuartic810]
  module

set_option maxHeartbeats 64000000 in
/-- With gamma zero, the new carrier has one load-free monomial. -/
theorem factoredN4PrimeEFG810 (epsilon eta : k) (A E F G : k[X]) :
    degreeZeroN4PrimeQuartic810 0 0 0 0 epsilon 0 eta 0 A 0 0 0 E F G =
      (-(15 / 32) : k) • (A * F * G) + (-(3 / 8) * eta : k) • (A * F) := by
  simp only [degreeZeroN4PrimeQuartic810, degreeZeroPrimitiveQuartic810,
    degreeZeroOmicronQuartic810, rhoBaseGroupQuartic810, rhoBetaGroupQuartic810,
    rhoGammaGroupQuartic810, rhoDeltaGroupQuartic810, rhoEpsilonGroupQuartic810,
    rhoZetaGroupQuartic810, rhoEtaGroupQuartic810, rhoThetaGroupQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
/-- The sparse pi identity also covers the constant-G boundary. -/
theorem factoredPiEFG810 (gamma epsilon eta : k) (A E F G : k[X]) :
    degreeZeroPiQuartic810 0 0 gamma 0 epsilon 0 eta 0 A 0 0 0 E F G =
      (-(5 / 16) : k) • (A * F ^ 2) +
        ((5 / 4 : k) • G ^ 2 - (3 / 4 * gamma : k) • E ^ 2 + (2 * eta : k) • G) := by
  simp only [degreeZeroPiQuartic810, piBaseGroupQuartic810, piBetaGroupQuartic810,
    piGammaGroupQuartic810, piDeltaGroupQuartic810, piEpsilonGroupQuartic810,
    piZetaGroupQuartic810, piEtaGroupQuartic810, piThetaGroupQuartic810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
/-- The E-constant part of the EFG chamber, including its constant-G boundary. -/
theorem quarticUnownedCell_rEFG0_impossible_of_loads_of_E_constant
    (l beta gamma delta epsilon zeta eta theta j t : k)
    (A B C D E F G : k[X])
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G) = Polynomial.C (j / t))
    (hl : l = 0) (hbe : beta = 0) (hde : delta = 0) (hze : zeta = 0) (hth : theta = 0)
    (hcone : QuarticRatioConeA810 A B C D E F G)
    (hc : QuarticChamberEFG0810 A B C D E F G)
    (hE : E.natDegree = 0) : False := by
  obtain ⟨_, hB, hC, hD, hEne, hFne, hGne, hc⟩ := hc
  subst B C D l beta delta zeta theta
  have hApos := hcone.1
  have hAne : A ≠ 0 := by intro h; simp [h] at hApos
  by_cases hG : G.natDegree = 0
  · have hrest : ((5 / 4 : k) • G ^ 2 - (3 / 4 * gamma : k) • E ^ 2 +
        (2 * eta : k) • G).natDegree < A.natDegree + 2 * F.natDegree := by
      compute_degree
      omega
    have hface : ((-(5 / 16) : k) • (A * F ^ 2)).natDegree = A.natDegree + 2 * F.natDegree := by
      rw [natDegree_smul _ (by norm_num : (-(5 / 16) : k) ≠ 0),
        natDegree_mul hAne (pow_ne_zero 2 hFne), natDegree_pow]
    rw [factoredPiEFG810, natDegree_add_eq_left_of_natDegree_lt (by omega), hface] at hpi
    omega
  · have hGpos : 0 < G.natDegree := Nat.pos_of_ne_zero hG
    have hgamma : gamma = 0 := by
      by_contra hn
      have hrest : ((5 / 32 : k) • E ^ 2 + (1 / 2 * epsilon : k) • E).natDegree < G.natDegree := by
        compute_degree
        omega
      have hface : ((3 / 4 * gamma : k) • G).natDegree = G.natDegree := by
        exact natDegree_smul _ (mul_ne_zero (by norm_num) hn)
      rw [factoredMuEFG810, natDegree_add_eq_left_of_natDegree_lt (by omega), hface] at hmu
      omega
    subst gamma
    have hprim := natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
    have hle := degreeZeroN4PrimeQuartic810_natDegree_le 0 0 0 0 epsilon 0 eta 0
      A 0 0 0 E F G hApos hprim homi
    have hrest : ((-(3 / 8) * eta : k) • (A * F)).natDegree <
        A.natDegree + F.natDegree + G.natDegree := by
      compute_degree
      omega
    have hface : ((-(15 / 32) : k) • (A * F * G)).natDegree =
        A.natDegree + F.natDegree + G.natDegree := by
      rw [natDegree_smul _ (by norm_num : (-(15 / 32) : k) ≠ 0),
        natDegree_mul (mul_ne_zero hAne hFne) hGne, natDegree_mul hAne hFne]
    rw [factoredN4PrimeEFG810, natDegree_add_eq_left_of_natDegree_lt (by omega), hface] at hle
    omega

set_option maxHeartbeats 64000000 in
/-- The first two letter bands, using only the original load ladder. -/
theorem quarticFactored_first_kappa_bands810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hA : QuarticRatioConeA810 A B C D E F G)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree = 0) :
    (l = 0 ∨ 5 * A.natDegree ≤ 4 * B.natDegree ∨
      7 * A.natDegree ≤ 4 * C.natDegree ∨ 9 * A.natDegree ≤ 4 * D.natDegree ∨
      11 * A.natDegree ≤ 4 * E.natDegree ∨ 13 * A.natDegree ≤ 4 * F.natDegree ∨
      15 * A.natDegree ≤ 4 * G.natDegree) ∧
    (beta = 0 ∨ 3 * A.natDegree ≤ 4 * B.natDegree ∨
      5 * A.natDegree ≤ 4 * C.natDegree ∨ 7 * A.natDegree ≤ 4 * D.natDegree ∨
      9 * A.natDegree ≤ 4 * E.natDegree ∨ 11 * A.natDegree ≤ 4 * F.natDegree ∨
      13 * A.natDegree ≤ 4 * G.natDegree) := by
  constructor
  · exact quarticSigma_l_band_disjunction A B C D E F G hA
      (fun htop => quarticSigma_l_eq_zero l beta gamma delta epsilon zeta eta theta
        A B C D E F G htop hkap)
  · apply quarticSigma_beta_band_disjunction A B C D E F G hA
    intro htop
    obtain ⟨ha, hab, hac, had, hae, haf, hag, hb, hc, hd, he, hf, hg⟩ :=
      quarticKappaLoadTopBeta810_bounds htop
    have hL : QuarticKappaLoadTopL810 A B C D E F G :=
      ⟨hA, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega),
        Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
    have hl := quarticSigma_l_eq_zero l beta gamma delta epsilon zeta eta theta
      A B C D E F G hL hkap
    exact quarticSigma_beta_eq_zero l beta gamma delta epsilon zeta eta theta
      A B C D E F G htop hl hkap

set_option maxHeartbeats 64000000 in
/-- On the `B=D=0`, constant-C support, the first two cost bands of kappa
are strict throughout cone A. Each remainder chunk has at most ten monomials. -/
theorem quarticFactored_BD_zero_C_constant_l_beta_zero810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeA810 A B C D E F G)
    (hB : B = 0) (hC : C.natDegree = 0) (hD : D = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
      eta theta A B C D E F G).natDegree = 0) :
    l = 0 ∧ beta = 0 := by
  obtain ⟨ha, hab, hac, had, hae, haf, hag⟩ := hcone
  subst B
  subst D
  let R₁ : k[X] := (5 / 16 : k) • (C * F) +
    (45 / 8192 * l : k) • (A ^ 3 * C) +
    (27 / 1024 * l : k) • (A ^ 2 * E) +
    (9 / 1024 * l : k) • (A * C ^ 2) +
    (9 / 64 * l : k) • (A * G) + (9 / 64 * l : k) • (C * E) +
    (35 / 32768 * beta : k) • A ^ 4 +
    (21 / 1024 * beta : k) • (A ^ 2 * C) +
    (7 / 64 * beta : k) • (A * E) - (7 / 128 * beta : k) • C ^ 2
  let R₂ : k[X] := (7 / 8 * beta : k) • G +
    (3 / 4 * gamma : k) • F + (5 / 1024 * delta : k) • A ^ 3 +
    (5 / 64 * delta : k) • (A * C) + (5 / 8 * delta : k) • E +
    (3 / 128 * zeta : k) • A ^ 2 + (3 / 8 * zeta : k) • C +
    (1 / 8 * theta : k) • A
  have hsplit : degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A 0 C 0 E F G = (63 / 262144 * l : k) • A ^ 5 + (R₁ + R₂) := by
    simp [degreeZeroKappaQuartic810, R₁, R₂] <;> module
  have hl : l = 0 := by
    by_contra hl
    have hface : ((63 / 262144 * l : k) • A ^ 5).natDegree =
        5 * A.natDegree := by
      rw [natDegree_smul _ (mul_ne_zero (by norm_num) hl), natDegree_pow]
    have hr1 : R₁.natDegree < 5 * A.natDegree := by
      dsimp [R₁]
      compute_degree
      omega
    have hr2 : R₂.natDegree < 5 * A.natDegree := by
      dsimp [R₂]
      compute_degree
      omega
    have hr := natDegree_add_lt810 hr1 hr2
    rw [hsplit, natDegree_add_eq_left_of_natDegree_lt (by rwa [hface]), hface] at hkap
    omega
  have hb : beta = 0 := by
    by_contra hb
    let S₁ : k[X] := (5 / 16 : k) • (C * F) +
      (21 / 1024 * beta : k) • (A ^ 2 * C) +
      (7 / 64 * beta : k) • (A * E) - (7 / 128 * beta : k) • C ^ 2
    have hsplitB : degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A 0 C 0 E F G = (35 / 32768 * beta : k) • A ^ 4 + (S₁ + R₂) := by
      simp [degreeZeroKappaQuartic810, S₁, R₂, hl] <;> module
    have hface : ((35 / 32768 * beta : k) • A ^ 4).natDegree =
        4 * A.natDegree := by
      rw [natDegree_smul _ (mul_ne_zero (by norm_num) hb), natDegree_pow]
    have hr1 : S₁.natDegree < 4 * A.natDegree := by
      dsimp [S₁]
      compute_degree
      omega
    have hr2 : R₂.natDegree < 4 * A.natDegree := by
      dsimp [R₂]
      compute_degree
      omega
    have hr := natDegree_add_lt810 hr1 hr2
    rw [hsplitB, natDegree_add_eq_left_of_natDegree_lt (by rwa [hface]), hface] at hkap
    omega
  exact ⟨hl, hb⟩

set_option maxHeartbeats 64000000 in
/-- The theta cost band on the `B=D=0`, constant-`C` support, proved from
its four-term `N₂` identity. -/
theorem quarticFactored_BD_zero_N2_theta_zero810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (ha : 0 < A.natDegree) (hB : B = 0) (hD : D = 0)
    (hC : C.natDegree = 0)
    (hEF : E.natDegree + F.natDegree < 2 * A.natDegree)
    (hF : F.natDegree < 2 * A.natDegree)
    (hl : l = 0) (hb : beta = 0) (hd : delta = 0) (hz : zeta = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
      eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta
      eta theta A B C D E F G).natDegree = 0) : theta = 0 := by
  subst B; subst D; subst l; subst beta; subst delta; subst zeta
  have heq : degreeZeroN2Quartic810 0 0 gamma 0 epsilon 0 eta theta
      A 0 C 0 E F G = (3 / 128 * theta : k) • A ^ 2 +
      ((5 / 16 : k) • (E * F) + (1 / 2 * epsilon : k) • F +
        (1 / 8 * theta : k) • C) := by
    simp only [degreeZeroN2Quartic810, degreeZeroNuQuartic810,
      degreeZeroKappaQuartic810, zero_mul, mul_zero, zero_smul, smul_zero,
      add_zero, zero_add, sub_zero, neg_zero]
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
      map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
      map_ofNat, map_natCast, map_one]
    ring
  by_contra ht0
  have ht : ((3 / 128 * theta : k) • A ^ 2).natDegree = 2 * A.natDegree := by
    rw [natDegree_smul _ (mul_ne_zero (by norm_num) ht0), natDegree_pow]
  have hr : ((5 / 16 : k) • (E * F) + (1 / 2 * epsilon : k) • F +
      (1 / 8 * theta : k) • C).natDegree < 2 * A.natDegree := by
    compute_degree
    omega
  have hn := degreeZeroN2Quartic810_natDegree_le 0 0 gamma 0 epsilon 0 eta theta
    A 0 C 0 E F G hnu hkap
  rw [heq, natDegree_add_eq_left_of_natDegree_lt (by omega), ht] at hn
  omega

set_option maxHeartbeats 64000000 in
/-- The five pure-`A` loads vanish when `B,D` vanish, `C,E` are constant,
and the two remaining degrees are below the degree of `A`. -/
theorem quarticFactored_constCE_loads_zero810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeA810 A B C D E F G)
    (hB : B = 0) (hD : D = 0)
    (hC : C.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree < A.natDegree) (hG : G.natDegree < A.natDegree)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
      eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta
      eta theta A B C D E F G).natDegree = 0) :
    l = 0 ∧ beta = 0 ∧ delta = 0 ∧ zeta = 0 ∧ theta = 0 := by
  have ha : 0 < A.natDegree := hcone.1
  have hBn : B.natDegree = 0 := by simp [hB]
  have hDn : D.natDegree = 0 := by simp [hD]
  have htL : QuarticKappaLoadTopL810 A B C D E F G :=
    ⟨hcone, Or.inl hB, Or.inr (by omega), Or.inl hD,
      Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
  have hl := quarticSigma_l_eq_zero l beta gamma delta epsilon zeta eta
    theta A B C D E F G htL hkap
  have htB : QuarticKappaLoadTopBeta810 A B C D E F G :=
    ⟨hcone, Or.inl hB, Or.inr (by omega), Or.inl hD,
      Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
  have hb := quarticSigma_beta_eq_zero l beta gamma delta epsilon zeta eta
    theta A B C D E F G htB hl hkap
  have htD : QuarticKappaLoadTopDelta810 A B C D E F G :=
    ⟨hcone, Or.inl hB, Or.inr (by omega), Or.inl hD,
      Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
  have hd := quarticSigma_delta_eq_zero l beta gamma delta epsilon zeta eta
    theta A B C D E F G htD hl hb hkap
  have htZ : QuarticKappaLoadTopZeta810 A B C D E F G :=
    ⟨hcone, hB, Or.inr (by omega), Or.inl hD,
      Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
  have hz := quarticSigma_zeta_eq_zero l beta gamma delta epsilon zeta eta
    theta A B C D E F G htZ hl hb hd hkap
  have ht := quarticFactored_BD_zero_N2_theta_zero810
    l beta gamma delta epsilon zeta eta theta A B C D E F G ha hB hD hC
    (by omega) (by omega) hl hb hd hz hkap hnu
  exact ⟨hl, hb, hd, hz, ht⟩

set_option maxHeartbeats 64000000 in
/-- The `E²` term of the sparse mu polynomial cannot stand above all other terms. -/
theorem factoredEFG_mu_E_top_impossible810
    (gamma delta epsilon : k) (E F G : k[X])
    (he : 0 < E.natDegree) (hg : G.natDegree < 2 * E.natDegree)
    (hd : delta = 0 ∨ F.natDegree < 2 * E.natDegree)
    (hm : ((5 / 32 : k) • E ^ 2 +
      ((3 / 4 * gamma : k) • G + (5 / 8 * delta : k) • F +
        (1 / 2 * epsilon : k) • E)).natDegree = 0) : False := by
  have ht : ((5 / 32 : k) • E ^ 2).natDegree = 2 * E.natDegree := by
    rw [natDegree_smul _ (by norm_num : (5 / 32 : k) ≠ 0), natDegree_pow]
  have hr : ((3 / 4 * gamma : k) • G + (5 / 8 * delta : k) • F +
      (1 / 2 * epsilon : k) • E).natDegree < 2 * E.natDegree := by
    rcases hd with hd | hf
    · subst delta
      simp only [mul_zero, zero_smul, add_zero]
      compute_degree
      omega
    · compute_degree
      omega
  rw [natDegree_add_eq_left_of_natDegree_lt (by omega), ht] at hm
  omega

set_option maxHeartbeats 64000000 in
/-- The `EFG0` inequalities and the four constant integrals force `E` to be constant. -/
theorem quarticFactored_EFG_E_constant810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree = 0)
    (hc : QuarticChamberEFG0810 A B C D E F G) : E.natDegree = 0 := by
  obtain ⟨hcone, hB, hC, hD, hEne, hFne, hGne, hfe, hge, hfe', hsum, hge'⟩ := hc
  have hCn : C.natDegree = 0 := by simp [hC]
  obtain ⟨hl, hb⟩ := quarticFactored_BD_zero_C_constant_l_beta_zero810
    l beta gamma delta epsilon zeta eta theta A B C D E F G hcone hB hCn hD hkap
  subst B; subst C; subst D; subst l; subst beta
  have ⟨ha, hab, hac, had, hae, haf, hag⟩ := hcone
  have hm : ((5 / 32 : k) • E ^ 2 +
      ((3 / 4 * gamma : k) • G + (5 / 8 * delta : k) • F +
        (1 / 2 * epsilon : k) • E)).natDegree = 0 := by
    have heq : degreeZeroMuQuartic810 0 0 gamma delta epsilon zeta eta theta
        A 0 0 0 E F G = (5 / 32 : k) • E ^ 2 +
        ((3 / 4 * gamma : k) • G + (5 / 8 * delta : k) • F +
          (1 / 2 * epsilon : k) • E) := by
      simp [degreeZeroMuQuartic810]
      module
    rwa [heq] at hmu
  have he2 : E.natDegree < 2 * A.natDegree := by
    by_contra hn
    exact factoredEFG_mu_E_top_impossible810 gamma delta epsilon E F G
      (by omega) (by omega) (Or.inr (by omega)) hm
  have hd : delta = 0 := by
    by_contra hd0
    have hkD : ((5 / 1024 * delta : k) • A ^ 3 +
        ((3 / 4 * gamma : k) • F + (5 / 8 * delta : k) • E +
          (3 / 128 * zeta : k) • A ^ 2 + (1 / 8 * theta : k) • A)).natDegree = 0 := by
      have heq : degreeZeroKappaQuartic810 0 0 gamma delta epsilon zeta eta theta
          A 0 0 0 E F G = (5 / 1024 * delta : k) • A ^ 3 +
          ((3 / 4 * gamma : k) • F + (5 / 8 * delta : k) • E +
            (3 / 128 * zeta : k) • A ^ 2 + (1 / 8 * theta : k) • A) := by
        simp [degreeZeroKappaQuartic810]
        module
      rwa [heq] at hkap
    have ht : ((5 / 1024 * delta : k) • A ^ 3).natDegree = 3 * A.natDegree := by
      rw [natDegree_smul _ (mul_ne_zero (by norm_num) hd0), natDegree_pow]
    have hr : ((3 / 4 * gamma : k) • F + (5 / 8 * delta : k) • E +
        (3 / 128 * zeta : k) • A ^ 2 + (1 / 8 * theta : k) • A).natDegree <
        3 * A.natDegree := by
      compute_degree
      omega
    rw [natDegree_add_eq_left_of_natDegree_lt (by omega), ht] at hkD
    omega
  subst delta
  have he1 : E.natDegree < A.natDegree := by
    by_contra hn
    exact factoredEFG_mu_E_top_impossible810 gamma 0 epsilon E F G
      (by omega) (by omega) (Or.inl rfl) hm
  have hz : zeta = 0 := by
    by_contra hz0
    have hkZ : ((3 / 128 * zeta : k) • A ^ 2 +
        ((3 / 4 * gamma : k) • F + (1 / 8 * theta : k) • A)).natDegree = 0 := by
      have heq : degreeZeroKappaQuartic810 0 0 gamma 0 epsilon zeta eta theta
          A 0 0 0 E F G = (3 / 128 * zeta : k) • A ^ 2 +
          ((3 / 4 * gamma : k) • F + (1 / 8 * theta : k) • A) := by
        simp [degreeZeroKappaQuartic810]
        module
      rwa [heq] at hkap
    have ht : ((3 / 128 * zeta : k) • A ^ 2).natDegree = 2 * A.natDegree := by
      rw [natDegree_smul _ (mul_ne_zero (by norm_num) hz0), natDegree_pow]
    have hr : ((3 / 4 * gamma : k) • F + (1 / 8 * theta : k) • A).natDegree <
        2 * A.natDegree := by
      compute_degree
      omega
    rw [natDegree_add_eq_left_of_natDegree_lt (by omega), ht] at hkZ
    omega
  subst zeta
  by_contra he0
  have he : 0 < E.natDegree := by omega
  have hgam : gamma ≠ 0 := by
    intro hg0
    subst gamma
    have ht : ((5 / 32 : k) • E ^ 2).natDegree = 2 * E.natDegree := by
      rw [natDegree_smul _ (by norm_num : (5 / 32 : k) ≠ 0), natDegree_pow]
    simp only [mul_zero, zero_smul, zero_add, add_zero] at hm
    have hr : ((1 / 2 * epsilon : k) • E).natDegree < 2 * E.natDegree := by
      compute_degree
      omega
    rw [natDegree_add_eq_left_of_natDegree_lt (by omega), ht] at hm
    omega
  have hgc : (3 / 4 * gamma : k) ≠ 0 := mul_ne_zero (by norm_num) hgam
  have hgeq : G.natDegree = 2 * E.natDegree := by
    apply Nat.le_antisymm
    · by_contra hn
      have hg : 2 * E.natDegree < G.natDegree := by omega
      have hm' : ((3 / 4 * gamma : k) • G +
          ((5 / 32 : k) • E ^ 2 + (1 / 2 * epsilon : k) • E)).natDegree = 0 := by
        have heq : (3 / 4 * gamma : k) • G +
            ((5 / 32 : k) • E ^ 2 + (1 / 2 * epsilon : k) • E) =
            (5 / 32 : k) • E ^ 2 +
              ((3 / 4 * gamma : k) • G + (5 / 8 * (0 : k) : k) • F +
                (1 / 2 * epsilon : k) • E) := by
          simp only [mul_zero, zero_smul, add_zero]
          module
        rw [heq]
        exact hm
      have ht : ((3 / 4 * gamma : k) • G).natDegree = G.natDegree :=
        natDegree_smul _ hgc
      have hr : ((5 / 32 : k) • E ^ 2 +
          (1 / 2 * epsilon : k) • E).natDegree < G.natDegree := by
        compute_degree
        omega
      rw [natDegree_add_eq_left_of_natDegree_lt (by omega), ht] at hm'
      omega
    · by_contra hn
      exact factoredEFG_mu_E_top_impossible810 gamma 0 epsilon E F G
        he (by omega) (Or.inl rfl) hm
  have hk : ((3 / 4 * gamma : k) • F + (1 / 8 * theta : k) • A).natDegree = 0 := by
    have heq : degreeZeroKappaQuartic810 0 0 gamma 0 epsilon 0 eta theta
        A 0 0 0 E F G = (3 / 4 * gamma : k) • F + (1 / 8 * theta : k) • A := by
      simp [degreeZeroKappaQuartic810]
    rwa [heq] at hkap
  have hfa : F.natDegree ≤ A.natDegree := by
    by_contra hn
    have ht : ((3 / 4 * gamma : k) • F).natDegree = F.natDegree :=
      natDegree_smul _ hgc
    have hr : ((1 / 8 * theta : k) • A).natDegree < F.natDegree := by
      compute_degree
      omega
    rw [natDegree_add_eq_left_of_natDegree_lt (by omega), ht] at hk
    omega
  have htheta := quarticFactored_BD_zero_N2_theta_zero810
    0 0 gamma 0 epsilon 0 eta theta A 0 0 0 E F G ha rfl rfl (by simp)
    (by omega) (by omega) rfl rfl rfl rfl hkap hnu
  subst theta
  have hf0 : F.natDegree = 0 := by
    simpa only [mul_zero, zero_smul, add_zero, natDegree_smul _ hgc] using hk
  have hx : ((5 / 16 : k) • (E * G) +
      ((5 / 32 : k) • F ^ 2 + (1 / 2 * epsilon : k) • G +
        (1 / 4 * eta : k) • E)).natDegree = 0 := by
    have heq : degreeZeroXiQuartic810 0 0 gamma 0 epsilon 0 eta 0
        A 0 0 0 E F G = (5 / 16 : k) • (E * G) +
        ((5 / 32 : k) • F ^ 2 + (1 / 2 * epsilon : k) • G +
          (1 / 4 * eta : k) • E) := by
      simp [degreeZeroXiQuartic810]
      module
    rwa [heq] at hxi
  have ht : ((5 / 16 : k) • (E * G)).natDegree = E.natDegree + G.natDegree := by
    rw [natDegree_smul _ (by norm_num : (5 / 16 : k) ≠ 0), natDegree_mul hEne hGne]
  have hr : ((5 / 32 : k) • F ^ 2 + (1 / 2 * epsilon : k) • G +
      (1 / 4 * eta : k) • E).natDegree < E.natDegree + G.natDegree := by
    compute_degree
    omega
  rw [natDegree_add_eq_left_of_natDegree_lt (by omega), ht] at hx
  omega

set_option maxHeartbeats 64000000 in
/-- The exact Residual7 `rEFG0` constructor is impossible. -/
theorem quarticUnownedCell_rEFG0_impossible {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hjdiv : j / t ≠ 0)
    (hder : derivative (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G) = Polynomial.C (j / t))
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G).natDegree = 0)
    (hcone : QuarticRatioConeA810 A B C D E F G)
    (hc : QuarticChamberEFG0810 A B C D E F G) : False := by
  have hE := quarticFactored_EFG_E_constant810
    l beta gamma delta epsilon zeta eta theta A B C D E F G hxi hmu hkap hnu hc
  have hcell := hc
  obtain ⟨_, hB, hC, hD, hEne, hFne, hGne, hfe, hge, hfe', hsum, hge'⟩ := hc
  have hCn : C.natDegree = 0 := by simp [hC]
  obtain ⟨hl, hb, hd, hz, ht⟩ := quarticFactored_constCE_loads_zero810
    l beta gamma delta epsilon zeta eta theta A B C D E F G
    hcone hB hD hCn hE (by omega) (by omega) hkap hnu
  exact quarticUnownedCell_rEFG0_impossible_of_loads_of_E_constant
    l beta gamma delta epsilon zeta eta theta j t A B C D E F G
    hxi hmu homi hkap hnu hpi hjdiv hder hl hb hd hz ht hcone hcell hE

set_option maxHeartbeats 64000000 in
/-- The gamma wall is forced throughout the Residual7 CEFG3 chamber. -/
theorem quarticUnownedCEFG3_C_natDegree_eq_zero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG3810 A B C D E F G)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree = 0) : C.natDegree = 0 := by
  obtain ⟨hA, hBz, hCne, hDz, hEne, hFne, hGne,
    hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8⟩ := hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hBn : B.natDegree = 0 := by simp [hBz]
  have hDn : D.natDegree = 0 := by simp [hDz]
  by_contra hCzero
  have hCpos : 0 < C.natDegree := Nat.pos_of_ne_zero hCzero
  obtain ⟨hbl, hbbeta⟩ :=
    quarticFactored_first_kappa_bands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  have hbl' : l = 0 ∨
      (2 * A.natDegree + F.natDegree < C.natDegree + G.natDegree ∧
        C.natDegree + F.natDegree < C.natDegree + G.natDegree) := by
    rcases hbl with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by omega)
    · exact Or.inr ⟨by omega, by omega⟩
    · exact absurd h (by omega)
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have hbbeta' : beta = 0 ∨
      A.natDegree + F.natDegree < C.natDegree + G.natDegree := by
    rcases hbbeta with h | h | h | h | h | h | h
    · exact Or.inl h
    · exact absurd h (by omega)
    · exact Or.inr (by omega)
    · exact absurd h (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  let R : k[X] :=
    -(5 / 128 : k) • C ^ 3 + (5 / 32 : k) • E ^ 2
      - (9 / 1024 * l : k) • (A ^ 2 * F)
      + (9 / 64 * l : k) • (C * F)
      - (7 / 64 * beta : k) • (A * F)
      - (3 / 32 * gamma : k) • C ^ 2
      + (3 / 4 * gamma : k) • G
      + (5 / 8 * delta : k) • F
      + (1 / 2 * epsilon : k) • E
      + (1 / 4 * eta : k) • C
  have hsplit : degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G = (5 / 16 : k) • (C * G) + R := by
    simp [degreeZeroMuQuartic810, R, hBz, hDz]
    module
  have hrest : R.natDegree < C.natDegree + G.natDegree := by
    rcases hbl' with rfl | ⟨hl1, hl2⟩ <;>
      rcases hbbeta' with rfl | hb1
    all_goals
      simp only [R, mul_zero, zero_smul, sub_zero, add_zero]
      compute_degree
      omega
  have hlead : ((5 / 16 : k) • (C * G)).natDegree =
      C.natDegree + G.natDegree := by
    rw [natDegree_smul _ (by norm_num : (5 / 16 : k) ≠ 0),
      natDegree_mul hCne hGne]
  rw [hsplit, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hmu
  omega

set_option maxHeartbeats 64000000 in
/-- After the `C` wall is reached, the whole `CEFG3` chamber kills the
remaining three pure-`A` loads by `mu` and the polynomial identity for `kappa`. -/
theorem quarticFactored_CEFG_remaining_loads_zero810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberCEFG3810 A B C D E F G)
    (hCdeg : C.natDegree = 0) (hl : l = 0) (hb : beta = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree = 0) :
    delta = 0 ∧ zeta = 0 ∧ theta = 0 := by
  rcases hch with ⟨hcone, hB, hCne, hD, hEne, hFne, hGne, heq,
    hECF, hEAC, hEG, hFC, hGC, hGCF, hCCF, hCEF⟩
  have ha : 0 < A.natDegree := hcone.1
  have hg : 0 < G.natDegree := by omega
  have heg : 2 * E.natDegree < G.natDegree := by omega
  have hfg : F.natDegree < G.natDegree := by omega
  have hea : E.natDegree < A.natDegree := by omega
  subst B
  subst D
  subst l
  subst beta
  let Q : k[X] := Polynomial.C 5 * C + Polynomial.C (12 * gamma)
  let R : k[X] := (-(5 / 128 : k)) • C ^ 3 -
    (3 / 32 * gamma : k) • C ^ 2 + (5 / 32 : k) • E ^ 2 +
    (1 / 2 * epsilon : k) • E + (5 / 8 * delta : k) • F +
    (1 / 4 * eta : k) • C
  have hmuFac : degreeZeroMuQuartic810 0 0 gamma delta epsilon zeta eta theta
      A 0 C 0 E F G = (1 / 16 : k) • (Q * G) + R := by
    simp only [degreeZeroMuQuartic810, Q, R]
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
      map_neg, map_zero, RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
    ring
  have hQdeg : Q.natDegree = 0 := by
    apply natDegree_eq_zero_of_le_zero
    dsimp [Q]
    compute_degree
    omega
  have hQzero : Q = 0 := by
    by_contra hQ
    have hlead : ((1 / 16 : k) • (Q * G)).natDegree = G.natDegree := by
      rw [natDegree_smul _ (by norm_num : (1 / 16 : k) ≠ 0),
        natDegree_mul hQ hGne, hQdeg, zero_add]
    have hrest : R.natDegree < G.natDegree := by
      dsimp [R]
      compute_degree
      omega
    rw [hmuFac, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hmu
    omega
  have hkapReduced : degreeZeroKappaQuartic810 0 0 gamma delta epsilon zeta eta theta
      A 0 C 0 E F G = (5 / 1024 * delta : k) • A ^ 3 +
      ((5 / 64 * delta : k) • (A * C) + (5 / 8 * delta : k) • E +
        (3 / 128 * zeta : k) • A ^ 2 + (3 / 8 * zeta : k) • C +
        (1 / 8 * theta : k) • A) := by
    have hfull : degreeZeroKappaQuartic810 0 0 gamma delta epsilon zeta eta theta
        A 0 C 0 E F G = (1 / 16 : k) • (F * Q) +
        ((5 / 1024 * delta : k) • A ^ 3 +
          ((5 / 64 * delta : k) • (A * C) + (5 / 8 * delta : k) • E +
            (3 / 128 * zeta : k) • A ^ 2 + (3 / 8 * zeta : k) • C +
            (1 / 8 * theta : k) • A)) := by
      simp only [degreeZeroKappaQuartic810, Q]
      apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
      simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
        map_neg, map_zero, RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
      ring
    rw [hfull, hQzero]
    simp
  have hd : delta = 0 := by
    by_contra hd
    have hc : (5 / 1024 * delta : k) ≠ 0 := mul_ne_zero (by norm_num) hd
    have hlead : ((5 / 1024 * delta : k) • A ^ 3).natDegree = 3 * A.natDegree := by
      rw [natDegree_smul _ hc, natDegree_pow]
    have hrest : ((5 / 64 * delta : k) • (A * C) +
        (5 / 8 * delta : k) • E + (3 / 128 * zeta : k) • A ^ 2 +
        (3 / 8 * zeta : k) • C + (1 / 8 * theta : k) • A).natDegree <
        3 * A.natDegree := by
      compute_degree
      omega
    rw [hkapReduced, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hkap
    omega
  have hkapZ : degreeZeroKappaQuartic810 0 0 gamma delta epsilon zeta eta theta
      A 0 C 0 E F G = (3 / 128 * zeta : k) • A ^ 2 +
        ((3 / 8 * zeta : k) • C + (1 / 8 * theta : k) • A) := by
    rw [hkapReduced, hd]
    simp only [mul_zero, zero_smul, zero_add]
    abel
  have hz : zeta = 0 := by
    by_contra hz
    have hc : (3 / 128 * zeta : k) ≠ 0 := mul_ne_zero (by norm_num) hz
    have hlead : ((3 / 128 * zeta : k) • A ^ 2).natDegree = 2 * A.natDegree := by
      rw [natDegree_smul _ hc, natDegree_pow]
    have hrest : ((3 / 8 * zeta : k) • C + (1 / 8 * theta : k) • A).natDegree <
        2 * A.natDegree := by
      compute_degree
      omega
    rw [hkapZ, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hkap
    omega
  have ht : theta = 0 := by
    by_contra ht
    have hc : (1 / 8 * theta : k) ≠ 0 := mul_ne_zero (by norm_num) ht
    rw [hkapZ, hz] at hkap
    simp only [mul_zero, zero_smul, zero_add] at hkap
    rw [natDegree_smul _ hc] at hkap
    omega
  exact ⟨hd, hz, ht⟩

set_option maxHeartbeats 64000000 in
/-- A nonzero scalar multiple plus a constant is constant only when the polynomial is. -/
private theorem quarticFactored_constant_of_affine810
    (P : k[X]) (r s : k) (hr : r ≠ 0)
    (h : (Polynomial.C r * P + Polynomial.C s).natDegree = 0) :
    P.natDegree = 0 := by
  by_contra hp
  have hp0 : 0 < P.natDegree := by omega
  have hh : (Polynomial.C s).natDegree < (Polynomial.C r * P).natDegree := by
    rw [natDegree_C_mul hr, natDegree_C]
    exact hp0
  rw [natDegree_add_eq_left_of_natDegree_lt hh, natDegree_C_mul hr] at h
  exact hp h

set_option maxHeartbeats 64000000 in
/-- The three factored odd integrals close the whole `CEFG3` chamber once its
five pure-`A` loads have vanished. -/
theorem quarticUnownedCell_rCEFG3_impossible_of_loads
    (l beta gamma delta epsilon zeta eta theta j t : k)
    (A B C D E F G : k[X])
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G) = Polynomial.C (j / t))
    (hl : l = 0) (hbeta : beta = 0) (hdelta : delta = 0)
    (hzeta : zeta = 0) (htheta : theta = 0)
    (hcone : QuarticRatioConeA810 A B C D E F G)
    (hcell : QuarticChamberCEFG3810 A B C D E F G) : False := by
  rcases hcell with ⟨_, hB, hCne, hD, hEne, hFne, hGne, heq,
    hECF, hEAC, hEG, hFC, hGC, hGCF, hCCF, hCEF⟩
  have hApos : 0 < A.natDegree := hcone.1
  have hAne : A ≠ 0 := by
    intro hA
    simp [hA] at hApos
  subst B
  subst D
  subst l
  subst beta
  subst delta
  subst zeta
  subst theta
  let Q : k[X] := Polynomial.C 5 * C + Polynomial.C (12 * gamma)
  let P : k[X] := Polynomial.C 5 * E + Polynomial.C (8 * epsilon)
  have hkapFac : degreeZeroKappaQuartic810 0 0 gamma 0 epsilon 0 eta 0
      A 0 C 0 E F G = Polynomial.C (1 / 16 : k) * (F * Q) := by
    simp only [degreeZeroKappaQuartic810, Q]
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
      map_neg, map_zero, RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
    ring
  have hnuFac : degreeZeroNuQuartic810 0 0 gamma 0 epsilon 0 eta 0
      A 0 C 0 E F G =
      Polynomial.C (-(1 / 128 : k)) * (F * (A * Q - Polynomial.C 8 * P)) := by
    simp only [degreeZeroNuQuartic810, Q, P]
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
      map_neg, map_zero, RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
    ring
  have hQdeg : Q.natDegree = 0 := by
    by_cases hQ : Q = 0
    · simp [hQ]
    · rw [hkapFac, natDegree_C_mul (by norm_num : (1 / 16 : k) ≠ 0),
        natDegree_mul hFne hQ] at hkap
      omega
  have hCdeg : C.natDegree = 0 :=
    quarticFactored_constant_of_affine810 C 5 (12 * gamma) (by norm_num) hQdeg
  have hElt : E.natDegree < A.natDegree := by omega
  have hQzero : Q = 0 := by
    by_contra hQ
    have hlead : (A * Q).natDegree = A.natDegree := by
      rw [natDegree_mul hAne hQ, hQdeg, add_zero]
    have hrest : (Polynomial.C 8 * P).natDegree < A.natDegree := by
      dsimp [P]
      compute_degree
      omega
    have hinner : (A * Q - Polynomial.C 8 * P).natDegree = A.natDegree := by
      rw [natDegree_sub_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    have hinnerne : A * Q - Polynomial.C 8 * P ≠ 0 := by
      intro hzero
      simp [hzero] at hinner
      omega
    rw [hnuFac, natDegree_C_mul (by norm_num : (-(1 / 128 : k)) ≠ 0),
      natDegree_mul hFne hinnerne, hinner] at hnu
    omega
  have hnuReduced : degreeZeroNuQuartic810 0 0 gamma 0 epsilon 0 eta 0
      A 0 C 0 E F G = Polynomial.C (1 / 16 : k) * (F * P) := by
    rw [hnuFac, hQzero]
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [map_add, map_sub, map_mul, map_neg, map_zero, RatFunc.algebraMap_C,
      map_div₀, map_ofNat, map_natCast, map_one]
    ring
  have hPdeg : P.natDegree = 0 := by
    by_cases hP : P = 0
    · simp [hP]
    · rw [hnuReduced, natDegree_C_mul (by norm_num : (1 / 16 : k) ≠ 0),
        natDegree_mul hFne hP] at hnu
      omega
  have hEdeg : E.natDegree = 0 :=
    quarticFactored_constant_of_affine810 E 5 (8 * epsilon) (by norm_num) hPdeg
  have homiReduced : degreeZeroOmicronQuartic810 0 0 gamma 0 epsilon 0 eta 0
      A 0 C 0 E F G = Polynomial.C (-(1 / 128 : k)) *
        (F * (A * P + Polynomial.C 5 * C ^ 2 -
          Polynomial.C 40 * G - Polynomial.C (32 * eta))) := by
    have hfull : degreeZeroOmicronQuartic810 0 0 gamma 0 epsilon 0 eta 0
        A 0 C 0 E F G = Polynomial.C (-(1 / 2048 : k)) *
        (F * (A ^ 2 * Q + Polynomial.C 16 * A * P +
          Polynomial.C 16 * C * Q + Polynomial.C 80 * C ^ 2 -
          Polynomial.C 640 * G - Polynomial.C (512 * eta))) := by
      simp only [degreeZeroOmicronQuartic810, Q, P]
      apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
      simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
        map_neg, map_zero, RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
      ring
    rw [hfull, hQzero]
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C,
      map_div₀, map_ofNat, map_natCast, map_one]
    ring
  have hPzero : P = 0 := by
    by_contra hP
    have hFdeg : F.natDegree = 0 := by
      rw [hnuReduced, natDegree_C_mul (by norm_num : (1 / 16 : k) ≠ 0),
        natDegree_mul hFne hP, hPdeg] at hnu
      omega
    have hGlt : G.natDegree < A.natDegree := by omega
    have hlead : (A * P).natDegree = A.natDegree := by
      rw [natDegree_mul hAne hP, hPdeg, add_zero]
    have hrest : (Polynomial.C 5 * C ^ 2 - Polynomial.C 40 * G -
        Polynomial.C (32 * eta)).natDegree < A.natDegree := by
      compute_degree
      omega
    have heqinner : A * P + Polynomial.C 5 * C ^ 2 -
        Polynomial.C 40 * G - Polynomial.C (32 * eta) =
        A * P + (Polynomial.C 5 * C ^ 2 - Polynomial.C 40 * G -
          Polynomial.C (32 * eta)) := by ring
    have hinner : (A * P + Polynomial.C 5 * C ^ 2 -
        Polynomial.C 40 * G - Polynomial.C (32 * eta)).natDegree = A.natDegree := by
      rw [heqinner, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    have hinnerne : A * P + Polynomial.C 5 * C ^ 2 -
        Polynomial.C 40 * G - Polynomial.C (32 * eta) ≠ 0 := by
      intro hz
      rw [hz, natDegree_zero] at hinner
      omega
    rw [homiReduced, natDegree_C_mul (by norm_num : (-(1 / 128 : k)) ≠ 0),
      natDegree_mul hFne hinnerne, hinner] at homi
    omega
  have hGpos : 0 < G.natDegree := by omega
  have heqinner : A * P + Polynomial.C 5 * C ^ 2 -
      Polynomial.C 40 * G - Polynomial.C (32 * eta) =
      Polynomial.C (-40) * G +
        (Polynomial.C 5 * C ^ 2 - Polynomial.C (32 * eta)) := by
    rw [hPzero]
    simp only [map_neg]
    ring
  have hlead : (Polynomial.C (-40 : k) * G).natDegree = G.natDegree := by
    rw [natDegree_C_mul (by norm_num : (-40 : k) ≠ 0)]
  have hrest : (Polynomial.C 5 * C ^ 2 - Polynomial.C (32 * eta)).natDegree <
      G.natDegree := by
    compute_degree
    omega
  have hinner : (A * P + Polynomial.C 5 * C ^ 2 -
      Polynomial.C 40 * G - Polynomial.C (32 * eta)).natDegree = G.natDegree := by
    rw [heqinner, natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
  have hinnerne : A * P + Polynomial.C 5 * C ^ 2 -
      Polynomial.C 40 * G - Polynomial.C (32 * eta) ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hinner
    omega
  rw [homiReduced, natDegree_C_mul (by norm_num : (-(1 / 128 : k)) ≠ 0),
    natDegree_mul hFne hinnerne, hinner] at homi
  omega

set_option maxHeartbeats 64000000 in
/-- The exact Residual7 `rCEFG3` constructor is impossible. -/
theorem quarticUnownedCell_rCEFG3_impossible {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hjdiv : j / t ≠ 0)
    (hder : derivative (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G) = Polynomial.C (j / t))
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree = 0)
    (hcone : QuarticRatioConeA810 A B C D E F G)
    (hcell : QuarticChamberCEFG3810 A B C D E F G) : False := by
  have hCdeg := quarticUnownedCEFG3_C_natDegree_eq_zero
    l beta gamma delta epsilon zeta eta theta A B C D E F G hcell hkap hmu
  obtain ⟨hl, hb⟩ := quarticFactored_BD_zero_C_constant_l_beta_zero810
    l beta gamma delta epsilon zeta eta theta A B C D E F G hcone
    hcell.2.1 hCdeg hcell.2.2.2.1 hkap
  obtain ⟨hd, hz, ht⟩ := quarticFactored_CEFG_remaining_loads_zero810
    l beta gamma delta epsilon zeta eta theta A B C D E F G hcell hCdeg hl hb hkap hmu
  exact quarticUnownedCell_rCEFG3_impossible_of_loads
    l beta gamma delta epsilon zeta eta theta j t A B C D E F G
    hxi hmu homi hkap hnu hpi hjdiv hder hl hb hd hz ht hcone hcell

end Max11DegreeRoutes

#print axioms Max11DegreeRoutes.quarticUnownedCell_rEFG0_impossible
#print axioms Max11DegreeRoutes.quarticUnownedCell_rCEFG3_impossible
