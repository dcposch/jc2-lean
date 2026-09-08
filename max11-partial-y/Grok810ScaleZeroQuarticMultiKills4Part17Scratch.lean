import Grok810ScaleZeroQuarticMultiKills4Part16Scratch

/-! # Part 17 of `Grok810ScaleZeroQuarticMultiKills4Scratch`.

One declaration split out of `Grok810ScaleZeroQuarticMultiKills4Scratch`; statements are byte-identical.
-/

open scoped Polynomial.Bivariate

noncomputable section

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

section QuarticKills810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuartic810_eq_ABDFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      piQuarticFaceABDFG810 A B C D E F G +
        degreeZeroPiQuarticNoABDFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [degreeZeroPiQuartic810, piBaseGroupQuartic810,
    piBetaGroupQuartic810, piGammaGroupQuartic810, piDeltaGroupQuartic810,
    piEpsilonGroupQuartic810, piZetaGroupQuartic810, piEtaGroupQuartic810,
    piThetaGroupQuartic810, piQuarticFaceABDFG810, degreeZeroPiQuarticNoABDFG810]
  all_goals module

set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroPiQuarticNoABDFG810` (87 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroPiQuarticNoABDFG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroPiQuarticNoABDFG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (-(45 / 512) : k), (-(35 / 256) : k), (5 / 32 : k),
      (5 / 16 : k), (5 / 32 : k), (45 / 64 : k),
      (45 / 64 : k), (15 / 256 : k), (-(15 / 16) : k),
      (-(5 / 16) : k), (-(15 / 16) : k), (-(5 / 8) : k),
      (-(5 / 8) : k), (45 / 131072 * l : k), (-(3 / 32768 * l) : k),
      (-(45 / 32768 * l) : k), (9 / 4096 * l : k), (9 / 4096 * l : k),
      (-(27 / 4096 * l) : k), (9 / 4096 * l : k), (-(189 / 4096 * l) : k),
      (-(63 / 4096 * l) : k), (-(27 / 1024 * l) : k), (9 / 512 * l : k),
      (63 / 1024 * l : k), (9 / 128 * l : k), (27 / 256 * l : k),
      (9 / 256 * l : k), (63 / 512 * l : k), (189 / 512 * l : k),
      (63 / 512 * l : k), (-(9 / 64 * l) : k), (-(9 / 32 * l) : k),
      (-(27 / 64 * l) : k), (-(9 / 32 * l) : k), (-(27 / 128 * l) : k),
      (-(9 / 16 * l) : k), (-(3 / 32 * l) : k), (9 / 8 * l : k),
      (7 / 4096 * beta : k), (7 / 4096 * beta : k), (-(7 / 1024 * beta) : k),
      (7 / 512 * beta : k), (7 / 512 * beta : k), (-(21 / 256 * beta) : k),
      (-(7 / 256 * beta) : k), (-(63 / 512 * beta) : k), (-(7 / 64 * beta) : k),
      (7 / 32 * beta : k), (21 / 128 * beta : k), (7 / 16 * beta : k),
      (7 / 32 * beta : k), (7 / 32 * beta : k), (-(7 / 8 * beta) : k),
      (-(3 / 32 * gamma) : k), (-(15 / 256 * gamma) : k), (3 / 16 * gamma : k),
      (3 / 8 * gamma : k), (3 / 4 * gamma : k), (1 / 8 * gamma : k),
      (-(3 / 4 * gamma) : k), (-(3 / 4 * gamma) : k), (5 / 512 * delta : k),
      (-(15 / 256 * delta) : k), (-(5 / 128 * delta) : k), (5 / 32 * delta : k),
      (5 / 32 * delta : k), (15 / 32 * delta : k), (15 / 32 * delta : k),
      (-(5 / 8 * delta) : k), (-(5 / 4 * delta) : k), (1 / 4 * epsilon : k),
      (1 / 2 * epsilon : k), (-(1 / 2 * epsilon) : k), (-(1 * epsilon) : k),
      (-(1 / 2 * epsilon) : k), (3 / 32 * zeta : k), (5 / 32 * zeta : k),
      (-(3 / 8 * zeta) : k), (-(3 / 4 * zeta) : k), (-(3 / 4 * zeta) : k),
      (1 / 16 * eta : k), (-(1 / 2 * eta) : k), (-(1 / 4 * eta) : k),
      (2 * eta : k), (-(1 / 4 * theta) : k), (1 * theta : k)]
      [
      [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0], [1, 1, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0],
      [1, 0, 1, 2, 0, 0, 0], [0, 2, 1, 0, 1, 0, 0], [0, 1, 2, 1, 0, 0, 0], [0, 0, 4, 0, 0, 0, 0],
      [0, 1, 0, 0, 1, 1, 0], [0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0], [0, 0, 1, 0, 2, 0, 0],
      [0, 0, 0, 2, 1, 0, 0], [4, 1, 1, 0, 0, 0, 0], [3, 3, 0, 0, 0, 0, 0], [4, 0, 0, 0, 0, 1, 0],
      [3, 1, 0, 0, 1, 0, 0], [3, 0, 1, 1, 0, 0, 0], [2, 2, 0, 1, 0, 0, 0], [2, 1, 2, 0, 0, 0, 0],
      [1, 3, 1, 0, 0, 0, 0], [0, 5, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 1, 0], [2, 0, 0, 1, 1, 0, 0],
      [1, 2, 0, 0, 0, 1, 0], [1, 1, 1, 0, 1, 0, 0], [1, 1, 0, 2, 0, 0, 0], [1, 0, 2, 1, 0, 0, 0],
      [0, 3, 0, 0, 1, 0, 0], [0, 2, 1, 1, 0, 0, 0], [0, 1, 3, 0, 0, 0, 0], [1, 0, 0, 0, 1, 1, 0],
      [0, 1, 1, 0, 0, 0, 1], [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 2, 0, 0], [0, 0, 2, 0, 0, 1, 0],
      [0, 0, 1, 1, 1, 0, 0], [0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1], [3, 1, 1, 0, 0, 0, 0],
      [2, 3, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0], [2, 1, 0, 0, 1, 0, 0], [2, 0, 1, 1, 0, 0, 0],
      [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0],
      [1, 0, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 2, 0, 0, 0],
      [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0], [1, 2, 1, 0, 0, 0, 0], [0, 4, 0, 0, 0, 0, 0],
      [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 3, 0, 0, 0, 0],
      [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0], [2, 1, 1, 0, 0, 0, 0], [1, 3, 0, 0, 0, 0, 0],
      [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0], [0, 2, 0, 1, 0, 0, 0],
      [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0],
      [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 2, 0, 0, 0],
      [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0],
      [0, 0, 1, 1, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]] := by
  simp only [degreeZeroPiQuarticNoABDFG810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module

set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuarticNoABDFG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABDFG810 A B C D E F G) :
    (degreeZeroPiQuarticNoABDFG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * A.natDegree + 4 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hFpos, hGpos, hAB, hAD, hAF, hAG, hClt, hElt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  rw [speedRefl_degreeZeroPiQuarticNoABDFG810_eq_polyOf]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mdeg_cons,
    Max11ReflectDeg.mdeg_nil_left, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, mul_zero, zero_mul, neg_zero,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
    mul_one, one_mul, and_true, true_and, natDegree_zero]
  repeat' apply And.intro
  all_goals first
    | (right; right; omega)
    | (left; norm_num; done)
    | (right; left; simp; done)
    | trivial

theorem piQuarticFaceABDFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABDFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (piQuarticFaceABDFG810 A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) =
      (1 / 4096 : k) * piQuarticInnerABDFG810 A.leadingCoeff B.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hFpos, hGpos, hAB, hAD, hAF, hAG, hClt, hElt⟩
  simp only [piQuarticFaceABDFG810, piQuarticInnerABDFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A2B4 : ((A ^ 2 * B ^ 4)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 4 hBne), natDegree_pow, natDegree_pow]
  have hcf_A2B4 : ((A ^ 2 * B ^ 4)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 := by
    rw [← hdeg_A2B4, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_AB3D : ((A * B ^ 3 * D)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 3 hBne)) hDne, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
    omega
  have hcf_AB3D : ((A * B ^ 3 * D)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_AB3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB2G : ((A * B ^ 2 * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hGne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2G : ((A * B ^ 2 * G)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_AB2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AF2 : ((A * F ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hFne), natDegree_pow]
    omega
  have hcf_AF2 : ((A * F ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      A.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hdeg_AF2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B3F : ((B ^ 3 * F)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hFne, natDegree_pow]
    omega
  have hcf_B3F : ((B ^ 3 * F)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 3 * F.leadingCoeff := by
    rw [← hdeg_B3F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2D2 : ((B ^ 2 * D ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) (pow_ne_zero 2 hDne), natDegree_pow, natDegree_pow]
    omega
  have hcf_B2D2 : ((B ^ 2 * D ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff ^ 2 := by
    rw [← hdeg_B2D2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_BDG : ((B * D * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hDne) hGne, natDegree_mul hBne hDne]
    omega
  have hcf_BDG : ((B * D * G)).coeff (2 * A.natDegree + 4 * B.natDegree) =
      B.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BDG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_G2 : (G ^ 2).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_G2 : (G ^ 2).coeff (2 * A.natDegree + 4 * B.natDegree) =
      G.leadingCoeff ^ 2 := by
    rw [← hdeg_G2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_A2B4, hcf_AB3D, hcf_AB2G, hcf_AF2, hcf_B3F, hcf_B2D2, hcf_BDG, hcf_G2]
  ring

set_option maxHeartbeats 16000000 in
theorem quarticCone_ABDFG_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABDFG810 A B C D E F G)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hFpos, hGpos, hAB, hAD, hAF, hAG, hClt, hElt⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hFpos, hGpos, hAB, hAD, hAF, hAG, hClt, hElt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hFpos, hGpos, hAB, hAD, hAF, hAG, hClt, hElt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hFpos, hGpos, hAB, hAD, hAF, hAG, hClt, hElt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hFpos, hGpos, hAB, hAD, hAF, hAG, hClt, hElt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hkappainner : kappaQuarticInnerABDFG810 A.leadingCoeff B.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaQuarticNoABDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := kappaQuarticFaceABDFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hApos, hBpos, hDpos, hFpos, hGpos, hAB, hAD, hAF, hAG, hClt, hElt⟩
      omega
    rw [degreeZeroKappaQuartic810_eq_ABDFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 512 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muQuarticInnerABDFG810 A.leadingCoeff B.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoABDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceABDFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + B.natDegree + F.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hApos, hBpos, hDpos, hFpos, hGpos, hAB, hAD, hAF, hAG, hClt, hElt⟩
      omega
    rw [degreeZeroMuQuartic810_eq_ABDFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hnuinner : nuQuarticInnerABDFG810 A.leadingCoeff B.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroNuQuarticNoABDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := nuQuarticFaceABDFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hnu]
      rcases hcone with ⟨hApos, hBpos, hDpos, hFpos, hGpos, hAB, hAD, hAF, hAG, hClt, hElt⟩
      omega
    rw [degreeZeroNuQuartic810_eq_ABDFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hxiinner : xiQuarticInnerABDFG810 A.leadingCoeff B.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroXiQuarticNoABDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := xiQuarticFaceABDFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hxi]
      rcases hcone with ⟨hApos, hBpos, hDpos, hFpos, hGpos, hAB, hAD, hAF, hAG, hClt, hElt⟩
      omega
    rw [degreeZeroXiQuartic810_eq_ABDFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronQuarticInnerABDFG810 A.leadingCoeff B.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronQuarticNoABDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := omicronQuarticFaceABDFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (3 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hApos, hBpos, hDpos, hFpos, hGpos, hAB, hAD, hAF, hAG, hClt, hElt⟩
      omega
    rw [degreeZeroOmicronQuartic810_eq_ABDFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 65536 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hpiinner : piQuarticInnerABDFG810 A.leadingCoeff B.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroPiQuarticNoABDFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := piQuarticFaceABDFG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hpi]
      rcases hcone with ⟨hApos, hBpos, hDpos, hFpos, hGpos, hAB, hAD, hAF, hAG, hClt, hElt⟩
      omega
    rw [degreeZeroPiQuartic810_eq_ABDFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := quarticInner_ABDFG_identity A.leadingCoeff B.leadingCoeff D.leadingCoeff F.leadingCoeff G.leadingCoeff
  have hpow : G.leadingCoeff ^ 3 = 0 := by
    rw [hkappainner, hmuinner, hnuinner, hxiinner, homicroninner, hpiinner] at hid
    simpa using hid.symm
  have hlc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact hlc ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hpow)

def kappaQuarticInnerABEFG810 (a b e f g : k) : k :=
  5 * a * b ^ 3 + 160 * b * g

def muQuarticInnerABEFG810 (a b e f g : k) : k :=
  (-160 : k) * a * b * f + 35 * b ^ 4 + (-240 : k) * b ^ 2 * e + 320 * e ^ 2

def nuQuarticInnerABEFG810 (a b e f g : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + (-160 : k) * a * b * g + (-480 : k) * b ^ 2 * f + 1280 * e * f

end QuarticKills810

end Max11DegreeRoutes
