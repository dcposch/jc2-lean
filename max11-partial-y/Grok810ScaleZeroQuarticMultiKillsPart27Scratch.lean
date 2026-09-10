import Grok810ScaleZeroQuarticMultiKillsPart26Scratch

/-! Part 27 of 47 of `Grok810ScaleZeroQuarticMultiKillsScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

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


set_option maxHeartbeats 400000000 in
/-- Reflected form of `degreeZeroPiQuarticNoACG810` (92 monomials, 7 atoms):
the CAS-emitted coefficient list and exponent vectors.  Proved once, and
used by every case-fan branch below, so the polynomial is reflected once
instead of `2^k` times. -/
theorem speedRefl_degreeZeroPiQuarticNoACG810_eq_polyOf
    (l beta gamma delta epsilon zeta eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroPiQuarticNoACG810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      Max11ReflectDeg.polyOf [A, B, C, D, E, F, G]
      [
      (15 / 4096 : k), (-(15 / 128) : k), (-(45 / 512) : k),
      (-(35 / 256) : k), (5 / 64 : k), (5 / 32 : k),
      (5 / 16 : k), (5 / 32 : k), (25 / 128 : k),
      (45 / 64 : k), (45 / 128 : k), (45 / 64 : k),
      (-(5 / 16) : k), (-(5 / 8) : k), (-(15 / 16) : k),
      (-(15 / 16) : k), (-(5 / 8) : k), (-(5 / 8) : k),
      (45 / 131072 * l : k), (-(3 / 32768 * l) : k), (-(45 / 32768 * l) : k),
      (9 / 4096 * l : k), (9 / 4096 * l : k), (-(27 / 4096 * l) : k),
      (9 / 4096 * l : k), (-(189 / 4096 * l) : k), (-(63 / 4096 * l) : k),
      (-(27 / 1024 * l) : k), (9 / 512 * l : k), (63 / 1024 * l : k),
      (9 / 128 * l : k), (27 / 256 * l : k), (9 / 256 * l : k),
      (63 / 512 * l : k), (189 / 512 * l : k), (63 / 512 * l : k),
      (-(9 / 64 * l) : k), (-(9 / 32 * l) : k), (-(27 / 64 * l) : k),
      (-(9 / 32 * l) : k), (-(27 / 128 * l) : k), (-(9 / 16 * l) : k),
      (-(3 / 32 * l) : k), (9 / 8 * l : k), (7 / 4096 * beta : k),
      (7 / 4096 * beta : k), (-(7 / 1024 * beta) : k), (7 / 512 * beta : k),
      (7 / 512 * beta : k), (-(21 / 256 * beta) : k), (-(7 / 256 * beta) : k),
      (-(63 / 512 * beta) : k), (-(7 / 64 * beta) : k), (7 / 32 * beta : k),
      (21 / 128 * beta : k), (7 / 16 * beta : k), (7 / 32 * beta : k),
      (7 / 32 * beta : k), (-(7 / 8 * beta) : k), (-(3 / 32 * gamma) : k),
      (-(15 / 256 * gamma) : k), (3 / 16 * gamma : k), (3 / 8 * gamma : k),
      (3 / 4 * gamma : k), (1 / 8 * gamma : k), (-(3 / 4 * gamma) : k),
      (-(3 / 4 * gamma) : k), (5 / 512 * delta : k), (-(15 / 256 * delta) : k),
      (-(5 / 128 * delta) : k), (5 / 32 * delta : k), (5 / 32 * delta : k),
      (15 / 32 * delta : k), (15 / 32 * delta : k), (-(5 / 8 * delta) : k),
      (-(5 / 4 * delta) : k), (1 / 4 * epsilon : k), (1 / 2 * epsilon : k),
      (-(1 / 2 * epsilon) : k), (-(1 * epsilon) : k), (-(1 / 2 * epsilon) : k),
      (3 / 32 * zeta : k), (5 / 32 * zeta : k), (-(3 / 8 * zeta) : k),
      (-(3 / 4 * zeta) : k), (-(3 / 4 * zeta) : k), (1 / 16 * eta : k),
      (-(1 / 2 * eta) : k), (-(1 / 4 * eta) : k), (2 * eta : k),
      (-(1 / 4 * theta) : k), (1 * theta : k)]
      [
      [2, 4, 0, 0, 0, 0, 0], [1, 3, 0, 1, 0, 0, 0], [1, 2, 2, 0, 0, 0, 0], [0, 4, 1, 0, 0, 0, 0],
      [1, 2, 0, 0, 0, 0, 1], [1, 1, 1, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 0], [1, 0, 1, 2, 0, 0, 0],
      [0, 3, 0, 0, 0, 1, 0], [0, 2, 1, 0, 1, 0, 0], [0, 2, 0, 2, 0, 0, 0], [0, 1, 2, 1, 0, 0, 0],
      [1, 0, 0, 0, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0], [0, 0, 1, 1, 0, 1, 0],
      [0, 0, 1, 0, 2, 0, 0], [0, 0, 0, 2, 1, 0, 0], [4, 1, 1, 0, 0, 0, 0], [3, 3, 0, 0, 0, 0, 0],
      [4, 0, 0, 0, 0, 1, 0], [3, 1, 0, 0, 1, 0, 0], [3, 0, 1, 1, 0, 0, 0], [2, 2, 0, 1, 0, 0, 0],
      [2, 1, 2, 0, 0, 0, 0], [1, 3, 1, 0, 0, 0, 0], [0, 5, 0, 0, 0, 0, 0], [2, 0, 1, 0, 0, 1, 0],
      [2, 0, 0, 1, 1, 0, 0], [1, 2, 0, 0, 0, 1, 0], [1, 1, 1, 0, 1, 0, 0], [1, 1, 0, 2, 0, 0, 0],
      [1, 0, 2, 1, 0, 0, 0], [0, 3, 0, 0, 1, 0, 0], [0, 2, 1, 1, 0, 0, 0], [0, 1, 3, 0, 0, 0, 0],
      [1, 0, 0, 0, 1, 1, 0], [0, 1, 1, 0, 0, 0, 1], [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 2, 0, 0],
      [0, 0, 2, 0, 0, 1, 0], [0, 0, 1, 1, 1, 0, 0], [0, 0, 0, 3, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1],
      [3, 1, 1, 0, 0, 0, 0], [2, 3, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 1, 0], [2, 1, 0, 0, 1, 0, 0],
      [2, 0, 1, 1, 0, 0, 0], [1, 2, 0, 1, 0, 0, 0], [1, 1, 2, 0, 0, 0, 0], [0, 3, 1, 0, 0, 0, 0],
      [1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0], [0, 2, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0],
      [0, 1, 0, 2, 0, 0, 0], [0, 0, 2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0], [1, 2, 1, 0, 0, 0, 0],
      [0, 4, 0, 0, 0, 0, 0], [1, 0, 0, 2, 0, 0, 0], [0, 2, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0],
      [0, 0, 3, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 2, 0, 0], [2, 1, 1, 0, 0, 0, 0],
      [1, 3, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 1, 0], [1, 1, 0, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0, 0],
      [0, 2, 0, 1, 0, 0, 0], [0, 1, 2, 0, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0],
      [1, 1, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0],
      [0, 0, 0, 2, 0, 0, 0], [1, 1, 1, 0, 0, 0, 0], [0, 3, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 1, 0],
      [0, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 0], [1, 2, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0],
      [0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]] := by
  simp only [degreeZeroPiQuarticNoACG810, Max11ReflectDeg.polyOf_cons,
    Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons,
    Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right,
    pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc]
  module


set_option maxHeartbeats 32000000 in
theorem degreeZeroPiQuarticNoACG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACG810 A B C D E F G) :
    (degreeZeroPiQuarticNoACG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * C.natDegree := by
  rcases hcone with ⟨hApos, hCpos, hGpos, hAC, hAG, hBlt, hDlt, hElt, hFlt⟩
  have hB1 : 2 * B.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hBlt
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  rw [speedRefl_degreeZeroPiQuarticNoACG810_eq_polyOf]
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


theorem piQuarticFaceACG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeACG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hGne : G ≠ 0)
    : (piQuarticFaceACG810 A B C D E F G).coeff (4 * C.natDegree) =
      (1 / 256 : k) * piQuarticInnerACG810 A.leadingCoeff C.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hCpos, hGpos, hAC, hAG, hBlt, hDlt, hElt, hFlt⟩
  simp only [piQuarticFaceACG810, piQuarticInnerACG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_C4 : (C ^ 4).natDegree = 4 * C.natDegree := by
    rw [natDegree_pow]
  have hcf_C4 : (C ^ 4).coeff (4 * C.natDegree) =
      C.leadingCoeff ^ 4 := by
    rw [← hdeg_C4, coeff_natDegree, leadingCoeff_pow]
  have hdeg_C2G : ((C ^ 2 * G)).natDegree = 4 * C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne, natDegree_pow]
    omega
  have hcf_C2G : ((C ^ 2 * G)).coeff (4 * C.natDegree) =
      C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hdeg_C2G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_G2 : (G ^ 2).natDegree = 4 * C.natDegree := by
    rw [natDegree_pow]
    omega
  have hcf_G2 : (G ^ 2).coeff (4 * C.natDegree) =
      G.leadingCoeff ^ 2 := by
    rw [← hdeg_G2, coeff_natDegree, leadingCoeff_pow]
  rw [hcf_C4, hcf_C2G, hcf_G2]
  ring


set_option maxHeartbeats 16000000 in
theorem quarticCone_ACG_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACG810 A B C D E F G)
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
    rcases hcone with ⟨hApos, hCpos, hGpos, hAC, hAG, hBlt, hDlt, hElt, hFlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hGpos, hAC, hAG, hBlt, hDlt, hElt, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hGpos, hAC, hAG, hBlt, hDlt, hElt, hFlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hmuinner : muQuarticInnerACG810 A.leadingCoeff C.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoACG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceACG810_coeff_top (hcone := hcone) (hAne := hAne) (hCne := hCne) (hGne := hGne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (3 * C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hApos, hCpos, hGpos, hAC, hAG, hBlt, hDlt, hElt, hFlt⟩
      omega
    rw [degreeZeroMuQuartic810_eq_ACG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hpiinner : piQuarticInnerACG810 A.leadingCoeff C.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroPiQuarticNoACG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := piQuarticFaceACG810_coeff_top (hcone := hcone) (hAne := hAne) (hCne := hCne) (hGne := hGne)
    have hz : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (4 * C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hpi]
      rcases hcone with ⟨hApos, hCpos, hGpos, hAC, hAG, hBlt, hDlt, hElt, hFlt⟩
      omega
    rw [degreeZeroPiQuartic810_eq_ACG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 256 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := quarticInner_ACG_identity A.leadingCoeff C.leadingCoeff G.leadingCoeff
  have hpow : C.leadingCoeff ^ 5 = 0 := by
    rw [hmuinner, hpiinner] at hid
    simpa using hid.symm
  have hlc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  exact hlc ((pow_eq_zero_iff (by decide : (5 : ℕ) ≠ 0)).mp hpow)



end QuarticKills810
end Max11DegreeRoutes
end
