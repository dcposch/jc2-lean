import InfinityRho1Tie
import FiniteRho2Extraction

/-! # The exact weight-eleven `rho2`/transverse tie at infinity

After all source loads and `rho1` vanish, `rho2` is the next target load.
At `11p = 2δ`, the second Faber row is loaded at the quadratic transverse
scale.  The resulting packet forces a nonzero zero-high terminal coefficient,
hence exact terminal order `11p`, which the infinity degree landing excludes.
-/

noncomputable section
open Polynomial

namespace GCD369CubeHahnCommonCoefficientData

/-- The primitive quadratic Hahn coefficients with second-row value
`186624 * R` are exactly the arbitrary-`rho2` Faber packet. -/
theorem TransverseFactor.rhoTwoTieLeadingFaberRowsAt
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (R : k)
    (h1 : (729 * GCD369CubeFaberN1
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h2 : (2187 * GCD369CubeFaberN2
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 186624 * R)
    (h3 : (GCD369CubeFaberN3
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h4 : (6561 * GCD369CubeFaberN4
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0) :
    GCD369CubeRhoTwoLeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v R := by
  dsimp [GCD369CubeRhoTwoLeadingFaberRowsAt]
  have hc := GCD369CubeFaberCommonNormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v
  dsimp only at hc
  rcases hc with ⟨hc1, hc2, hc3, hc4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc1, ← T.zeroHighN1Coeff]
    exact h1
  · rw [hc2, ← T.zeroHighN2Coeff]
    exact h2
  · rw [hc3, ← T.zeroHighN3Coeff]
    exact h3
  · rw [hc4, ← T.zeroHighN4Coeff]
    exact h4

/-- At the exact tie, the four source equations produce the arbitrary-`rho2`
packet on the infinity residue jet. -/
theorem TransverseScale.rhoTwoLeadingFaberRowsAt_at_transverse
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (R2 R3 R4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant 0)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant 0)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant 0)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : 11 * D.faber.scale.p = 2 * T.delta) :
    GCD369CubeRhoTwoLeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v R2 := by
  have hz := D.faber.rho2NCoeff R2 R3 R4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4
  rcases hz with ⟨hz1, hz2, hz3, hz4⟩
  have heq : ((11 : ℕ) : ℚ) * D.faber.scale.p =
      ((2 : ℕ) : ℚ) * T.delta := by
    norm_num
    exact htie
  rw [heq] at hz1 hz2 hz3 hz4
  exact T.factor.rhoTwoTieLeadingFaberRowsAt R2 hz1 hz2 hz3 hz4

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubeHahnCommonCoefficientData

/-- A nonzero tied `rho2` load forces the common-cubic coordinate `u` to
vanish. -/
theorem TransverseScale.u_eq_zero_of_rho2_tie
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (R2 R3 R4 : k) (hR2 : R2 ≠ 0)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant 0)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant 0)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant 0)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : 11 * D.faber.scale.p = 2 * T.delta) :
    D.u = 0 := by
  have hrows := T.rhoTwoLeadingFaberRowsAt_at_transverse
    R2 R3 R4 hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 htie
  dsimp [GCD369CubeRhoTwoLeadingFaberRowsAt] at hrows
  have hcoeff := GCD369CubeFaberCommonNormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v
  dsimp only at hcoeff
  rcases hrows with ⟨hf1, hf2, _hf3, hf4⟩
  rcases hcoeff with ⟨hc1', hc2', _hc3', hc4'⟩
  rw [hc1'] at hf1
  rw [hc2'] at hf2
  rw [hc4'] at hf4
  have h1 : GCD369CubeNormalRow1
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u = 0 :=
    (mul_eq_zero.mp hf1).resolve_left (by norm_num)
  have h2 : GCD369CubeNormalRow2
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v - 5832 * R2 = 0 := by
    linear_combination (1 / 32 : k) * hf2
  have h4 : GCD369CubeNormalRow4
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v = 0 :=
    (mul_eq_zero.mp hf4).resolve_left (by norm_num)
  have hRu : R2 * D.u = 0 := by
    dsimp only [GCD369CubeNormalRow1, GCD369CubeNormalRow2,
      GCD369CubeNormalRow4] at h1 h2 h4
    linear_combination
      (1 / 972 * D.v) * h1 + (-1 / 5832 * D.u) * h2 +
        (-1 / 17496) * h4
  exact (mul_eq_zero.mp hRu).resolve_left hR2

/-- Consequently the projective common cubic lies on the `v ≠ 0` chart. -/
theorem TransverseScale.v_ne_zero_of_rho2_tie
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (R2 R3 R4 : k) (hR2 : R2 ≠ 0)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant 0)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant 0)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant 0)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : 11 * D.faber.scale.p = 2 * T.delta) :
    D.v ≠ 0 := by
  have hu := T.u_eq_zero_of_rho2_tie R2 R3 R4 hR2
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 htie
  exact D.hprojective.resolve_left (fun h => h hu)

/-- The tied `rho2` packet forces a nonzero zero-high terminal coefficient. -/
theorem TransverseScale.rho2TerminalAt_nonzero_at_transverse
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (R2 R3 R4 : k) (hR2 : R2 ≠ 0)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant 0)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant 0)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant 0)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : 11 * D.faber.scale.p = 2 * T.delta) :
    rho1TerminalAt D T ≠ 0 := by
  have hrows := T.rhoTwoLeadingFaberRowsAt_at_transverse
    R2 R3 R4 hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 htie
  dsimp [GCD369CubeRhoTwoLeadingFaberRowsAt] at hrows
  have hcoeff := GCD369CubeFaberCommonNormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v
  dsimp only at hcoeff
  rcases hrows with ⟨_hf1, hf2, _hf3, _hf4⟩
  rcases hcoeff with ⟨_hc1', hc2', _hc3', _hc4'⟩
  rw [hc2'] at hf2
  have h2 : GCD369CubeNormalRow2
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v - 5832 * R2 = 0 := by
    linear_combination (1 / 32 : k) * hf2
  have hu := T.u_eq_zero_of_rho2_tie R2 R3 R4 hR2
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 htie
  have hv := T.v_ne_zero_of_rho2_tie R2 R3 R4 hR2
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 htie
  intro hterminal
  dsimp only [rho1TerminalAt, GCD369CubeNormalRow2,
    GCD369CubeNormalRow5] at h2 hterminal
  rw [hu] at h2 hterminal
  have hbad : R2 * D.v = 0 := by
    linear_combination (-1 / 5832 * D.v) * h2 +
      (-729 / 5832) * hterminal
  exact (mul_ne_zero hR2 hv) hbad

/-- At the exact tie, the zero-high terminal numerator has its expected
quadratic coefficient. -/
theorem TransverseScale.rho2ZeroHighTerminalCoeff_at_transverse
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (htie : 11 * D.faber.scale.p = 2 * T.delta) :
    (GCD369CubeFaberFullN5
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4 0 0 0 0 0 0 0).1.coeff
        (11 * D.faber.scale.p) =
      559872 * GCD369CubeNormalRow5
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v := by
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let K : GCD369CubeHahnRegular k :=
    559872 * GCD369CubeNormalRow5
      T.Xn T.Yn T.Zn D.cubicU D.cubicV
  let E : GCD369CubeHahnRegular k :=
    839808 * GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU
  have hchart0 : D.faber.scale.regular0 =
      D.cubicV ^ 2 + H * T.Zn := by
    rw [T.regular0_eq]
    dsimp only [H]
    rw [monomial_eq_regularMonomial]
    ring
  have hchart1 : D.faber.scale.regular1 =
      2 * D.cubicU * D.cubicV + H * T.Yn := by
    rw [T.regular1_eq]
    dsimp only [H]
    rw [monomial_eq_regularMonomial]
    ring
  have hchart2 : D.faber.scale.regular2 =
      D.cubicU ^ 2 + H * T.Xn := by
    rw [T.regular2_eq]
    dsimp only [H]
    rw [monomial_eq_regularMonomial]
    ring
  have hzero := GCD369CubeFaberFullN5_zeroHigh_expansion
    T.Xn T.Yn T.Zn D.cubicU D.cubicV H
  have hfactor :
      GCD369CubeFaberFullN5
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 0 0 0 0 0 0 0 =
          H ^ 2 * K + H ^ 3 * E := by
    rw [hchart0, hchart1, hchart2,
      D.regular3_eq_two_cubicV, D.regular4_eq_two_cubicU]
    rw [hzero]
    dsimp only [K, E]
    ring
  have hc := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * T.delta)) hfactor
  have hmain := GCD369CubeHahnRegular.coeff_monomial_pow_mul_at
    T.delta T.hdelta 2 K
  have hhigh := GCD369CubeHahnRegular.coeff_monomial_pow_mul_of_lt
    T.delta T.hdelta 2 3 (by norm_num) E
  change (H ^ 2 * K).1.coeff (2 * T.delta) =
    GCD369CubeHahnRegular.constantCoeff K at hmain
  change (H ^ 3 * E).1.coeff (2 * T.delta) = 0 at hhigh
  change
    (GCD369CubeFaberFullN5
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4 0 0 0 0 0 0 0).1.coeff
        (2 * T.delta) =
      (H ^ 2 * K).1.coeff (2 * T.delta) +
        (H ^ 3 * E).1.coeff (2 * T.delta) at hc
  rw [hmain, hhigh, add_zero] at hc
  rw [← htie] at hc
  rw [hc]
  dsimp only [K]
  simp only [map_mul, map_ofNat, GCD369CubeNormalRow5_map,
    D.constantCoeff_cubicU, D.constantCoeff_cubicV]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- A nonzero tied `rho2` load makes the complete terminal numerator have
exact order `11p`. -/
theorem TransverseScale.fullN5_orderTop_eq_eleven_p_of_rho2_tie
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (R2 R3 R4 : k) (hR2 : R2 ≠ 0)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant 0)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant 0)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant 0)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : 11 * D.faber.scale.p = 2 * T.delta) :
    (GCD369CubeFaberFullN5
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (D.faber.scale.weightedRegular 1 D.faber.d)
      (D.faber.scale.weightedRegular 2 D.faber.c7)
      (D.faber.scale.weightedRegular 4 D.faber.c5)
      (D.faber.scale.weightedRegular 5 D.faber.c4)
      (D.faber.scale.weightedRegular 6 D.faber.c3)
      (D.faber.scale.weightedRegular 7 D.faber.c2)
      (D.faber.scale.weightedRegular 8 D.faber.c1)).1.orderTop =
        (↑(11 * D.faber.scale.p) : WithTop ℚ) := by
  let full : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4
    (D.faber.scale.weightedRegular 1 D.faber.d)
    (D.faber.scale.weightedRegular 2 D.faber.c7)
    (D.faber.scale.weightedRegular 4 D.faber.c5)
    (D.faber.scale.weightedRegular 5 D.faber.c4)
    (D.faber.scale.weightedRegular 6 D.faber.c3)
    (D.faber.scale.weightedRegular 7 D.faber.c2)
    (D.faber.scale.weightedRegular 8 D.faber.c1)
  let zeroRow : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4 0 0 0 0 0 0 0
  have hterminal := T.rho2TerminalAt_nonzero_at_transverse
    R2 R3 R4 hR2
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 htie
  have hspecialCoeff := T.rho2ZeroHighTerminalCoeff_at_transverse htie
  have hspecialCoeffNe :
      zeroRow.1.coeff (11 * D.faber.scale.p) ≠ 0 := by
    change
      (GCD369CubeFaberFullN5
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 0 0 0 0 0 0 0).1.coeff
          (11 * D.faber.scale.p) ≠ 0
    rw [hspecialCoeff]
    exact mul_ne_zero (by norm_num) hterminal
  have hspecialUpper : zeroRow.1.orderTop ≤
      (↑(11 * D.faber.scale.p) : WithTop ℚ) :=
    HahnSeries.orderTop_le_of_coeff_ne_zero hspecialCoeffNe
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let K : GCD369CubeHahnRegular k :=
    559872 * GCD369CubeNormalRow5
      T.Xn T.Yn T.Zn D.cubicU D.cubicV
  let E : GCD369CubeHahnRegular k :=
    839808 * GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU
  have hchart0 : D.faber.scale.regular0 =
      D.cubicV ^ 2 + H * T.Zn := by
    rw [T.regular0_eq]
    dsimp only [H]
    rw [monomial_eq_regularMonomial]
    ring
  have hchart1 : D.faber.scale.regular1 =
      2 * D.cubicU * D.cubicV + H * T.Yn := by
    rw [T.regular1_eq]
    dsimp only [H]
    rw [monomial_eq_regularMonomial]
    ring
  have hchart2 : D.faber.scale.regular2 =
      D.cubicU ^ 2 + H * T.Xn := by
    rw [T.regular2_eq]
    dsimp only [H]
    rw [monomial_eq_regularMonomial]
    ring
  have hzero := GCD369CubeFaberFullN5_zeroHigh_expansion
    T.Xn T.Yn T.Zn D.cubicU D.cubicV H
  have hfactor : zeroRow = H ^ 2 * (K + H * E) := by
    dsimp only [zeroRow]
    rw [hchart0, hchart1, hchart2,
      D.regular3_eq_two_cubicV, D.regular4_eq_two_cubicU]
    rw [hzero]
    dsimp only [K, E]
    ring
  have hspecialLower : (↑(11 * D.faber.scale.p) : WithTop ℚ) ≤
      zeroRow.1.orderTop := by
    rw [hfactor, htie]
    exact GCD369CubeHahnRegular.orderTop_monomial_pow_mul_lower
      T.delta T.hdelta 2 (K + H * E)
  have hspecialOrder : zeroRow.1.orderTop =
      (↑(11 * D.faber.scale.p) : WithTop ℚ) :=
    le_antisymm hspecialUpper hspecialLower
  have hzeroWeighted (w : ℕ) (x : GCD369CubeHahnRegular k)
      (hx : x = GCD369CubeHahnRegular.constant 0) :
      D.faber.scale.weightedRegular w x = 0 := by
    rw [hx]
    apply Subtype.ext
    simp [GCD369CubeHahnPoleScale.weightedRegular]
  have hfull : full = zeroRow := by
    dsimp only [full, zeroRow]
    rw [hzeroWeighted 1 D.faber.d hd,
      hzeroWeighted 2 D.faber.c7 hc7,
      hzeroWeighted 4 D.faber.c5 hc5,
      hzeroWeighted 5 D.faber.c4 hc4,
      hzeroWeighted 6 D.faber.c3 hc3,
      hzeroWeighted 7 D.faber.c2 hc2,
      hzeroWeighted 8 D.faber.c1 hc1]
  change full.1.orderTop = (↑(11 * D.faber.scale.p) : WithTop ℚ)
  rw [hfull]
  exact hspecialOrder

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubePolynomialSource

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- A nonzero `rho2` load cannot tie the first transverse normal once all
source loads and `rho1` vanish. -/
theorem infinity_rho2_eq_zero_at_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hd0 : S.faberConstantParameters.d = 0)
    (hc70 : S.faberConstantParameters.c7 = 0)
    (hc50 : S.faberConstantParameters.c5 = 0)
    (hc40 : S.faberConstantParameters.c4 = 0)
    (hc30 : S.faberConstantParameters.c3 = 0)
    (hc20 : S.faberConstantParameters.c2 = 0)
    (hc10 : S.faberConstantParameters.c1 = 0)
    (hr10 : S.faberFirstIntegralConstants.rho1 = 0)
    (htie :
      11 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p =
        2 * T.delta) :
    S.faberFirstIntegralConstants.rho2 = 0 := by
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let D := S.infinityCommonCoefficientData hsdegree
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  obtain ⟨hdraw, hc7raw, hc5raw, hc4raw, hc3raw, hc2raw, hc1raw,
      hr1raw, hr2raw, hr3raw, hr4raw⟩ :=
    S.infinityFaberPoleData_constant_loads hpole
  have hd : D.faber.d = GCD369CubeHahnRegular.constant 0 := by
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    simpa only [P, hd0] using hdraw
  have hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0 := by
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    simpa only [P, hc70] using hc7raw
  have hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0 := by
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    simpa only [P, hc50] using hc5raw
  have hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0 := by
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    simpa only [P, hc40] using hc4raw
  have hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0 := by
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    simpa only [P, hc30] using hc3raw
  have hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant 0 := by
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    simpa only [P, hc20] using hc2raw
  have hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant 0 := by
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    simpa only [P, hc10] using hc1raw
  have hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant 0 := by
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    simpa only [R, hr10] using hr1raw
  have hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R.rho2 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree]
      using hr2raw
  have hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R.rho3 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree]
      using hr3raw
  have hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R.rho4 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree]
      using hr4raw
  by_contra hR2
  apply hR2
  apply S.infinity_rho2_eq_zero_of_terminal_order_eq_eleven
    hsdegree T htie.symm
  intro _hload
  have hNorder := T.fullN5_orderTop_eq_eleven_p_of_rho2_tie
    R.rho2 R.rho3 R.rho4 hR2
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 htie
  have hterminalOrder :=
    GCD369CubeHahnFaberPoleData.faberR5_order_eq_of_fullN5_orderTop_eq
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (D.faber.scale.weightedRegular 1 D.faber.d)
      (D.faber.scale.weightedRegular 2 D.faber.c7)
      (D.faber.scale.weightedRegular 4 D.faber.c5)
      (D.faber.scale.weightedRegular 5 D.faber.c4)
      (D.faber.scale.weightedRegular 6 D.faber.c3)
      (D.faber.scale.weightedRegular 7 D.faber.c2)
      (D.faber.scale.weightedRegular 8 D.faber.c1)
      (11 * D.faber.scale.p) hNorder
  let terminal : HahnSeries ℚ k := GCD369CubeFaberR5
    (D.faber.scale.regular0 : HahnSeries ℚ k)
    D.faber.scale.regular1 D.faber.scale.regular2
    D.faber.scale.regular3 D.faber.scale.regular4
    (D.faber.scale.weightedRegular 1 D.faber.d)
    (D.faber.scale.weightedRegular 2 D.faber.c7)
    (D.faber.scale.weightedRegular 4 D.faber.c5)
    (D.faber.scale.weightedRegular 5 D.faber.c4)
    (D.faber.scale.weightedRegular 6 D.faber.c3)
    (D.faber.scale.weightedRegular 7 D.faber.c2)
    (D.faber.scale.weightedRegular 8 D.faber.c1)
  have hscaled : terminal = D.faber.scale.t ^ 14 *
      GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant := by
    have hs := S.infinityFaberPoleData_scaled_terminal hpole
    change terminal = D.faber.scale.t ^ 14 *
      GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant at hs
    exact hs
  dsimp only
  rw [← hscaled]
  simpa only [terminal] using hterminalOrder

/-- Target-normalized source wrapper: canonical uniqueness supplies
`d=c3=0`; the remaining load vanishings stay explicit. -/
theorem targetNormalized_infinity_rho2_eq_zero_at_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (hd0 : S.faberConstantParameters.d = 0)
    (T : let U := S.targetNormalizedSource
      (U.infinityCommonCoefficientData (by
        simpa [U, targetNormalizedSource] using hsdegree)).TransverseScale)
    (hc70 : S.targetNormalizedSource.faberConstantParameters.c7 = 0)
    (hc50 : S.targetNormalizedSource.faberConstantParameters.c5 = 0)
    (hc40 : S.targetNormalizedSource.faberConstantParameters.c4 = 0)
    (hc20 : S.targetNormalizedSource.faberConstantParameters.c2 = 0)
    (hc10 : S.targetNormalizedSource.faberConstantParameters.c1 = 0)
    (hr10 : S.targetNormalizedSource.faberFirstIntegralConstants.rho1 = 0)
    (htie : let U := S.targetNormalizedSource
      let hsdegreeU : U.s.natDegree = 0 := by
        simpa [U, targetNormalizedSource] using hsdegree
      11 * (U.infinityCommonCoefficientData hsdegreeU).faber.scale.p =
        2 * T.delta) :
    S.targetNormalizedSource.faberFirstIntegralConstants.rho2 = 0 := by
  let U := S.targetNormalizedSource
  let Q := U.faberConstantParameters
  have hsdegreeU : U.s.natDegree = 0 := by
    simpa [U, targetNormalizedSource] using hsdegree
  obtain ⟨hQd, _hQc7, _hQc6, _hQc5, _hQc4, hQc3,
      _hQc2, _hQc1, _hQc0⟩ :=
    S.targetNormalizedCanonicalParameters hd0
  apply U.infinity_rho2_eq_zero_at_transverse hsdegreeU T
  · simpa only [Q, U] using hQd
  · simpa only [U] using hc70
  · simpa only [U] using hc50
  · simpa only [U] using hc40
  · simpa only [Q, U] using hQc3
  · simpa only [U] using hc20
  · simpa only [U] using hc10
  · simpa only [U] using hr10
  · exact htie

end GCD369CubePolynomialSource

#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.rhoTwoLeadingFaberRowsAt_at_transverse
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.rho2TerminalAt_nonzero_at_transverse
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.rho2ZeroHighTerminalCoeff_at_transverse
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.fullN5_orderTop_eq_eleven_p_of_rho2_tie
#print axioms GCD369CubePolynomialSource.infinity_rho2_eq_zero_at_transverse
#print axioms
  GCD369CubePolynomialSource.targetNormalized_infinity_rho2_eq_zero_at_transverse
