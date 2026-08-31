import InfinityC4Before
import InfinityLoadLanding

/-! # The exact weight-five/transverse tie at infinity

When `5p = 2δ`, the first `c4` load and the quadratic transverse normal
arrive at the same Hahn order.  The tied first four rows certify a nonzero
terminal coefficient for every nonzero `c4`; its exact terminal order is
then excluded by the constant-core degree landing.
-/

noncomputable section
open Polynomial

namespace GCD369CubeHahnCommonCoefficientData

/-- Coefficient of the pure `c4` load in the denominator-cleared terminal
numerator. -/
def terminalC4Coeff {R : Type*} [CommRing R]
    (_a0 a1 a2 a3 a4 : R) : R :=
  -1492992 * a1 * a2 + 373248 * a1 * a4 ^ 2 +
    995328 * a2 * a3 * a4 + 165888 * a3 ^ 3 -
    290304 * a3 * a4 ^ 3

/-- Isolate the pure `c4` contribution to the terminal numerator. -/
theorem fullN5_c4_specialize
    {R : Type*} [CommRing R]
    (a0 a1 a2 a3 a4 c4 : R) :
    GCD369CubeFaberFullN5 a0 a1 a2 a3 a4 0 0 0 c4 0 0 0 =
      GCD369CubeFaberFullN5 a0 a1 a2 a3 a4 0 0 0 0 0 0 0 +
        c4 * terminalC4Coeff a0 a1 a2 a3 a4 := by
  simp only [terminalC4Coeff]
  ring

/-- At the exact `c4`/transverse tie, the four source equations are the
arbitrary-`c4` row packet on the infinity residue jet. -/
theorem TransverseScale.c4LeadingFaberRowsAt_at_transverse
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : 5 * D.faber.scale.p = 2 * T.delta) :
    GCD369CubeC4LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C4 := by
  have hz := D.faber.c4NCoeff_zero C3 C2 C1 R1 R2 R3 R4
    hd hc7 hc5 hc3 hc2 hc1 hr1 hr2 hr3 hr4
  have hhalf : ((5 : ℚ) * D.faber.scale.p) / 2 = T.delta := by
    linarith
  have hweighted : D.faber.scale.weightedRegular 5 D.faber.c4 =
      (GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
        GCD369CubeHahnRegular.constant C4 := by
    rw [hc4, D.faber.scale.weightedRegular_constant_eq_monomial_sq
      5 (by norm_num) C4]
    apply Subtype.ext
    change
      (HahnSeries.single (((5 : ℕ) : ℚ) * D.faber.scale.p / 2) (1 : k)) ^ 2 *
          HahnSeries.C C4 =
        (HahnSeries.single T.delta (1 : k)) ^ 2 * HahnSeries.C C4
    congr 4
  rw [hweighted] at hz
  rcases hz with ⟨hz1, hz2, hz3, hz4⟩
  have heq : ((5 : ℕ) : ℚ) * D.faber.scale.p =
      ((2 : ℕ) : ℚ) * T.delta := by
    norm_num
    exact htie
  rw [heq] at hz1 hz2 hz3 hz4
  exact T.factor.c4BeforeLeadingFaberRowsAt C4 hz1 hz2 hz3 hz4

/-- A nonzero tied `c4` load forces the leading weight-three common-cubic
coordinate to be nonzero. -/
theorem TransverseScale.v_ne_zero_of_c4_tie
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hC4 : C4 ≠ 0)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : 5 * D.faber.scale.p = 2 * T.delta) :
    D.v ≠ 0 := by
  have hrows := T.c4LeadingFaberRowsAt_at_transverse
    C4 C3 C2 C1 R1 R2 R3 R4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 htie
  dsimp [GCD369CubeC4LeadingFaberRowsAt] at hrows
  have hcoeff := GCD369CubeFaberC4NormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C4
  dsimp at hcoeff
  rcases hrows with ⟨_hf1, hf2, _hf3, hf4⟩
  rcases hcoeff with ⟨_hc1', hc2', _hc3', hc4'⟩
  rw [hc2'] at hf2
  rw [hc4'] at hf4
  have h2 :
      32 * C4 * D.u ^ 3 - 144 * C4 * D.v ^ 2 +
        243 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
        486 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) -
        486 * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) = 0 :=
    (mul_eq_zero.mp hf2).resolve_left (by norm_num)
  have h4 :
      8 * C4 * D.u ^ 4 - 96 * C4 * D.u * D.v ^ 2 -
        243 * D.u * D.v *
          (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
        162 * D.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) +
        324 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) +
        162 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 +
        162 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) = 0 :=
    (mul_eq_zero.mp hf4).resolve_left (by norm_num)
  intro hv
  have hu : D.u ≠ 0 := D.hprojective.resolve_right (fun hne => hne hv)
  rw [hv] at h2 h4
  have hbad : C4 * D.u ^ 4 = 0 := by
    linear_combination (1 / 56 : k) * (D.u * h2 + 3 * h4)
  exact (mul_ne_zero hC4 (pow_ne_zero 4 hu)) hbad

/-- The unnormalized weight-five terminal polynomial at a tied `c4` load. -/
def c4TerminalAt {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k)
    (T : D.TransverseScale) (C4 : k) : k :=
  32 * C4 * D.u ^ 3 * D.v - 64 * C4 * D.v ^ 3 +
    27 * D.u ^ 3 * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
    81 * D.v ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
    162 * D.u * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
      (GCD369CubeHahnRegular.constantCoeff T.Yn) -
    54 * D.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
      (GCD369CubeHahnRegular.constantCoeff T.Zn) -
    27 * D.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 +
    162 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
      (GCD369CubeHahnRegular.constantCoeff T.Zn)

/-- The actual unnormalized terminal polynomial is nonzero whenever the
tied `c4` load is nonzero. -/
theorem TransverseScale.c4TerminalAt_nonzero_at_transverse
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hC4 : C4 ≠ 0)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : 5 * D.faber.scale.p = 2 * T.delta) :
    c4TerminalAt D T C4 ≠ 0 := by
  have hrows := T.c4LeadingFaberRowsAt_at_transverse
    C4 C3 C2 C1 R1 R2 R3 R4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 htie
  dsimp [GCD369CubeC4LeadingFaberRowsAt] at hrows
  have hcoeff := GCD369CubeFaberC4NormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C4
  dsimp at hcoeff
  rcases hrows with ⟨hf1, hf2, _hf3, hf4⟩
  rcases hcoeff with ⟨hc1', hc2', _hc3', hc4'⟩
  rw [hc1'] at hf1
  rw [hc2'] at hf2
  rw [hc4'] at hf4
  have h1 :
      32 * C4 * D.u * D.v -
        27 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
        54 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) +
        27 * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 = 0 :=
    (mul_eq_zero.mp hf1).resolve_left (by norm_num)
  have h2 :
      32 * C4 * D.u ^ 3 - 144 * C4 * D.v ^ 2 +
        243 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
        486 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) -
        486 * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) = 0 :=
    (mul_eq_zero.mp hf2).resolve_left (by norm_num)
  have h4 :
      8 * C4 * D.u ^ 4 - 96 * C4 * D.u * D.v ^ 2 -
        243 * D.u * D.v *
          (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
        162 * D.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) +
        324 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) +
        162 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 +
        162 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) = 0 :=
    (mul_eq_zero.mp hf4).resolve_left (by norm_num)
  intro hterminal
  dsimp only [c4TerminalAt] at hterminal
  by_cases hu : D.u = 0
  · have hv : D.v ≠ 0 := D.hprojective.resolve_left (fun h => h hu)
    rw [hu] at h2 hterminal
    have hbad : C4 * D.v ^ 3 = 0 := by
      linear_combination (-1 / 336 : k) * (D.v * h2) +
        (-1 / 112 : k) * hterminal
    exact (mul_ne_zero hC4 (pow_ne_zero 3 hv)) hbad
  · have hbad : C4 * D.u ^ 7 = 0 := by
      linear_combination
        (-9 / 154 * D.u ^ 3 * D.v + 81 / 154 * D.v ^ 3) * h1 +
        (1 / 56 * D.u ^ 4 + 9 / 154 * D.u * D.v ^ 2) * h2 +
        (3 / 56 * D.u ^ 3 - 27 / 308 * D.v ^ 2) * h4 +
        (81 / 308 * D.u * D.v) * hterminal
    exact (mul_ne_zero hC4 (pow_ne_zero 7 hu)) hbad

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- At the exact tie, the pure-`c4` terminal numerator has coefficient
`-20736` times the unnormalized terminal polynomial. -/
theorem TransverseScale.c4SpecializedTerminalCoeff_at_transverse
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C4 : k)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (htie : 5 * D.faber.scale.p = 2 * T.delta) :
    (GCD369CubeFaberFullN5
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4 0 0 0
      (D.faber.scale.weightedRegular 5 D.faber.c4)
      0 0 0).1.coeff (5 * D.faber.scale.p) =
      -20736 * c4TerminalAt D T C4 := by
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let P : GCD369CubeHahnRegular k := terminalC4Coeff
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4
  let K : GCD369CubeHahnRegular k :=
    559872 * GCD369CubeNormalRow5
      T.Xn T.Yn T.Zn D.cubicU D.cubicV +
      GCD369CubeHahnRegular.constant C4 * P
  let E : GCD369CubeHahnRegular k :=
    839808 * GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU
  have hhalf : ((5 : ℚ) * D.faber.scale.p) / 2 = T.delta := by
    linarith
  have hload : D.faber.scale.weightedRegular 5 D.faber.c4 =
      H ^ 2 * GCD369CubeHahnRegular.constant C4 := by
    rw [hc4, D.faber.scale.weightedRegular_constant_eq_monomial_sq
      5 (by norm_num) C4]
    apply Subtype.ext
    change
      (HahnSeries.single (((5 : ℕ) : ℚ) * D.faber.scale.p / 2) (1 : k)) ^ 2 *
          HahnSeries.C C4 =
        (HahnSeries.single T.delta (1 : k)) ^ 2 * HahnSeries.C C4
    congr 4
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
        D.faber.scale.regular4 0 0 0
        (D.faber.scale.weightedRegular 5 D.faber.c4)
        0 0 0 = H ^ 2 * K + H ^ 3 * E := by
    rw [fullN5_c4_specialize, hload]
    rw [hchart0, hchart1, hchart2,
      D.regular3_eq_two_cubicV, D.regular4_eq_two_cubicU]
    rw [hzero]
    dsimp only [K, E]
    rw [← hchart0, ← hchart1, ← hchart2,
      ← D.regular3_eq_two_cubicV, ← D.regular4_eq_two_cubicU]
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
      D.faber.scale.regular4 0 0 0
      (D.faber.scale.weightedRegular 5 D.faber.c4)
      0 0 0).1.coeff (2 * T.delta) =
      (H ^ 2 * K).1.coeff (2 * T.delta) +
        (H ^ 3 * E).1.coeff (2 * T.delta) at hc
  rw [hmain, hhigh, add_zero] at hc
  rw [← htie] at hc
  rw [hc]
  dsimp only [K, P, terminalC4Coeff, c4TerminalAt]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat,
    GCD369CubeNormalRow5_map, D.constantCoeff_cubicU,
    D.constantCoeff_cubicV,
    GCD369CubeHahnRegular.constantCoeff_constant]
  have ha1 : GCD369CubeHahnRegular.constantCoeff
      D.faber.scale.regular1 = D.faber.scale.leading1 := rfl
  have ha2 : GCD369CubeHahnRegular.constantCoeff
      D.faber.scale.regular2 = D.faber.scale.leading2 := rfl
  have ha3 : GCD369CubeHahnRegular.constantCoeff
      D.faber.scale.regular3 = D.faber.scale.leading3 := rfl
  have ha4 : GCD369CubeHahnRegular.constantCoeff
      D.faber.scale.regular4 = D.faber.scale.leading4 := rfl
  rw [ha1, ha2, ha3, ha4,
    D.ha1, D.ha2, D.ha3, D.ha4]
  dsimp only [GCD369CubeNormalRow5]
  ring

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubeHahnFaberPoleData

/-- With `d=c7=c5=0`, every load strictly after `c4` is invisible through
the weight-five terminal cutoff. -/
theorem fullN5_sub_c4Specialized_mem_higherOrderIdeal
    {k : Type*} [Field k] [CharZero k]
    (F : GCD369CubeHahnFaberPoleData k)
    (C3 C2 C1 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant 0)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1) :
    GCD369CubeFaberFullN5
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4
      (F.scale.weightedRegular 1 F.d)
      (F.scale.weightedRegular 2 F.c7)
      (F.scale.weightedRegular 4 F.c5)
      (F.scale.weightedRegular 5 F.c4)
      (F.scale.weightedRegular 6 F.c3)
      (F.scale.weightedRegular 7 F.c2)
      (F.scale.weightedRegular 8 F.c1) -
    GCD369CubeFaberFullN5
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4 0 0 0
      (F.scale.weightedRegular 5 F.c4) 0 0 0 ∈
        GCD369CubeHahnRegular.higherOrderIdeal
          (5 * F.scale.p) (mul_nonneg (by norm_num) F.scale.hp.le) := by
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal
      (5 * F.scale.p) (mul_nonneg (by norm_num) F.scale.hp.le)
  let q := Ideal.Quotient.mk I
  have hweight (w : ℕ) (hw : 5 < w) :
      5 * F.scale.p < (w : ℚ) * F.scale.p := by
    exact mul_lt_mul_of_pos_right
      (show (5 : ℚ) < (w : ℚ) by exact_mod_cast hw) F.scale.hp
  have hzeroWeighted (w : ℕ) (x : GCD369CubeHahnRegular k)
      (hx : x = GCD369CubeHahnRegular.constant 0) :
      F.scale.weightedRegular w x = 0 := by
    rw [hx]
    apply Subtype.ext
    simp [GCD369CubeHahnPoleScale.weightedRegular]
  have hdq : q (F.scale.weightedRegular 1 F.d) = 0 := by
    rw [hzeroWeighted 1 F.d hd, map_zero]
  have hc7q : q (F.scale.weightedRegular 2 F.c7) = 0 := by
    rw [hzeroWeighted 2 F.c7 hc7, map_zero]
  have hc5q : q (F.scale.weightedRegular 4 F.c5) = 0 := by
    rw [hzeroWeighted 4 F.c5 hc5, map_zero]
  have hkill (w : ℕ) (hw : 5 < w) (c : k)
      (x : GCD369CubeHahnRegular k)
      (hx : x = GCD369CubeHahnRegular.constant c) :
      q (F.scale.weightedRegular w x) = 0 := by
    rw [hx, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale w c (mul_nonneg (by norm_num) F.scale.hp.le) (hweight w hw)
  have hc3q := hkill 6 (by norm_num) C3 F.c3 hc3
  have hc2q := hkill 7 (by norm_num) C2 F.c2 hc2
  have hc1q := hkill 8 (by norm_num) C1 F.c1 hc1
  let full : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
    (F.scale.weightedRegular 1 F.d)
    (F.scale.weightedRegular 2 F.c7)
    (F.scale.weightedRegular 4 F.c5)
    (F.scale.weightedRegular 5 F.c4)
    (F.scale.weightedRegular 6 F.c3)
    (F.scale.weightedRegular 7 F.c2)
    (F.scale.weightedRegular 8 F.c1)
  let c4row : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4 0 0 0
    (F.scale.weightedRegular 5 F.c4) 0 0 0
  have hq : q full = q c4row := by
    dsimp only [full, c4row]
    rw [GCD369CubeFaberFullN5_map, GCD369CubeFaberFullN5_map,
      hdq, hc7q, hc5q, hc3q, hc2q, hc1q]
    simp
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [map_sub, hq, sub_self]

end GCD369CubeHahnFaberPoleData

namespace GCD369CubeHahnCommonCoefficientData

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- A nonzero tied `c4` load makes the complete terminal numerator have
exact order `5p`; all later loads are strictly higher. -/
theorem TransverseScale.fullN5_orderTop_eq_five_p_of_c4_tie
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hC4 : C4 ≠ 0)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : 5 * D.faber.scale.p = 2 * T.delta) :
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
        (↑(5 * D.faber.scale.p) : WithTop ℚ) := by
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
  let c4row : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4 0 0 0
    (D.faber.scale.weightedRegular 5 D.faber.c4) 0 0 0
  have hterminal := T.c4TerminalAt_nonzero_at_transverse
    C4 C3 C2 C1 R1 R2 R3 R4 hC4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 htie
  have hspecialCoeff := T.c4SpecializedTerminalCoeff_at_transverse
    C4 hc4 htie
  have hspecialCoeffNe :
      c4row.1.coeff (5 * D.faber.scale.p) ≠ 0 := by
    change
      (GCD369CubeFaberFullN5
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 0 0 0
        (D.faber.scale.weightedRegular 5 D.faber.c4)
        0 0 0).1.coeff (5 * D.faber.scale.p) ≠ 0
    rw [hspecialCoeff]
    exact mul_ne_zero (by norm_num) hterminal
  have hspecialUpper : c4row.1.orderTop ≤
      (↑(5 * D.faber.scale.p) : WithTop ℚ) :=
    HahnSeries.orderTop_le_of_coeff_ne_zero hspecialCoeffNe
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let P : GCD369CubeHahnRegular k := terminalC4Coeff
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4
  let K : GCD369CubeHahnRegular k :=
    559872 * GCD369CubeNormalRow5
      T.Xn T.Yn T.Zn D.cubicU D.cubicV +
      GCD369CubeHahnRegular.constant C4 * P
  let E : GCD369CubeHahnRegular k :=
    839808 * GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU
  have hhalf : ((5 : ℚ) * D.faber.scale.p) / 2 = T.delta := by
    linarith
  have hload : D.faber.scale.weightedRegular 5 D.faber.c4 =
      H ^ 2 * GCD369CubeHahnRegular.constant C4 := by
    rw [hc4, D.faber.scale.weightedRegular_constant_eq_monomial_sq
      5 (by norm_num) C4]
    apply Subtype.ext
    change
      (HahnSeries.single (((5 : ℕ) : ℚ) * D.faber.scale.p / 2) (1 : k)) ^ 2 *
          HahnSeries.C C4 =
        (HahnSeries.single T.delta (1 : k)) ^ 2 * HahnSeries.C C4
    congr 4
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
  have hfactor : c4row = H ^ 2 * (K + H * E) := by
    dsimp only [c4row]
    rw [fullN5_c4_specialize, hload]
    rw [hchart0, hchart1, hchart2,
      D.regular3_eq_two_cubicV, D.regular4_eq_two_cubicU]
    rw [hzero]
    dsimp only [K, E]
    rw [← hchart0, ← hchart1, ← hchart2,
      ← D.regular3_eq_two_cubicV, ← D.regular4_eq_two_cubicU]
    ring
  have hspecialLower : (↑(5 * D.faber.scale.p) : WithTop ℚ) ≤
      c4row.1.orderTop := by
    rw [hfactor, htie]
    exact GCD369CubeHahnRegular.orderTop_monomial_pow_mul_lower
      T.delta T.hdelta 2 (K + H * E)
  have hspecialOrder : c4row.1.orderTop =
      (↑(5 * D.faber.scale.p) : WithTop ℚ) :=
    le_antisymm hspecialUpper hspecialLower
  have hdiff : full - c4row ∈
      GCD369CubeHahnRegular.higherOrderIdeal
        (5 * D.faber.scale.p)
        (mul_nonneg (by norm_num) D.faber.scale.hp.le) :=
    D.faber.fullN5_sub_c4Specialized_mem_higherOrderIdeal
      C3 C2 C1 hd hc7 hc5 hc3 hc2 hc1
  have hlt : c4row.1.orderTop < (full - c4row).1.orderTop := by
    rw [hspecialOrder]
    exact hdiff
  have hsum := HahnSeries.orderTop_add_eq_right hlt
  have hfull : full - c4row + c4row = full := by ring
  have hfullval : (full - c4row).1 + c4row.1 = full.1 :=
    congrArg Subtype.val hfull
  rw [hfullval] at hsum
  change full.1.orderTop = (↑(5 * D.faber.scale.p) : WithTop ℚ)
  exact hsum.trans hspecialOrder

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubePolynomialSource

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- A nonzero `c4` load cannot tie the first transverse normal at a
constant-core infinity pole.  The tied packet gives exact terminal order
`5p`, and the weight-five degree landing excludes that order. -/
theorem infinity_c4_eq_zero_at_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hd0 : S.faberConstantParameters.d = 0)
    (hc70 : S.faberConstantParameters.c7 = 0)
    (hc50 : S.faberConstantParameters.c5 = 0)
    (htie :
      5 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p =
        2 * T.delta) :
    S.faberConstantParameters.c4 = 0 := by
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
  have hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant P.c4 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree]
      using hc4raw
  have hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant P.c3 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree]
      using hc3raw
  have hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant P.c2 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree]
      using hc2raw
  have hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant P.c1 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree]
      using hc1raw
  have hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R.rho1 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree]
      using hr1raw
  have hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R.rho2 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree]
      using hr2raw
  have hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R.rho3 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree]
      using hr3raw
  have hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R.rho4 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree]
      using hr4raw
  by_contra hPc4
  have hv : D.v ≠ 0 := T.v_ne_zero_of_c4_tie
    P.c4 P.c3 P.c2 P.c1 R.rho1 R.rho2 R.rho3 R.rho4 hPc4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 htie
  have h3D : D.faber.scale.leading3 ≠ 0 := by
    rw [D.ha3]
    exact mul_ne_zero (by norm_num) hv
  have h3 :
      (S.infinityCommonCoefficientData hsdegree).faber.scale.leading3 ≠ 0 := by
    simpa only [D] using h3D
  apply hPc4
  apply S.infinity_c4_eq_zero_of_terminal_order_eq_five hsdegree h3
  intro _hload
  have hNorder := T.fullN5_orderTop_eq_five_p_of_c4_tie
    P.c4 P.c3 P.c2 P.c1 R.rho1 R.rho2 R.rho3 R.rho4 hPc4
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
      (5 * D.faber.scale.p) hNorder
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

end GCD369CubePolynomialSource

#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.c4LeadingFaberRowsAt_at_transverse
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.v_ne_zero_of_c4_tie
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.c4TerminalAt_nonzero_at_transverse
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.c4SpecializedTerminalCoeff_at_transverse
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.fullN5_orderTop_eq_five_p_of_c4_tie
#print axioms GCD369CubePolynomialSource.infinity_c4_eq_zero_at_transverse
