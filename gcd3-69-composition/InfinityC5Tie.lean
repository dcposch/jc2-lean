import InfinityC5Before
import InfinityLoadLanding

/-! # The exact weight-four/transverse tie at infinity

When `4p = 2δ`, the first `c5` load and the quadratic transverse normal
arrive at the same Hahn order.  The tied first four rows certify a nonzero
terminal coefficient for every nonzero `c5`; its exact terminal order is
then excluded by the constant-core degree landing.
-/

noncomputable section
open Polynomial

namespace GCD369CubeHahnCommonCoefficientData

/-- Coefficient of the pure `c5` load in the denominator-cleared terminal
numerator. -/
def terminalC5Coeff {R : Type*} [CommRing R]
    (_a0 a1 a2 a3 a4 : R) : R :=
  -933120 * a1 ^ 2 + 622080 * a1 * a3 * a4 +
    311040 * a2 ^ 2 * a4 + 311040 * a2 * a3 ^ 2 -
    155520 * a2 * a4 ^ 3 - 259200 * a3 ^ 2 * a4 ^ 2 +
    21168 * a4 ^ 5

/-- Isolate the pure `c5` contribution to the terminal numerator. -/
theorem fullN5_c5_specialize
    {R : Type*} [CommRing R]
    (a0 a1 a2 a3 a4 c5 : R) :
    GCD369CubeFaberFullN5 a0 a1 a2 a3 a4 0 0 c5 0 0 0 0 =
      GCD369CubeFaberFullN5 a0 a1 a2 a3 a4 0 0 0 0 0 0 0 +
        c5 * terminalC5Coeff a0 a1 a2 a3 a4 := by
  simp only [terminalC5Coeff]
  ring

/-- At the exact `c5`/transverse tie, the four source equations are the
arbitrary-`c5` row packet on the infinity residue jet. -/
theorem TransverseScale.c5LeadingFaberRowsAt_at_transverse
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : 4 * D.faber.scale.p = 2 * T.delta) :
    GCD369CubeC5LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C5 := by
  have hz := D.faber.c5NCoeff_zero C4 C3 C2 C1 R1 R2 R3 R4
    hd hc7 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4
  have hhalf : ((4 : ℚ) * D.faber.scale.p) / 2 = T.delta := by
    linarith
  have hweighted : D.faber.scale.weightedRegular 4 D.faber.c5 =
      (GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
        GCD369CubeHahnRegular.constant C5 := by
    rw [hc5, D.faber.scale.weightedRegular_constant_eq_monomial_sq
      4 (by norm_num) C5]
    apply Subtype.ext
    change
      (HahnSeries.single (((4 : ℕ) : ℚ) * D.faber.scale.p / 2) (1 : k)) ^ 2 *
          HahnSeries.C C5 =
        (HahnSeries.single T.delta (1 : k)) ^ 2 * HahnSeries.C C5
    congr 4
  rw [hweighted] at hz
  rcases hz with ⟨hz1, hz2, hz3, hz4⟩
  have heq : ((4 : ℕ) : ℚ) * D.faber.scale.p =
      ((2 : ℕ) : ℚ) * T.delta := by
    norm_num
    exact htie
  rw [heq] at hz1 hz2 hz3 hz4
  exact T.factor.c5BeforeLeadingFaberRowsAt C5 hz1 hz2 hz3 hz4

/-- A nonzero tied `c5` load forces the leading weight-two common-cubic
coordinate to be nonzero. -/
theorem TransverseScale.u_ne_zero_of_c5_tie
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hC5 : C5 ≠ 0)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : 4 * D.faber.scale.p = 2 * T.delta) :
    D.u ≠ 0 := by
  have hrows := T.c5LeadingFaberRowsAt_at_transverse
    C5 C4 C3 C2 C1 R1 R2 R3 R4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 htie
  dsimp [GCD369CubeC5LeadingFaberRowsAt] at hrows
  have hcoeff := GCD369CubeFaberC5NormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C5
  dsimp at hcoeff
  rcases hrows with ⟨hf1, _hf2, _hf3, hf4⟩
  rcases hcoeff with ⟨hc1', _hc2', _hc3', hc4'⟩
  rw [hc1'] at hf1
  rw [hc4'] at hf4
  have h1 :
      40 * C5 * D.u ^ 3 - 360 * C5 * D.v ^ 2 +
        243 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
        486 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) -
        243 * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 = 0 :=
    (mul_eq_zero.mp hf1).resolve_left (by norm_num)
  have h4 :
      40 * C5 * D.u ^ 3 * D.v - 80 * C5 * D.v ^ 3 -
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
  intro hu
  have hv : D.v ≠ 0 := D.hprojective.resolve_left (fun hne => hne hu)
  rw [hu] at h1 h4
  have hbad : C5 * D.v ^ 3 = 0 := by
    linear_combination (-1 / 480 : k) * (D.v * h1 + (3 / 2 : k) * h4)
  exact (mul_ne_zero hC5 (pow_ne_zero 3 hv)) hbad

/-- The unnormalized weight-four terminal polynomial at a tied `c5` load. -/
def c5TerminalAt {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k)
    (T : D.TransverseScale) (C5 : k) : k :=
  8 * C5 * D.u ^ 5 - 240 * C5 * D.u ^ 2 * D.v ^ 2 -
    81 * D.u ^ 3 * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
    243 * D.v ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
    486 * D.u * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
      (GCD369CubeHahnRegular.constantCoeff T.Yn) +
    162 * D.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
      (GCD369CubeHahnRegular.constantCoeff T.Zn) +
    81 * D.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 -
    486 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
      (GCD369CubeHahnRegular.constantCoeff T.Zn)

/-- The actual unnormalized terminal polynomial is nonzero whenever the
tied `c5` load is nonzero. -/
theorem TransverseScale.c5TerminalAt_nonzero_at_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hC5 : C5 ≠ 0)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : 4 * D.faber.scale.p = 2 * T.delta) :
    c5TerminalAt D T C5 ≠ 0 := by
  have hrows := T.c5LeadingFaberRowsAt_at_transverse
    C5 C4 C3 C2 C1 R1 R2 R3 R4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 htie
  dsimp [GCD369CubeC5LeadingFaberRowsAt] at hrows
  have hcoeff := GCD369CubeFaberC5NormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C5
  dsimp at hcoeff
  rcases hrows with ⟨hf1, hf2, _hf3, hf4⟩
  rcases hcoeff with ⟨hc1', hc2', _hc3', hc4'⟩
  rw [hc1'] at hf1
  rw [hc2'] at hf2
  rw [hc4'] at hf4
  have h1 :
      40 * C5 * D.u ^ 3 - 360 * C5 * D.v ^ 2 +
        243 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
        486 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) -
        243 * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 = 0 :=
    (mul_eq_zero.mp hf1).resolve_left (by norm_num)
  have h2 :
      40 * C5 * D.u ^ 2 * D.v +
        81 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
        162 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) -
        162 * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) = 0 :=
    (mul_eq_zero.mp hf2).resolve_left (by norm_num)
  have h4 :
      40 * C5 * D.u ^ 3 * D.v - 80 * C5 * D.v ^ 3 -
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
  obtain ⟨lambda, hlambda, hscale⟩ :=
    GCD369CubeExistsWeightedNormalizer 4 (by norm_num) C5 hC5
  have hnormalized := GCD369CubeC5TerminalNonzero
    (lambda ^ 4 * GCD369CubeHahnRegular.constantCoeff T.Xn)
    (lambda ^ 5 * GCD369CubeHahnRegular.constantCoeff T.Yn)
    (lambda ^ 6 * GCD369CubeHahnRegular.constantCoeff T.Zn)
    (lambda ^ 2 * D.u) (lambda ^ 3 * D.v)
    (GCD369CubeProjectiveOfWeightedScale lambda D.u D.v
      hlambda D.hprojective)
    (by
      calc
        40 * (lambda ^ 2 * D.u) ^ 3 -
            360 * (lambda ^ 3 * D.v) ^ 2 +
            243 * (lambda ^ 2 * D.u) *
              (lambda ^ 4 * GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
            486 * (lambda ^ 4 * GCD369CubeHahnRegular.constantCoeff T.Xn) *
              (lambda ^ 6 * GCD369CubeHahnRegular.constantCoeff T.Zn) -
            243 * (lambda ^ 5 *
              GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 =
          lambda ^ 10 * (40 * C5 * D.u ^ 3 - 360 * C5 * D.v ^ 2 +
            243 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
            486 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
              (GCD369CubeHahnRegular.constantCoeff T.Zn) -
            243 * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2) := by
              linear_combination
                (-(lambda ^ 6 * (40 * D.u ^ 3 - 360 * D.v ^ 2))) * hscale
        _ = 0 := by rw [h1, mul_zero])
    (by
      calc
        40 * (lambda ^ 2 * D.u) ^ 2 * (lambda ^ 3 * D.v) +
            81 * (lambda ^ 3 * D.v) *
              (lambda ^ 4 * GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
            162 * (lambda ^ 2 * D.u) *
              (lambda ^ 4 * GCD369CubeHahnRegular.constantCoeff T.Xn) *
              (lambda ^ 5 * GCD369CubeHahnRegular.constantCoeff T.Yn) -
            162 * (lambda ^ 5 * GCD369CubeHahnRegular.constantCoeff T.Yn) *
              (lambda ^ 6 * GCD369CubeHahnRegular.constantCoeff T.Zn) =
          lambda ^ 11 * (40 * C5 * D.u ^ 2 * D.v +
            81 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
            162 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
              (GCD369CubeHahnRegular.constantCoeff T.Yn) -
            162 * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
              (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
              linear_combination
                (-(lambda ^ 7 * (40 * D.u ^ 2 * D.v))) * hscale
        _ = 0 := by rw [h2, mul_zero])
    (by
      calc
        40 * (lambda ^ 2 * D.u) ^ 3 * (lambda ^ 3 * D.v) -
            80 * (lambda ^ 3 * D.v) ^ 3 -
            243 * (lambda ^ 2 * D.u) * (lambda ^ 3 * D.v) *
              (lambda ^ 4 * GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
            162 * (lambda ^ 2 * D.u) ^ 2 *
              (lambda ^ 4 * GCD369CubeHahnRegular.constantCoeff T.Xn) *
              (lambda ^ 5 * GCD369CubeHahnRegular.constantCoeff T.Yn) +
            324 * (lambda ^ 3 * D.v) *
              (lambda ^ 4 * GCD369CubeHahnRegular.constantCoeff T.Xn) *
              (lambda ^ 6 * GCD369CubeHahnRegular.constantCoeff T.Zn) +
            162 * (lambda ^ 3 * D.v) *
              (lambda ^ 5 * GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 +
            162 * (lambda ^ 2 * D.u) *
              (lambda ^ 5 * GCD369CubeHahnRegular.constantCoeff T.Yn) *
              (lambda ^ 6 * GCD369CubeHahnRegular.constantCoeff T.Zn) =
          lambda ^ 13 * (40 * C5 * D.u ^ 3 * D.v -
            80 * C5 * D.v ^ 3 - 243 * D.u * D.v *
              (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
            162 * D.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
              (GCD369CubeHahnRegular.constantCoeff T.Yn) +
            324 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
              (GCD369CubeHahnRegular.constantCoeff T.Zn) +
            162 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 +
            162 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
              (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
              linear_combination
                (-(lambda ^ 9 * (40 * D.u ^ 3 * D.v -
                  80 * D.v ^ 3))) * hscale
        _ = 0 := by rw [h4, mul_zero])
  intro hzero
  apply hnormalized
  calc
    _ = lambda ^ 14 * c5TerminalAt D T C5 := by
      dsimp only [c5TerminalAt]
      linear_combination
        (-(lambda ^ 10 * (8 * D.u ^ 5 -
          240 * D.u ^ 2 * D.v ^ 2))) * hscale
    _ = 0 := by rw [hzero, mul_zero]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- At the exact tie, the pure-`c5` terminal numerator has coefficient
`6912` times the unnormalized terminal polynomial. -/
theorem TransverseScale.c5SpecializedTerminalCoeff_at_transverse
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C5 : k)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (htie : 4 * D.faber.scale.p = 2 * T.delta) :
    (GCD369CubeFaberFullN5
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4 0 0
      (D.faber.scale.weightedRegular 4 D.faber.c5)
      0 0 0 0).1.coeff (4 * D.faber.scale.p) =
      6912 * c5TerminalAt D T C5 := by
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let P : GCD369CubeHahnRegular k := terminalC5Coeff
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4
  let K : GCD369CubeHahnRegular k :=
    559872 * GCD369CubeNormalRow5
      T.Xn T.Yn T.Zn D.cubicU D.cubicV +
      GCD369CubeHahnRegular.constant C5 * P
  let E : GCD369CubeHahnRegular k :=
    839808 * GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU
  have hhalf : ((4 : ℚ) * D.faber.scale.p) / 2 = T.delta := by
    linarith
  have hload : D.faber.scale.weightedRegular 4 D.faber.c5 =
      H ^ 2 * GCD369CubeHahnRegular.constant C5 := by
    rw [hc5, D.faber.scale.weightedRegular_constant_eq_monomial_sq
      4 (by norm_num) C5]
    apply Subtype.ext
    change
      (HahnSeries.single (((4 : ℕ) : ℚ) * D.faber.scale.p / 2) (1 : k)) ^ 2 *
          HahnSeries.C C5 =
        (HahnSeries.single T.delta (1 : k)) ^ 2 * HahnSeries.C C5
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
        D.faber.scale.regular4 0 0
        (D.faber.scale.weightedRegular 4 D.faber.c5)
        0 0 0 0 = H ^ 2 * K + H ^ 3 * E := by
    rw [fullN5_c5_specialize, hload]
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
      D.faber.scale.regular4 0 0
      (D.faber.scale.weightedRegular 4 D.faber.c5)
      0 0 0 0).1.coeff (2 * T.delta) =
      (H ^ 2 * K).1.coeff (2 * T.delta) +
        (H ^ 3 * E).1.coeff (2 * T.delta) at hc
  rw [hmain, hhigh, add_zero] at hc
  rw [← htie] at hc
  rw [hc]
  dsimp only [K, P, terminalC5Coeff, c5TerminalAt]
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

/-- With `d=c7=0`, every load strictly after `c5` is invisible through
the weight-four terminal cutoff. -/
theorem fullN5_sub_c5Specialized_mem_higherOrderIdeal
    {k : Type*} [Field k] [CharZero k]
    (F : GCD369CubeHahnFaberPoleData k)
    (C4 C3 C2 C1 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
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
      F.scale.regular3 F.scale.regular4 0 0
      (F.scale.weightedRegular 4 F.c5) 0 0 0 0 ∈
        GCD369CubeHahnRegular.higherOrderIdeal
          (4 * F.scale.p) (mul_nonneg (by norm_num) F.scale.hp.le) := by
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal
      (4 * F.scale.p) (mul_nonneg (by norm_num) F.scale.hp.le)
  let q := Ideal.Quotient.mk I
  have hweight (w : ℕ) (hw : 4 < w) :
      4 * F.scale.p < (w : ℚ) * F.scale.p := by
    exact mul_lt_mul_of_pos_right
      (show (4 : ℚ) < (w : ℚ) by exact_mod_cast hw) F.scale.hp
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
  have hkill (w : ℕ) (hw : 4 < w) (c : k)
      (x : GCD369CubeHahnRegular k)
      (hx : x = GCD369CubeHahnRegular.constant c) :
      q (F.scale.weightedRegular w x) = 0 := by
    rw [hx, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale w c (mul_nonneg (by norm_num) F.scale.hp.le) (hweight w hw)
  have hc4q := hkill 5 (by norm_num) C4 F.c4 hc4
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
  let c5row : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4 0 0
    (F.scale.weightedRegular 4 F.c5) 0 0 0 0
  have hq : q full = q c5row := by
    dsimp only [full, c5row]
    rw [GCD369CubeFaberFullN5_map, GCD369CubeFaberFullN5_map,
      hdq, hc7q, hc4q, hc3q, hc2q, hc1q]
    simp
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [map_sub, hq, sub_self]

end GCD369CubeHahnFaberPoleData

namespace GCD369CubeHahnCommonCoefficientData

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- A nonzero tied `c5` load makes the complete terminal numerator have
exact order `4p`; all later loads are strictly higher. -/
theorem TransverseScale.fullN5_orderTop_eq_four_p_of_c5_tie
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hC5 : C5 ≠ 0)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : 4 * D.faber.scale.p = 2 * T.delta) :
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
        (↑(4 * D.faber.scale.p) : WithTop ℚ) := by
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
  let c5row : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4 0 0
    (D.faber.scale.weightedRegular 4 D.faber.c5) 0 0 0 0
  have hterminal := T.c5TerminalAt_nonzero_at_transverse
    C5 C4 C3 C2 C1 R1 R2 R3 R4 hC5
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 htie
  have hspecialCoeff := T.c5SpecializedTerminalCoeff_at_transverse
    C5 hc5 htie
  have hspecialCoeffNe :
      c5row.1.coeff (4 * D.faber.scale.p) ≠ 0 := by
    change
      (GCD369CubeFaberFullN5
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 0 0
        (D.faber.scale.weightedRegular 4 D.faber.c5)
        0 0 0 0).1.coeff (4 * D.faber.scale.p) ≠ 0
    rw [hspecialCoeff]
    exact mul_ne_zero (by norm_num) hterminal
  have hspecialUpper : c5row.1.orderTop ≤
      (↑(4 * D.faber.scale.p) : WithTop ℚ) :=
    HahnSeries.orderTop_le_of_coeff_ne_zero hspecialCoeffNe
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let P : GCD369CubeHahnRegular k := terminalC5Coeff
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4
  let K : GCD369CubeHahnRegular k :=
    559872 * GCD369CubeNormalRow5
      T.Xn T.Yn T.Zn D.cubicU D.cubicV +
      GCD369CubeHahnRegular.constant C5 * P
  let E : GCD369CubeHahnRegular k :=
    839808 * GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU
  have hhalf : ((4 : ℚ) * D.faber.scale.p) / 2 = T.delta := by
    linarith
  have hload : D.faber.scale.weightedRegular 4 D.faber.c5 =
      H ^ 2 * GCD369CubeHahnRegular.constant C5 := by
    rw [hc5, D.faber.scale.weightedRegular_constant_eq_monomial_sq
      4 (by norm_num) C5]
    apply Subtype.ext
    change
      (HahnSeries.single (((4 : ℕ) : ℚ) * D.faber.scale.p / 2) (1 : k)) ^ 2 *
          HahnSeries.C C5 =
        (HahnSeries.single T.delta (1 : k)) ^ 2 * HahnSeries.C C5
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
  have hfactor : c5row = H ^ 2 * (K + H * E) := by
    dsimp only [c5row]
    rw [fullN5_c5_specialize, hload]
    rw [hchart0, hchart1, hchart2,
      D.regular3_eq_two_cubicV, D.regular4_eq_two_cubicU]
    rw [hzero]
    dsimp only [K, E]
    rw [← hchart0, ← hchart1, ← hchart2,
      ← D.regular3_eq_two_cubicV, ← D.regular4_eq_two_cubicU]
    ring
  have hspecialLower : (↑(4 * D.faber.scale.p) : WithTop ℚ) ≤
      c5row.1.orderTop := by
    rw [hfactor, htie]
    exact GCD369CubeHahnRegular.orderTop_monomial_pow_mul_lower
      T.delta T.hdelta 2 (K + H * E)
  have hspecialOrder : c5row.1.orderTop =
      (↑(4 * D.faber.scale.p) : WithTop ℚ) :=
    le_antisymm hspecialUpper hspecialLower
  have hdiff : full - c5row ∈
      GCD369CubeHahnRegular.higherOrderIdeal
        (4 * D.faber.scale.p)
        (mul_nonneg (by norm_num) D.faber.scale.hp.le) :=
    D.faber.fullN5_sub_c5Specialized_mem_higherOrderIdeal
      C4 C3 C2 C1 hd hc7 hc4 hc3 hc2 hc1
  have hlt : c5row.1.orderTop < (full - c5row).1.orderTop := by
    rw [hspecialOrder]
    exact hdiff
  have hsum := HahnSeries.orderTop_add_eq_right hlt
  have hfull : full - c5row + c5row = full := by ring
  have hfullval : (full - c5row).1 + c5row.1 = full.1 :=
    congrArg Subtype.val hfull
  rw [hfullval] at hsum
  change full.1.orderTop = (↑(4 * D.faber.scale.p) : WithTop ℚ)
  exact hsum.trans hspecialOrder

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubePolynomialSource

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- A nonzero `c5` load cannot tie the first transverse normal at a
constant-core infinity pole.  The tied packet gives exact terminal order
`4p`, and the weight-four degree landing excludes that order. -/
theorem infinity_c5_eq_zero_at_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hd0 : S.faberConstantParameters.d = 0)
    (hc70 : S.faberConstantParameters.c7 = 0)
    (htie :
      4 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p =
        2 * T.delta) :
    S.faberConstantParameters.c5 = 0 := by
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
  have hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant P.c5 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree]
      using hc5raw
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
  by_contra hPc5
  have hu : D.u ≠ 0 := T.u_ne_zero_of_c5_tie
    P.c5 P.c4 P.c3 P.c2 P.c1 R.rho1 R.rho2 R.rho3 R.rho4 hPc5
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 htie
  have h4D : D.faber.scale.leading4 ≠ 0 := by
    rw [D.ha4]
    exact mul_ne_zero (by norm_num) hu
  have h4 :
      (S.infinityCommonCoefficientData hsdegree).faber.scale.leading4 ≠ 0 := by
    simpa only [D] using h4D
  apply hPc5
  apply S.infinity_c5_eq_zero_of_terminal_order_eq_four hsdegree h4
  intro _hload
  have hNorder := T.fullN5_orderTop_eq_four_p_of_c5_tie
    P.c5 P.c4 P.c3 P.c2 P.c1 R.rho1 R.rho2 R.rho3 R.rho4 hPc5
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
      (4 * D.faber.scale.p) hNorder
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
  GCD369CubeHahnCommonCoefficientData.TransverseScale.c5LeadingFaberRowsAt_at_transverse
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.u_ne_zero_of_c5_tie
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.c5TerminalAt_nonzero_at_transverse
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.c5SpecializedTerminalCoeff_at_transverse
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.fullN5_orderTop_eq_four_p_of_c5_tie
#print axioms GCD369CubePolynomialSource.infinity_c5_eq_zero_at_transverse
