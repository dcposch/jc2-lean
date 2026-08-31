import InfinityC4Tie
import FiniteC2Extraction
import FiniteTargetNormalizedParameters

/-! # The exact weight-seven/transverse tie at infinity

When `7p = 2δ`, the first `c2` load and the quadratic transverse normal
arrive at the same Hahn order.  The tied first four rows certify a nonzero
terminal coefficient for every nonzero `c2`; its exact terminal order is
then excluded by the constant-core degree landing.
-/

noncomputable section
open Polynomial

namespace GCD369CubeHahnCommonCoefficientData

theorem TransverseFactor.c2TieN1Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C2 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC2N1
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C2)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -2592 * (-16 * C2 * D.v +
        9 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
        18 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) -
        9 * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    20736 * D.faber.scale.regular3
  change
    (729 * GCD369CubeFaberN1
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C2 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN1Coeff]
  have hload :
      ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
        GCD369CubeHahnRegular.constant C2 * P).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) =
        C2 * GCD369CubeHahnRegular.constantCoeff P := by
    exact GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C2 P
  rw [hload]
  dsimp only [P]
  simp only [map_mul, map_ofNat]
  change _ + C2 * (20736 * D.faber.scale.leading3) = _
  rw [D.ha3]
  dsimp only [GCD369CubeNormalRow1]
  ring

theorem TransverseFactor.c2TieN2Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C2 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC2N2
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C2)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -2592 * (8 * C2 * D.u ^ 2 +
        27 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
        54 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) -
        54 * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    62208 * D.faber.scale.regular2 -
      20736 * D.faber.scale.regular4 ^ 2
  change
    (2187 * GCD369CubeFaberN2
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C2 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN2Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C2 P]
  dsimp only [P]
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  change _ + C2 *
    (62208 * D.faber.scale.leading2 -
      20736 * D.faber.scale.leading4 ^ 2) = _
  rw [D.ha2, D.ha4]
  dsimp only [GCD369CubeNormalRow2]
  ring

theorem TransverseFactor.c2TieN3Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C2 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC2N3
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C2)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      31104 * GCD369CubeNormalRow3
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    82944 * D.faber.scale.regular1 -
      41472 * D.faber.scale.regular3 *
        D.faber.scale.regular4
  have hzero :
      (243 * GCD369CubeFaberN3
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) =
        31104 * GCD369CubeNormalRow3
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v := by
    calc
      _ = (243 : k) *
          (GCD369CubeFaberN3
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4).1.coeff
              (((2 : ℕ) : ℚ) * T.delta) :=
        GCD369CubeHahnRegular.coeff_nat_mul 243 _ _
      _ = _ := by rw [T.zeroHighN3Coeff]; ring
  change
    (243 * GCD369CubeFaberN3
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C2 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [hzero,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C2 P]
  dsimp only [P]
  simp only [map_sub, map_mul, map_ofNat]
  change _ + C2 *
    (82944 * D.faber.scale.leading1 -
      41472 * D.faber.scale.leading3 *
        D.faber.scale.leading4) = _
  rw [D.ha1, D.ha3, D.ha4]
  ring

theorem TransverseFactor.c2TieN4Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C2 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC2N4
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C2)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -2592 * (16 * C2 * D.u ^ 3 - 72 * C2 * D.v ^ 2 -
        243 * D.u * D.v *
          (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
        162 * D.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) +
        324 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) +
        162 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 +
        162 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    559872 * D.faber.scale.regular0 -
      186624 * D.faber.scale.regular2 *
        D.faber.scale.regular4 -
      93312 * D.faber.scale.regular3 ^ 2 +
      41472 * D.faber.scale.regular4 ^ 3
  change
    (6561 * GCD369CubeFaberN4
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C2 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN4Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C2 P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change _ + C2 *
    (559872 * D.faber.scale.leading0 -
      186624 * D.faber.scale.leading2 *
        D.faber.scale.leading4 -
      93312 * D.faber.scale.leading3 ^ 2 +
      41472 * D.faber.scale.leading4 ^ 3) = _
  rw [D.ha0, D.ha2, D.ha3, D.ha4]
  dsimp only [GCD369CubeNormalRow4]
  ring

/-- Vanishing of the four literal quadratic Hahn coefficients is exactly
the source-facing arbitrary-`c2` Faber row packet. -/
theorem TransverseFactor.c2TieLeadingFaberRowsAt
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C2 : k)
    (h1 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC2N1
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C2)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h2 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC2N2
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C2)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h3 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC2N3
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C2)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h4 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC2N4
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C2)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0) :
    GCD369CubeC2LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C2 := by
  dsimp [GCD369CubeC2LeadingFaberRowsAt]
  have hc := GCD369CubeFaberC2NormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C2
  dsimp only at hc
  rcases hc with ⟨hc1, hc2, hc3, hc4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc1, ← T.c2TieN1Coeff C2]
    exact h1
  · rw [hc2, ← T.c2TieN2Coeff C2]
    exact h2
  · rw [hc3, ← T.c2TieN3Coeff C2]
    exact h3
  · rw [hc4, ← T.c2TieN4Coeff C2]
    exact h4

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubeHahnCommonCoefficientData

/-- Coefficient of the pure `c2` load in the denominator-cleared terminal
numerator. -/
def terminalC2Coeff {R : Type*} [CommRing R]
    (_a0 a1 a2 a3 a4 : R) : R :=
  -746496 * a1 * a4 - 746496 * a2 * a3 +
    435456 * a3 * a4 ^ 2

/-- Isolate the pure `c2` contribution to the terminal numerator. -/
theorem fullN5_c2_specialize
    {R : Type*} [CommRing R]
    (a0 a1 a2 a3 a4 c2 : R) :
    GCD369CubeFaberFullN5 a0 a1 a2 a3 a4 0 0 0 0 0 c2 0 =
      GCD369CubeFaberFullN5 a0 a1 a2 a3 a4 0 0 0 0 0 0 0 +
        c2 * terminalC2Coeff a0 a1 a2 a3 a4 := by
  simp only [terminalC2Coeff]
  ring

/-- At the exact `c2`/transverse tie, the four source equations are the
arbitrary-`c2` row packet on the infinity residue jet. -/
theorem TransverseScale.c2LeadingFaberRowsAt_at_transverse
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C2 C1 R1 R2 R3 R4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : 7 * D.faber.scale.p = 2 * T.delta) :
    GCD369CubeC2LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C2 := by
  have hz := D.faber.c2NCoeff_zero C1 R1 R2 R3 R4
    hd hc7 hc5 hc4 hc3 hc1 hr1 hr2 hr3 hr4
  have hhalf : ((7 : ℚ) * D.faber.scale.p) / 2 = T.delta := by
    linarith
  have hweighted : D.faber.scale.weightedRegular 7 D.faber.c2 =
      (GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
        GCD369CubeHahnRegular.constant C2 := by
    rw [hc2, D.faber.scale.weightedRegular_constant_eq_monomial_sq
      7 (by norm_num) C2]
    apply Subtype.ext
    change
      (HahnSeries.single (((7 : ℕ) : ℚ) * D.faber.scale.p / 2) (1 : k)) ^ 2 *
          HahnSeries.C C2 =
        (HahnSeries.single T.delta (1 : k)) ^ 2 * HahnSeries.C C2
    congr 4
  rw [hweighted] at hz
  rcases hz with ⟨hz1, hz2, hz3, hz4⟩
  have heq : ((7 : ℕ) : ℚ) * D.faber.scale.p =
      ((2 : ℕ) : ℚ) * T.delta := by
    norm_num
    exact htie
  rw [heq] at hz1 hz2 hz3 hz4
  exact T.factor.c2TieLeadingFaberRowsAt C2 hz1 hz2 hz3 hz4

/-- A nonzero tied `c2` load forces the leading weight-two common-cubic
coordinate to be nonzero. -/
theorem TransverseScale.u_ne_zero_of_c2_tie
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C2 C1 R1 R2 R3 R4 : k)
    (hC2 : C2 ≠ 0)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : 7 * D.faber.scale.p = 2 * T.delta) :
    D.u ≠ 0 := by
  have hrows := T.c2LeadingFaberRowsAt_at_transverse
    C2 C1 R1 R2 R3 R4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 htie
  dsimp [GCD369CubeC2LeadingFaberRowsAt] at hrows
  have hcoeff := GCD369CubeFaberC2NormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C2
  dsimp at hcoeff
  rcases hrows with ⟨hf1, _hf2, _hf3, hf4⟩
  rcases hcoeff with ⟨hc1', _hc2', _hc3', hc4'⟩
  rw [hc1'] at hf1
  rw [hc4'] at hf4
  have h1 :
      -16 * C2 * D.v +
        9 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
        18 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) -
        9 * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 = 0 :=
    (mul_eq_zero.mp hf1).resolve_left (by norm_num)
  have h4 :
      16 * C2 * D.u ^ 3 - 72 * C2 * D.v ^ 2 -
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
  have hbad : C2 * D.v ^ 2 = 0 := by
    linear_combination (-1 / 20 : k) * (D.v * h1) +
      (-1 / 360 : k) * h4
  exact (mul_ne_zero hC2 (pow_ne_zero 2 hv)) hbad

/-- The unnormalized weight-seven terminal polynomial at a tied `c2` load. -/
def c2TerminalAt {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k)
    (T : D.TransverseScale) (C2 : k) : k :=
  16 * C2 * D.u ^ 2 * D.v +
    9 * D.u ^ 3 * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
    27 * D.v ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
    54 * D.u * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
      (GCD369CubeHahnRegular.constantCoeff T.Yn) -
    18 * D.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
      (GCD369CubeHahnRegular.constantCoeff T.Zn) -
    9 * D.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 +
    54 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
      (GCD369CubeHahnRegular.constantCoeff T.Zn)

/-- The actual unnormalized terminal polynomial is nonzero whenever the
tied `c2` load is nonzero. -/
theorem TransverseScale.c2TerminalAt_nonzero_at_transverse
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C2 C1 R1 R2 R3 R4 : k)
    (hC2 : C2 ≠ 0)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : 7 * D.faber.scale.p = 2 * T.delta) :
    c2TerminalAt D T C2 ≠ 0 := by
  have hrows := T.c2LeadingFaberRowsAt_at_transverse
    C2 C1 R1 R2 R3 R4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 htie
  have hcoeff := GCD369CubeFaberC2NormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C2
  dsimp at hcoeff
  rcases hrows with ⟨hf1, hf2, _hf3, hf4⟩
  rcases hcoeff with ⟨hc1', hc2', _hc3', hc4'⟩
  rw [hc1'] at hf1
  rw [hc2'] at hf2
  rw [hc4'] at hf4
  have h1 :
      -16 * C2 * D.v +
        9 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
        18 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) -
        9 * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 = 0 :=
    (mul_eq_zero.mp hf1).resolve_left (by norm_num)
  have h2 :
      8 * C2 * D.u ^ 2 +
        27 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
        54 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) -
        54 * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) = 0 :=
    (mul_eq_zero.mp hf2).resolve_left (by norm_num)
  have h4 :
      16 * C2 * D.u ^ 3 - 72 * C2 * D.v ^ 2 -
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
  dsimp only [c2TerminalAt] at hterminal
  by_cases hu : D.u = 0
  · have hv : D.v ≠ 0 := D.hprojective.resolve_left (fun h => h hu)
    rw [hu] at h1 h4
    have hbad : C2 * D.v ^ 2 = 0 := by
      linear_combination (-1 / 20 : k) * (D.v * h1) +
        (-1 / 360 : k) * h4
    exact (mul_ne_zero hC2 (pow_ne_zero 2 hv)) hbad
  · have hbad : C2 * D.u ^ 5 = 0 := by
      linear_combination
        (9 / 40 * D.u ^ 2 * D.v) * h1 +
        (3 / 40 * D.u ^ 3 + 9 / 40 * D.v ^ 2) * h2 +
        (1 / 40 * D.u ^ 2) * h4 +
        (9 / 40 * D.v) * hterminal
    exact (mul_ne_zero hC2 (pow_ne_zero 5 hu)) hbad

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- At the exact tie, the pure-`c2` terminal numerator has coefficient
`-62208` times the unnormalized terminal polynomial. -/
theorem TransverseScale.c2SpecializedTerminalCoeff_at_transverse
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C2 : k)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (htie : 7 * D.faber.scale.p = 2 * T.delta) :
    (GCD369CubeFaberFullN5
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4 0 0 0 0 0
      (D.faber.scale.weightedRegular 7 D.faber.c2)
      0).1.coeff (7 * D.faber.scale.p) =
      -62208 * c2TerminalAt D T C2 := by
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let P : GCD369CubeHahnRegular k := terminalC2Coeff
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4
  let K : GCD369CubeHahnRegular k :=
    559872 * GCD369CubeNormalRow5
      T.Xn T.Yn T.Zn D.cubicU D.cubicV +
      GCD369CubeHahnRegular.constant C2 * P
  let E : GCD369CubeHahnRegular k :=
    839808 * GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU
  have hhalf : ((7 : ℚ) * D.faber.scale.p) / 2 = T.delta := by
    linarith
  have hload : D.faber.scale.weightedRegular 7 D.faber.c2 =
      H ^ 2 * GCD369CubeHahnRegular.constant C2 := by
    rw [hc2, D.faber.scale.weightedRegular_constant_eq_monomial_sq
      7 (by norm_num) C2]
    apply Subtype.ext
    change
      (HahnSeries.single (((7 : ℕ) : ℚ) * D.faber.scale.p / 2) (1 : k)) ^ 2 *
          HahnSeries.C C2 =
        (HahnSeries.single T.delta (1 : k)) ^ 2 * HahnSeries.C C2
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
        D.faber.scale.regular4 0 0 0 0 0
        (D.faber.scale.weightedRegular 7 D.faber.c2)
        0 = H ^ 2 * K + H ^ 3 * E := by
    rw [fullN5_c2_specialize, hload]
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
      D.faber.scale.regular4 0 0 0 0 0
      (D.faber.scale.weightedRegular 7 D.faber.c2)
      0).1.coeff (2 * T.delta) =
      (H ^ 2 * K).1.coeff (2 * T.delta) +
        (H ^ 3 * E).1.coeff (2 * T.delta) at hc
  rw [hmain, hhigh, add_zero] at hc
  rw [← htie] at hc
  rw [hc]
  dsimp only [K, P, terminalC2Coeff, c2TerminalAt]
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

/-! With `d=c7=c5=c4=c3=0`, the only terminal load at weight seven is
the specialized `c2` term; the later `c1` term is strictly higher. -/
theorem fullN5_sub_c2Specialized_mem_higherOrderIdeal
    {k : Type*} [Field k] [CharZero k]
    (F : GCD369CubeHahnFaberPoleData k)
    (C1 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant 0)
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
      F.scale.regular3 F.scale.regular4 0 0 0 0 0
      (F.scale.weightedRegular 7 F.c2) 0 ∈
        GCD369CubeHahnRegular.higherOrderIdeal
          (7 * F.scale.p) (mul_nonneg (by norm_num) F.scale.hp.le) := by
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal
      (7 * F.scale.p) (mul_nonneg (by norm_num) F.scale.hp.le)
  let q := Ideal.Quotient.mk I
  have hweight : 7 * F.scale.p < (8 : ℚ) * F.scale.p := by
    exact mul_lt_mul_of_pos_right (by norm_num) F.scale.hp
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
  have hc4q : q (F.scale.weightedRegular 5 F.c4) = 0 := by
    rw [hzeroWeighted 5 F.c4 hc4, map_zero]
  have hc3q : q (F.scale.weightedRegular 6 F.c3) = 0 := by
    rw [hzeroWeighted 6 F.c3 hc3, map_zero]
  have hc1q : q (F.scale.weightedRegular 8 F.c1) = 0 := by
    rw [hc1, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 8 C1 (mul_nonneg (by norm_num) F.scale.hp.le) hweight
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
  let c2row : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4 0 0 0 0 0
    (F.scale.weightedRegular 7 F.c2) 0
  have hq : q full = q c2row := by
    dsimp only [full, c2row]
    rw [GCD369CubeFaberFullN5_map, GCD369CubeFaberFullN5_map,
      hdq, hc7q, hc5q, hc4q, hc3q, hc1q]
    simp
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [map_sub, hq, sub_self]

end GCD369CubeHahnFaberPoleData

namespace GCD369CubeHahnCommonCoefficientData

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- A nonzero tied `c2` load makes the complete terminal numerator have
exact order `7p`; all later loads are strictly higher. -/
theorem TransverseScale.fullN5_orderTop_eq_seven_p_of_c2_tie
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C2 C1 R1 R2 R3 R4 : k)
    (hC2 : C2 ≠ 0)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : 7 * D.faber.scale.p = 2 * T.delta) :
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
        (↑(7 * D.faber.scale.p) : WithTop ℚ) := by
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
  let c2row : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4 0 0 0 0 0
    (D.faber.scale.weightedRegular 7 D.faber.c2) 0
  have hterminal := T.c2TerminalAt_nonzero_at_transverse
    C2 C1 R1 R2 R3 R4 hC2
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 htie
  have hspecialCoeff := T.c2SpecializedTerminalCoeff_at_transverse
    C2 hc2 htie
  have hspecialCoeffNe :
      c2row.1.coeff (7 * D.faber.scale.p) ≠ 0 := by
    change
      (GCD369CubeFaberFullN5
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 0 0 0 0 0
        (D.faber.scale.weightedRegular 7 D.faber.c2)
        0).1.coeff (7 * D.faber.scale.p) ≠ 0
    rw [hspecialCoeff]
    exact mul_ne_zero (by norm_num) hterminal
  have hspecialUpper : c2row.1.orderTop ≤
      (↑(7 * D.faber.scale.p) : WithTop ℚ) :=
    HahnSeries.orderTop_le_of_coeff_ne_zero hspecialCoeffNe
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let P : GCD369CubeHahnRegular k := terminalC2Coeff
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4
  let K : GCD369CubeHahnRegular k :=
    559872 * GCD369CubeNormalRow5
      T.Xn T.Yn T.Zn D.cubicU D.cubicV +
      GCD369CubeHahnRegular.constant C2 * P
  let E : GCD369CubeHahnRegular k :=
    839808 * GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU
  have hhalf : ((7 : ℚ) * D.faber.scale.p) / 2 = T.delta := by
    linarith
  have hload : D.faber.scale.weightedRegular 7 D.faber.c2 =
      H ^ 2 * GCD369CubeHahnRegular.constant C2 := by
    rw [hc2, D.faber.scale.weightedRegular_constant_eq_monomial_sq
      7 (by norm_num) C2]
    apply Subtype.ext
    change
      (HahnSeries.single (((7 : ℕ) : ℚ) * D.faber.scale.p / 2) (1 : k)) ^ 2 *
          HahnSeries.C C2 =
        (HahnSeries.single T.delta (1 : k)) ^ 2 * HahnSeries.C C2
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
  have hfactor : c2row = H ^ 2 * (K + H * E) := by
    dsimp only [c2row]
    rw [fullN5_c2_specialize, hload]
    rw [hchart0, hchart1, hchart2,
      D.regular3_eq_two_cubicV, D.regular4_eq_two_cubicU]
    rw [hzero]
    dsimp only [K, E]
    rw [← hchart0, ← hchart1, ← hchart2,
      ← D.regular3_eq_two_cubicV, ← D.regular4_eq_two_cubicU]
    ring
  have hspecialLower : (↑(7 * D.faber.scale.p) : WithTop ℚ) ≤
      c2row.1.orderTop := by
    rw [hfactor, htie]
    exact GCD369CubeHahnRegular.orderTop_monomial_pow_mul_lower
      T.delta T.hdelta 2 (K + H * E)
  have hspecialOrder : c2row.1.orderTop =
      (↑(7 * D.faber.scale.p) : WithTop ℚ) :=
    le_antisymm hspecialUpper hspecialLower
  have hdiff : full - c2row ∈
      GCD369CubeHahnRegular.higherOrderIdeal
        (7 * D.faber.scale.p)
        (mul_nonneg (by norm_num) D.faber.scale.hp.le) :=
    D.faber.fullN5_sub_c2Specialized_mem_higherOrderIdeal
      C1 hd hc7 hc5 hc4 hc3 hc1
  have hlt : c2row.1.orderTop < (full - c2row).1.orderTop := by
    rw [hspecialOrder]
    exact hdiff
  have hsum := HahnSeries.orderTop_add_eq_right hlt
  have hfull : full - c2row + c2row = full := by ring
  have hfullval : (full - c2row).1 + c2row.1 = full.1 :=
    congrArg Subtype.val hfull
  rw [hfullval] at hsum
  change full.1.orderTop = (↑(7 * D.faber.scale.p) : WithTop ℚ)
  exact hsum.trans hspecialOrder

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubePolynomialSource

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- A nonzero `c2` load cannot tie the first transverse normal in the
canonical `c3=0` gauge.  The tied packet gives exact terminal order `7p`,
and the weight-seven degree landing excludes that order. -/
theorem infinity_c2_eq_zero_at_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hd0 : S.faberConstantParameters.d = 0)
    (hc70 : S.faberConstantParameters.c7 = 0)
    (hc50 : S.faberConstantParameters.c5 = 0)
    (hc40 : S.faberConstantParameters.c4 = 0)
    (hc30 : S.faberConstantParameters.c3 = 0)
    (htie :
      7 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p =
        2 * T.delta) :
    S.faberConstantParameters.c2 = 0 := by
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
  by_contra hPc2
  have hu : D.u ≠ 0 := T.u_ne_zero_of_c2_tie
    P.c2 P.c1 R.rho1 R.rho2 R.rho3 R.rho4 hPc2
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 htie
  have h4D : D.faber.scale.leading4 ≠ 0 := by
    rw [D.ha4]
    exact mul_ne_zero (by norm_num) hu
  have h4 :
      (S.infinityCommonCoefficientData hsdegree).faber.scale.leading4 ≠ 0 := by
    simpa only [D] using h4D
  apply hPc2
  apply S.infinity_c2_eq_zero_of_terminal_order_eq_seven hsdegree h4
  intro _hload
  have hNorder := T.fullN5_orderTop_eq_seven_p_of_c2_tie
    P.c2 P.c1 R.rho1 R.rho2 R.rho3 R.rho4 hPc2
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
      (7 * D.faber.scale.p) hNorder
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

/-- Target-normalized source wrapper: canonical parameter uniqueness supplies
`d=c3=0`, so only the four genuine earlier load vanishings are assumed. -/
theorem targetNormalized_infinity_c2_eq_zero_at_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (hd0 : S.faberConstantParameters.d = 0)
    (T : let U := S.targetNormalizedSource
      (U.infinityCommonCoefficientData (by
        simpa [U, targetNormalizedSource] using hsdegree)).TransverseScale)
    (hc70 : S.targetNormalizedSource.faberConstantParameters.c7 = 0)
    (hc50 : S.targetNormalizedSource.faberConstantParameters.c5 = 0)
    (hc40 : S.targetNormalizedSource.faberConstantParameters.c4 = 0)
    (htie : let U := S.targetNormalizedSource
      let hsdegreeU : U.s.natDegree = 0 := by
        simpa [U, targetNormalizedSource] using hsdegree
      7 * (U.infinityCommonCoefficientData hsdegreeU).faber.scale.p =
        2 * T.delta) :
    S.targetNormalizedSource.faberConstantParameters.c2 = 0 := by
  let U := S.targetNormalizedSource
  let Q := U.faberConstantParameters
  have hsdegreeU : U.s.natDegree = 0 := by
    simpa [U, targetNormalizedSource] using hsdegree
  obtain ⟨hQd, _hQc7, _hQc6, _hQc5, _hQc4, hQc3,
      _hQc2, _hQc1, _hQc0⟩ :=
    S.targetNormalizedCanonicalParameters hd0
  apply U.infinity_c2_eq_zero_at_transverse hsdegreeU T
  · simpa only [Q, U] using hQd
  · simpa only [U] using hc70
  · simpa only [U] using hc50
  · simpa only [U] using hc40
  · simpa only [Q, U] using hQc3
  · exact htie

end GCD369CubePolynomialSource

#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.c2LeadingFaberRowsAt_at_transverse
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.u_ne_zero_of_c2_tie
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.c2TerminalAt_nonzero_at_transverse
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.c2SpecializedTerminalCoeff_at_transverse
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.fullN5_orderTop_eq_seven_p_of_c2_tie
#print axioms GCD369CubePolynomialSource.infinity_c2_eq_zero_at_transverse
#print axioms
  GCD369CubePolynomialSource.targetNormalized_infinity_c2_eq_zero_at_transverse
