import InfinityC2Tie
import FiniteC1Extraction

/-! # The exact weight-eight/transverse tie at infinity

When `8p = 2δ`, the first `c1` load and the quadratic transverse normal
arrive at the same Hahn order.  The tied first four rows force a nonzero
terminal coefficient for every nonzero `c1`; its exact terminal order is
then excluded by the constant-core degree landing.
-/

noncomputable section
open Polynomial

namespace GCD369CubeHahnCommonCoefficientData

theorem TransverseFactor.c1TieN1Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C1 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC1N1
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C1)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      2592 * (8 * C1 * D.u -
        9 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
        18 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) +
        9 * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2) := by
  dsimp only
  let P : GCD369CubeHahnRegular k := 10368 * D.faber.scale.regular4
  change
    (729 * GCD369CubeFaberN1
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C1 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN1Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C1 P]
  dsimp only [P]
  simp only [map_mul, map_ofNat]
  change _ + C1 * (10368 * D.faber.scale.leading4) = _
  rw [D.ha4]
  dsimp only [GCD369CubeNormalRow1]
  ring

theorem TransverseFactor.c1TieN2Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C1 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC1N2
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C1)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -7776 * (-8 * C1 * D.v +
        9 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
        18 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) -
        18 * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
  dsimp only
  let P : GCD369CubeHahnRegular k := 31104 * D.faber.scale.regular3
  change
    (2187 * GCD369CubeFaberN2
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C1 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN2Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C1 P]
  dsimp only [P]
  simp only [map_mul, map_ofNat]
  change _ + C1 * (31104 * D.faber.scale.leading3) = _
  rw [D.ha3]
  dsimp only [GCD369CubeNormalRow2]
  ring

theorem TransverseFactor.c1TieN3Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C1 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC1N3
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C1)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      31104 * GCD369CubeNormalRow3
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    41472 * D.faber.scale.regular2 -
      10368 * D.faber.scale.regular4 ^ 2
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
      GCD369CubeHahnRegular.constant C1 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [hzero,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C1 P]
  dsimp only [P]
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  change _ + C1 *
    (41472 * D.faber.scale.leading2 -
      10368 * D.faber.scale.leading4 ^ 2) = _
  rw [D.ha2, D.ha4]
  ring

theorem TransverseFactor.c1TieN4Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C1 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC1N4
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C1)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      23328 * (8 * C1 * D.u * D.v +
        27 * D.u * D.v *
          (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
        18 * D.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) -
        36 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) -
        18 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 -
        18 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    279936 * D.faber.scale.regular1 -
      93312 * D.faber.scale.regular3 * D.faber.scale.regular4
  change
    (6561 * GCD369CubeFaberN4
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C1 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN4Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C1 P]
  dsimp only [P]
  simp only [map_sub, map_mul, map_ofNat]
  change _ + C1 *
    (279936 * D.faber.scale.leading1 -
      93312 * D.faber.scale.leading3 * D.faber.scale.leading4) = _
  rw [D.ha1, D.ha3, D.ha4]
  dsimp only [GCD369CubeNormalRow4]
  ring

/-- Vanishing of the four tied Hahn coefficients is exactly the
arbitrary-`c1` Faber row packet. -/
theorem TransverseFactor.c1TieLeadingFaberRowsAt
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C1 : k)
    (h1 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC1N1
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C1)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h2 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC1N2
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C1)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h3 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC1N3
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C1)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h4 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC1N4
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C1)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0) :
    GCD369CubeC1LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C1 := by
  dsimp [GCD369CubeC1LeadingFaberRowsAt]
  have hc := GCD369CubeFaberC1NormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C1
  dsimp only at hc
  rcases hc with ⟨hc1, hc2, hc3, hc4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc1, ← T.c1TieN1Coeff C1]
    exact h1
  · rw [hc2, ← T.c1TieN2Coeff C1]
    exact h2
  · rw [hc3, ← T.c1TieN3Coeff C1]
    exact h3
  · rw [hc4, ← T.c1TieN4Coeff C1]
    exact h4

end GCD369CubeHahnCommonCoefficientData


namespace GCD369CubeHahnCommonCoefficientData

/-- At the exact `c1`/transverse tie, the four source equations are the
arbitrary-`c1` row packet on the infinity residue jet. -/
theorem TransverseScale.c1LeadingFaberRowsAt_at_transverse
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C1 R1 R2 R3 R4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant 0)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : 8 * D.faber.scale.p = 2 * T.delta) :
    GCD369CubeC1LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C1 := by
  have hz := D.faber.c1NCoeff_zero R1 R2 R3 R4
    hd hc7 hc5 hc4 hc3 hc2 hr1 hr2 hr3 hr4
  have hhalf : ((8 : ℚ) * D.faber.scale.p) / 2 = T.delta := by
    linarith
  have hweighted : D.faber.scale.weightedRegular 8 D.faber.c1 =
      (GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
        GCD369CubeHahnRegular.constant C1 := by
    rw [hc1, D.faber.scale.weightedRegular_constant_eq_monomial_sq
      8 (by norm_num) C1]
    apply Subtype.ext
    change
      (HahnSeries.single (((8 : ℕ) : ℚ) * D.faber.scale.p / 2) (1 : k)) ^ 2 *
          HahnSeries.C C1 =
        (HahnSeries.single T.delta (1 : k)) ^ 2 * HahnSeries.C C1
    congr 4
  rw [hweighted] at hz
  rcases hz with ⟨hz1, hz2, hz3, hz4⟩
  have heq : ((8 : ℕ) : ℚ) * D.faber.scale.p =
      ((2 : ℕ) : ℚ) * T.delta := by
    norm_num
    exact htie
  rw [heq] at hz1 hz2 hz3 hz4
  exact T.factor.c1TieLeadingFaberRowsAt C1 hz1 hz2 hz3 hz4

/-- The unnormalized weight-eight terminal polynomial at a tied `c1` load. -/
def c1TerminalAt {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k)
    (T : D.TransverseScale) (C1 : k) : k :=
  8 * C1 * D.u ^ 3 - 72 * C1 * D.v ^ 2 +
    27 * D.u ^ 3 * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
    81 * D.v ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
    162 * D.u * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
      (GCD369CubeHahnRegular.constantCoeff T.Yn) -
    54 * D.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
      (GCD369CubeHahnRegular.constantCoeff T.Zn) -
    27 * D.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 +
    162 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
      (GCD369CubeHahnRegular.constantCoeff T.Zn)

/-- The tied terminal polynomial is nonzero whenever the `c1` load is
nonzero. -/
theorem TransverseScale.c1TerminalAt_nonzero_at_transverse
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C1 R1 R2 R3 R4 : k)
    (hC1 : C1 ≠ 0)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant 0)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : 8 * D.faber.scale.p = 2 * T.delta) :
    c1TerminalAt D T C1 ≠ 0 := by
  have hrows := T.c1LeadingFaberRowsAt_at_transverse
    C1 R1 R2 R3 R4 hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 htie
  have hcoeff := GCD369CubeFaberC1NormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C1
  dsimp at hcoeff
  rcases hrows with ⟨hf1, hf2, _hf3, hf4⟩
  rcases hcoeff with ⟨hc1', hc2', _hc3', hc4'⟩
  rw [hc1'] at hf1
  rw [hc2'] at hf2
  rw [hc4'] at hf4
  have h1 :
      8 * C1 * D.u -
        9 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
        18 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) +
        9 * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 = 0 :=
    (mul_eq_zero.mp hf1).resolve_left (by norm_num)
  have h2 :
      -8 * C1 * D.v +
        9 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
        18 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) -
        18 * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) = 0 :=
    (mul_eq_zero.mp hf2).resolve_left (by norm_num)
  have h4 :
      8 * C1 * D.u * D.v + 27 * D.u * D.v *
          (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
        18 * D.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) -
        36 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) -
        18 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 -
        18 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) = 0 :=
    (mul_eq_zero.mp hf4).resolve_left (by norm_num)
  intro hterminal
  dsimp only [c1TerminalAt] at hterminal
  by_cases hu : D.u = 0
  · have hv : D.v ≠ 0 := D.hprojective.resolve_left (fun h => h hu)
    rw [hu] at h2 hterminal
    have hbad : C1 * D.v ^ 2 = 0 := by
      linear_combination (-1 / 16 : k) * (D.v * h2) +
        (-1 / 144 : k) * hterminal
    exact (mul_ne_zero hC1 (pow_ne_zero 2 hv)) hbad
  · have hbad : C1 * D.u ^ 4 = 0 := by
      linear_combination
        (3 / 32 * D.u ^ 3 + 9 / 32 * D.v ^ 2) * h1 +
        (9 / 64 * D.u * D.v) * h2 +
        (9 / 64 * D.v) * h4 +
        (1 / 32 * D.u) * hterminal
    exact (mul_ne_zero hC1 (pow_ne_zero 4 hu)) hbad

/-- Coefficient of the pure `c1` load in the denominator-cleared terminal
numerator. -/
def terminalC1Coeff {R : Type*} [CommRing R]
    (a0 _a1 a2 a3 a4 : R) : R :=
  2239488 * a0 - 373248 * a2 * a4 - 186624 * a3 ^ 2 +
    72576 * a4 ^ 3

/-- Isolate the pure `c1` contribution to the terminal numerator. -/
theorem fullN5_c1_specialize
    {R : Type*} [CommRing R]
    (a0 a1 a2 a3 a4 c1 : R) :
    GCD369CubeFaberFullN5 a0 a1 a2 a3 a4 0 0 0 0 0 0 c1 =
      GCD369CubeFaberFullN5 a0 a1 a2 a3 a4 0 0 0 0 0 0 0 +
        c1 * terminalC1Coeff a0 a1 a2 a3 a4 := by
  simp only [terminalC1Coeff]
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- At the exact tie, the pure-`c1` terminal numerator has coefficient
`-20736` times the unnormalized terminal polynomial. -/
theorem TransverseScale.c1SpecializedTerminalCoeff_at_transverse
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C1 : k)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (htie : 8 * D.faber.scale.p = 2 * T.delta) :
    (GCD369CubeFaberFullN5
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4 0 0 0 0 0 0
      (D.faber.scale.weightedRegular 8 D.faber.c1)).1.coeff
        (8 * D.faber.scale.p) =
      -20736 * c1TerminalAt D T C1 := by
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let P : GCD369CubeHahnRegular k := terminalC1Coeff
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4
  let K : GCD369CubeHahnRegular k :=
    559872 * GCD369CubeNormalRow5
      T.Xn T.Yn T.Zn D.cubicU D.cubicV +
      GCD369CubeHahnRegular.constant C1 * P
  let E : GCD369CubeHahnRegular k :=
    839808 * GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU
  have hhalf : ((8 : ℚ) * D.faber.scale.p) / 2 = T.delta := by
    linarith
  have hload : D.faber.scale.weightedRegular 8 D.faber.c1 =
      H ^ 2 * GCD369CubeHahnRegular.constant C1 := by
    rw [hc1, D.faber.scale.weightedRegular_constant_eq_monomial_sq
      8 (by norm_num) C1]
    apply Subtype.ext
    change
      (HahnSeries.single (((8 : ℕ) : ℚ) * D.faber.scale.p / 2) (1 : k)) ^ 2 *
          HahnSeries.C C1 =
        (HahnSeries.single T.delta (1 : k)) ^ 2 * HahnSeries.C C1
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
        D.faber.scale.regular4 0 0 0 0 0 0
        (D.faber.scale.weightedRegular 8 D.faber.c1) =
          H ^ 2 * K + H ^ 3 * E := by
    rw [fullN5_c1_specialize, hload]
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
      D.faber.scale.regular4 0 0 0 0 0 0
      (D.faber.scale.weightedRegular 8 D.faber.c1)).1.coeff
        (2 * T.delta) =
      (H ^ 2 * K).1.coeff (2 * T.delta) +
        (H ^ 3 * E).1.coeff (2 * T.delta) at hc
  rw [hmain, hhigh, add_zero] at hc
  rw [← htie] at hc
  rw [hc]
  dsimp only [K, P, terminalC1Coeff, c1TerminalAt]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat,
    GCD369CubeNormalRow5_map, D.constantCoeff_cubicU,
    D.constantCoeff_cubicV,
    GCD369CubeHahnRegular.constantCoeff_constant]
  have ha0 : GCD369CubeHahnRegular.constantCoeff
      D.faber.scale.regular0 = D.faber.scale.leading0 := rfl
  have ha2 : GCD369CubeHahnRegular.constantCoeff
      D.faber.scale.regular2 = D.faber.scale.leading2 := rfl
  have ha3 : GCD369CubeHahnRegular.constantCoeff
      D.faber.scale.regular3 = D.faber.scale.leading3 := rfl
  have ha4 : GCD369CubeHahnRegular.constantCoeff
      D.faber.scale.regular4 = D.faber.scale.leading4 := rfl
  rw [ha0, ha2, ha3, ha4, D.ha0, D.ha2, D.ha3, D.ha4]
  dsimp only [GCD369CubeNormalRow5]
  ring


set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- A nonzero tied `c1` load makes the complete terminal numerator have
exact order `8p`. -/
theorem TransverseScale.fullN5_orderTop_eq_eight_p_of_c1_tie
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C1 R1 R2 R3 R4 : k)
    (hC1 : C1 ≠ 0)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant 0)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (htie : 8 * D.faber.scale.p = 2 * T.delta) :
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
        (↑(8 * D.faber.scale.p) : WithTop ℚ) := by
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
  let c1row : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4 0 0 0 0 0 0
    (D.faber.scale.weightedRegular 8 D.faber.c1)
  have hterminal := T.c1TerminalAt_nonzero_at_transverse
    C1 R1 R2 R3 R4 hC1
    hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 htie
  have hspecialCoeff := T.c1SpecializedTerminalCoeff_at_transverse
    C1 hc1 htie
  have hspecialCoeffNe :
      c1row.1.coeff (8 * D.faber.scale.p) ≠ 0 := by
    change
      (GCD369CubeFaberFullN5
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 0 0 0 0 0 0
        (D.faber.scale.weightedRegular 8 D.faber.c1)).1.coeff
          (8 * D.faber.scale.p) ≠ 0
    rw [hspecialCoeff]
    exact mul_ne_zero (by norm_num) hterminal
  have hspecialUpper : c1row.1.orderTop ≤
      (↑(8 * D.faber.scale.p) : WithTop ℚ) :=
    HahnSeries.orderTop_le_of_coeff_ne_zero hspecialCoeffNe
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let P : GCD369CubeHahnRegular k := terminalC1Coeff
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4
  let K : GCD369CubeHahnRegular k :=
    559872 * GCD369CubeNormalRow5
      T.Xn T.Yn T.Zn D.cubicU D.cubicV +
      GCD369CubeHahnRegular.constant C1 * P
  let E : GCD369CubeHahnRegular k :=
    839808 * GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU
  have hhalf : ((8 : ℚ) * D.faber.scale.p) / 2 = T.delta := by
    linarith
  have hload : D.faber.scale.weightedRegular 8 D.faber.c1 =
      H ^ 2 * GCD369CubeHahnRegular.constant C1 := by
    rw [hc1, D.faber.scale.weightedRegular_constant_eq_monomial_sq
      8 (by norm_num) C1]
    apply Subtype.ext
    change
      (HahnSeries.single (((8 : ℕ) : ℚ) * D.faber.scale.p / 2) (1 : k)) ^ 2 *
          HahnSeries.C C1 =
        (HahnSeries.single T.delta (1 : k)) ^ 2 * HahnSeries.C C1
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
  have hfactor : c1row = H ^ 2 * (K + H * E) := by
    dsimp only [c1row]
    rw [fullN5_c1_specialize, hload]
    rw [hchart0, hchart1, hchart2,
      D.regular3_eq_two_cubicV, D.regular4_eq_two_cubicU]
    rw [hzero]
    dsimp only [K, E]
    rw [← hchart0, ← hchart1, ← hchart2,
      ← D.regular3_eq_two_cubicV, ← D.regular4_eq_two_cubicU]
    ring
  have hspecialLower : (↑(8 * D.faber.scale.p) : WithTop ℚ) ≤
      c1row.1.orderTop := by
    rw [hfactor, htie]
    exact GCD369CubeHahnRegular.orderTop_monomial_pow_mul_lower
      T.delta T.hdelta 2 (K + H * E)
  have hspecialOrder : c1row.1.orderTop =
      (↑(8 * D.faber.scale.p) : WithTop ℚ) :=
    le_antisymm hspecialUpper hspecialLower
  have hzeroWeighted (w : ℕ) (x : GCD369CubeHahnRegular k)
      (hx : x = GCD369CubeHahnRegular.constant 0) :
      D.faber.scale.weightedRegular w x = 0 := by
    rw [hx]
    apply Subtype.ext
    simp [GCD369CubeHahnPoleScale.weightedRegular]
  have hfull : full = c1row := by
    dsimp only [full, c1row]
    rw [hzeroWeighted 1 D.faber.d hd,
      hzeroWeighted 2 D.faber.c7 hc7,
      hzeroWeighted 4 D.faber.c5 hc5,
      hzeroWeighted 5 D.faber.c4 hc4,
      hzeroWeighted 6 D.faber.c3 hc3,
      hzeroWeighted 7 D.faber.c2 hc2]
  change full.1.orderTop = (↑(8 * D.faber.scale.p) : WithTop ℚ)
  rw [hfull]
  exact hspecialOrder

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubePolynomialSource

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- A nonzero `c1` load cannot tie the first transverse normal once all
earlier loads vanish.  The tied packet gives exact terminal order `8p`,
and the weight-eight degree landing excludes that order. -/
theorem infinity_c1_eq_zero_at_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hd0 : S.faberConstantParameters.d = 0)
    (hc70 : S.faberConstantParameters.c7 = 0)
    (hc50 : S.faberConstantParameters.c5 = 0)
    (hc40 : S.faberConstantParameters.c4 = 0)
    (hc30 : S.faberConstantParameters.c3 = 0)
    (hc20 : S.faberConstantParameters.c2 = 0)
    (htie :
      8 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p =
        2 * T.delta) :
    S.faberConstantParameters.c1 = 0 := by
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
  by_contra hPc1
  have hcoordinateD :
      D.faber.scale.leading4 ≠ 0 ∨ D.faber.scale.leading3 ≠ 0 := by
    rcases D.hprojective with hu | hv
    · left
      rw [D.ha4]
      exact mul_ne_zero (by norm_num) hu
    · right
      rw [D.ha3]
      exact mul_ne_zero (by norm_num) hv
  have hcoordinate :
      (S.infinityCommonCoefficientData hsdegree).faber.scale.leading4 ≠ 0 ∨
        (S.infinityCommonCoefficientData hsdegree).faber.scale.leading3 ≠ 0 := by
    simpa only [D] using hcoordinateD
  apply hPc1
  apply S.infinity_c1_eq_zero_of_terminal_order_eq_eight
    hsdegree hcoordinate
  intro _hload
  have hNorder := T.fullN5_orderTop_eq_eight_p_of_c1_tie
    P.c1 R.rho1 R.rho2 R.rho3 R.rho4 hPc1
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
      (8 * D.faber.scale.p) hNorder
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
`d=c3=0`; the remaining earlier load vanishings stay explicit. -/
theorem targetNormalized_infinity_c1_eq_zero_at_transverse
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
    (htie : let U := S.targetNormalizedSource
      let hsdegreeU : U.s.natDegree = 0 := by
        simpa [U, targetNormalizedSource] using hsdegree
      8 * (U.infinityCommonCoefficientData hsdegreeU).faber.scale.p =
        2 * T.delta) :
    S.targetNormalizedSource.faberConstantParameters.c1 = 0 := by
  let U := S.targetNormalizedSource
  let Q := U.faberConstantParameters
  have hsdegreeU : U.s.natDegree = 0 := by
    simpa [U, targetNormalizedSource] using hsdegree
  obtain ⟨hQd, _hQc7, _hQc6, _hQc5, _hQc4, hQc3,
      _hQc2, _hQc1, _hQc0⟩ :=
    S.targetNormalizedCanonicalParameters hd0
  apply U.infinity_c1_eq_zero_at_transverse hsdegreeU T
  · simpa only [Q, U] using hQd
  · simpa only [U] using hc70
  · simpa only [U] using hc50
  · simpa only [U] using hc40
  · simpa only [Q, U] using hQc3
  · simpa only [U] using hc20
  · exact htie

end GCD369CubePolynomialSource

#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.c1LeadingFaberRowsAt_at_transverse
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.c1TerminalAt_nonzero_at_transverse
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.c1SpecializedTerminalCoeff_at_transverse
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.fullN5_orderTop_eq_eight_p_of_c1_tie
#print axioms GCD369CubePolynomialSource.infinity_c1_eq_zero_at_transverse
#print axioms
  GCD369CubePolynomialSource.targetNormalized_infinity_c1_eq_zero_at_transverse
