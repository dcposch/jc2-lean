import InfinityCoefficientFactor
import InfinityDLoad
import FiniteC7Extraction

/-! # The strict-before weight-two load at infinity

At a prescribed c7 scale strictly below the first transverse normal order,
the normal residues vanish.  The surviving pure c7 Faber rows then contradict
the common-cubic root over the algebraically closed residue field.
-/

noncomputable section

open Polynomial

namespace GCD369CubeHahnCommonCoefficientData

theorem TransverseFactor.c7BeforeN1Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C7 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC7N1
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C7)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -32 * (56 * C7 * D.u ^ 4 - 1008 * C7 * D.u * D.v ^ 2 +
        GCD369CubeNormalRow1
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    12096 * D.faber.scale.regular0 * D.faber.scale.regular4 +
      12096 * D.faber.scale.regular1 * D.faber.scale.regular3 +
      6048 * D.faber.scale.regular2 ^ 2 -
      5040 * D.faber.scale.regular2 * D.faber.scale.regular4 ^ 2 -
      5040 * D.faber.scale.regular3 ^ 2 * D.faber.scale.regular4 +
      770 * D.faber.scale.regular4 ^ 4
  change
    (729 * GCD369CubeFaberN1
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C7 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN1Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C7 P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change _ + C7 *
    (12096 * D.faber.scale.leading0 * D.faber.scale.leading4 +
      12096 * D.faber.scale.leading1 * D.faber.scale.leading3 +
      6048 * D.faber.scale.leading2 ^ 2 -
      5040 * D.faber.scale.leading2 * D.faber.scale.leading4 ^ 2 -
      5040 * D.faber.scale.leading3 ^ 2 * D.faber.scale.leading4 +
      770 * D.faber.scale.leading4 ^ 4) = _
  rw [D.ha0, D.ha1, D.ha2, D.ha3, D.ha4]
  ring

theorem TransverseFactor.c7BeforeN2Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C7 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC7N2
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C7)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -96 * (224 * C7 * D.u ^ 3 * D.v - 336 * C7 * D.v ^ 3 +
        729 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 +
        1458 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) -
        1458 * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    36288 * D.faber.scale.regular0 * D.faber.scale.regular3 +
      36288 * D.faber.scale.regular1 * D.faber.scale.regular2 -
      15120 * D.faber.scale.regular1 * D.faber.scale.regular4 ^ 2 -
      30240 * D.faber.scale.regular2 * D.faber.scale.regular3 *
        D.faber.scale.regular4 -
      5040 * D.faber.scale.regular3 ^ 3 +
      9240 * D.faber.scale.regular3 * D.faber.scale.regular4 ^ 3
  change
    (2187 * GCD369CubeFaberN2
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C7 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN2Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C7 P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change _ + C7 *
    (36288 * D.faber.scale.leading0 * D.faber.scale.leading3 +
      36288 * D.faber.scale.leading1 * D.faber.scale.leading2 -
      15120 * D.faber.scale.leading1 * D.faber.scale.leading4 ^ 2 -
      30240 * D.faber.scale.leading2 * D.faber.scale.leading3 *
        D.faber.scale.leading4 -
      5040 * D.faber.scale.leading3 ^ 3 +
      9240 * D.faber.scale.leading3 * D.faber.scale.leading4 ^ 3) = _
  rw [D.ha0, D.ha1, D.ha2, D.ha3, D.ha4]
  dsimp only [GCD369CubeNormalRow2]
  ring

theorem TransverseFactor.c7BeforeN3Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C7 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC7N3
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C7)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      31104 * GCD369CubeNormalRow3
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    48384 * D.faber.scale.regular0 * D.faber.scale.regular2 -
      12096 * D.faber.scale.regular0 * D.faber.scale.regular4 ^ 2 +
      24192 * D.faber.scale.regular1 ^ 2 -
      32256 * D.faber.scale.regular1 * D.faber.scale.regular3 *
        D.faber.scale.regular4 -
      16128 * D.faber.scale.regular2 ^ 2 * D.faber.scale.regular4 -
      20160 * D.faber.scale.regular2 * D.faber.scale.regular3 ^ 2 +
      8960 * D.faber.scale.regular2 * D.faber.scale.regular4 ^ 3 +
      15120 * D.faber.scale.regular3 ^ 2 * D.faber.scale.regular4 ^ 2 -
      1232 * D.faber.scale.regular4 ^ 5
  have hzero :
      (243 * GCD369CubeFaberN3
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4).1.coeff (((2 : ℕ) : ℚ) * T.delta) =
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
      D.faber.scale.regular4).1.coeff (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C7 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [hzero,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C7 P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change _ + C7 *
    (48384 * D.faber.scale.leading0 * D.faber.scale.leading2 -
      12096 * D.faber.scale.leading0 * D.faber.scale.leading4 ^ 2 +
      24192 * D.faber.scale.leading1 ^ 2 -
      32256 * D.faber.scale.leading1 * D.faber.scale.leading3 *
        D.faber.scale.leading4 -
      16128 * D.faber.scale.leading2 ^ 2 * D.faber.scale.leading4 -
      20160 * D.faber.scale.leading2 * D.faber.scale.leading3 ^ 2 +
      8960 * D.faber.scale.leading2 * D.faber.scale.leading4 ^ 3 +
      15120 * D.faber.scale.leading3 ^ 2 * D.faber.scale.leading4 ^ 2 -
      1232 * D.faber.scale.leading4 ^ 5) = _
  rw [D.ha0, D.ha1, D.ha2, D.ha3, D.ha4]
  ring

theorem TransverseFactor.c7BeforeN4Coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C7 : k) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (GCD369CubeFaberC7N4
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4
      (H ^ 2 * GCD369CubeHahnRegular.constant C7)).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) =
      -288 * (224 * C7 * D.u ^ 4 * D.v - 1008 * C7 * D.u * D.v ^ 3 -
        2187 * D.u * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) ^ 2 -
        1458 * D.u ^ 2 * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Yn) +
        2916 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Xn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn) +
        1458 * D.v * (GCD369CubeHahnRegular.constantCoeff T.Yn) ^ 2 +
        1458 * D.u * (GCD369CubeHahnRegular.constantCoeff T.Yn) *
          (GCD369CubeHahnRegular.constantCoeff T.Zn)) := by
  dsimp only
  let P : GCD369CubeHahnRegular k :=
    326592 * D.faber.scale.regular0 * D.faber.scale.regular1 -
      108864 * D.faber.scale.regular0 * D.faber.scale.regular3 *
        D.faber.scale.regular4 -
      163296 * D.faber.scale.regular1 * D.faber.scale.regular2 *
        D.faber.scale.regular4 -
      81648 * D.faber.scale.regular1 * D.faber.scale.regular3 ^ 2 +
      37800 * D.faber.scale.regular1 * D.faber.scale.regular4 ^ 3 -
      108864 * D.faber.scale.regular2 ^ 2 * D.faber.scale.regular3 +
      136080 * D.faber.scale.regular2 * D.faber.scale.regular3 *
        D.faber.scale.regular4 ^ 2 +
      45360 * D.faber.scale.regular3 ^ 3 * D.faber.scale.regular4 -
      27720 * D.faber.scale.regular3 * D.faber.scale.regular4 ^ 4
  change
    (6561 * GCD369CubeFaberN4
      D.faber.scale.regular0 D.faber.scale.regular1
      D.faber.scale.regular2 D.faber.scale.regular3
      D.faber.scale.regular4).1.coeff (((2 : ℕ) : ℚ) * T.delta) +
    ((GCD369CubeHahnRegular.monomial T.delta T.hdelta.le) ^ 2 *
      GCD369CubeHahnRegular.constant C7 * P).1.coeff
        (((2 : ℕ) : ℚ) * T.delta) = _
  rw [T.zeroHighN4Coeff,
    GCD369CubeHahnRegular.coeff_monomial_sq_constant_mul
      T.delta T.hdelta C7 P]
  dsimp only [P]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  change _ + C7 *
    (326592 * D.faber.scale.leading0 * D.faber.scale.leading1 -
      108864 * D.faber.scale.leading0 * D.faber.scale.leading3 *
        D.faber.scale.leading4 -
      163296 * D.faber.scale.leading1 * D.faber.scale.leading2 *
        D.faber.scale.leading4 -
      81648 * D.faber.scale.leading1 * D.faber.scale.leading3 ^ 2 +
      37800 * D.faber.scale.leading1 * D.faber.scale.leading4 ^ 3 -
      108864 * D.faber.scale.leading2 ^ 2 * D.faber.scale.leading3 +
      136080 * D.faber.scale.leading2 * D.faber.scale.leading3 *
        D.faber.scale.leading4 ^ 2 +
      45360 * D.faber.scale.leading3 ^ 3 * D.faber.scale.leading4 -
      27720 * D.faber.scale.leading3 * D.faber.scale.leading4 ^ 4) = _
  rw [D.ha0, D.ha1, D.ha2, D.ha3, D.ha4]
  dsimp only [GCD369CubeNormalRow4]
  ring

/-- Vanishing of the four quadratic Hahn coefficients is exactly the
arbitrary-`c7` row packet on the prescribed normal residues. -/
theorem TransverseFactor.c7BeforeLeadingFaberRowsAt
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseFactor)
    (C7 : k)
    (h1 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC7N1
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C7)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h2 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC7N2
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C7)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h3 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC7N3
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C7)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0)
    (h4 : let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
      (GCD369CubeFaberC7N4
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4
        (H ^ 2 * GCD369CubeHahnRegular.constant C7)).1.coeff
          (((2 : ℕ) : ℚ) * T.delta) = 0) :
    GCD369CubeC7LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C7 := by
  dsimp [GCD369CubeC7LeadingFaberRowsAt]
  have hc := GCD369CubeFaberC7NormalCoefficients
    (GCD369CubeHahnRegular.constantCoeff T.Xn)
    (GCD369CubeHahnRegular.constantCoeff T.Yn)
    (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v C7
  dsimp only at hc
  rcases hc with ⟨hc1, hc2, hc3, hc4⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc1, ← T.c7BeforeN1Coeff C7]
    exact h1
  · rw [hc2, ← T.c7BeforeN2Coeff C7]
    exact h2
  · rw [hc3, ← T.c7BeforeN3Coeff C7]
    exact h3
  · rw [hc4, ← T.c7BeforeN4Coeff C7]
    exact h4

/-- A canonical first transverse scale bounds the orders of all three exact
normal coordinates. -/
theorem TransverseScale.normal_orderTop_lower_coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale) :
    (↑T.delta : WithTop ℚ) ≤ D.normal2.1.orderTop ∧
      (↑T.delta : WithTop ℚ) ≤ D.normal1.1.orderTop ∧
      (↑T.delta : WithTop ℚ) ≤ D.normal0.1.orderTop := by
  constructor
  · rw [T.hnormal2, monomial_eq_regularMonomial]
    exact GCD369CubeHahnRegular.monomial_mul_orderTop_lower
      T.delta T.hdelta.le T.Xn
  constructor
  · rw [T.hnormal1, monomial_eq_regularMonomial]
    exact GCD369CubeHahnRegular.monomial_mul_orderTop_lower
      T.delta T.hdelta.le T.Yn
  · rw [T.hnormal0, monomial_eq_regularMonomial]
    exact GCD369CubeHahnRegular.monomial_mul_orderTop_lower
      T.delta T.hdelta.le T.Zn

set_option maxHeartbeats 4000000 in
/-- Literal source parameters produce the pure `c7` row packet whenever the
three normal coordinates can be factored at the pole scale. -/
theorem c7BeforeLeadingFaberRowsAt_of_bounds
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k)
    (C7 C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (hnormal2 : (↑D.faber.scale.p : WithTop ℚ) ≤ D.normal2.1.orderTop)
    (hnormal1 : (↑D.faber.scale.p : WithTop ℚ) ≤ D.normal1.1.orderTop)
    (hnormal0 : (↑D.faber.scale.p : WithTop ℚ) ≤ D.normal0.1.orderTop) :
    let U := D.transverseFactorOfBounds D.faber.scale.p
      D.faber.scale.hp hnormal2 hnormal1 hnormal0
    GCD369CubeC7LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff U.Xn)
      (GCD369CubeHahnRegular.constantCoeff U.Yn)
      (GCD369CubeHahnRegular.constantCoeff U.Zn) D.u D.v C7 := by
  dsimp only
  let U := D.transverseFactorOfBounds D.faber.scale.p
    D.faber.scale.hp hnormal2 hnormal1 hnormal0
  have hz := D.faber.c7NCoeff_zero C5 C4 C3 C2 C1 R1 R2 R3 R4
    hd hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4
  rw [hc7,
    D.faber.scale.weightedRegular_constant_eq_monomial_sq
      2 (by norm_num) C7] at hz
  rcases hz with ⟨hz1, hz2, hz3, hz4⟩
  apply U.c7BeforeLeadingFaberRowsAt C7
  · have hUdelta : U.delta = D.faber.scale.p := rfl
    simp only [hUdelta]
    convert hz1 using 1 <;> norm_num
  · have hUdelta : U.delta = D.faber.scale.p := rfl
    simp only [hUdelta]
    convert hz2 using 1 <;> norm_num
  · have hUdelta : U.delta = D.faber.scale.p := rfl
    simp only [hUdelta]
    convert hz3 using 1 <;> norm_num
  · have hUdelta : U.delta = D.faber.scale.p := rfl
    simp only [hUdelta]
    convert hz4 using 1 <;> norm_num

set_option maxHeartbeats 4000000 in
/-- A nonzero constant `c7` load cannot arrive strictly before the first
transverse normal scale. -/
theorem TransverseScale.c7_eq_zero_strict_before
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C7 C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (hbefore : 2 * D.faber.scale.p < 2 * T.delta) :
    C7 = 0 := by
  have hpdelta : D.faber.scale.p < T.delta := by linarith
  obtain ⟨hn2, hn1, hn0⟩ := T.normal_orderTop_lower_coeff
  have hb2 : (↑D.faber.scale.p : WithTop ℚ) ≤ D.normal2.1.orderTop :=
    (WithTop.coe_le_coe.mpr hpdelta.le).trans hn2
  have hb1 : (↑D.faber.scale.p : WithTop ℚ) ≤ D.normal1.1.orderTop :=
    (WithTop.coe_le_coe.mpr hpdelta.le).trans hn1
  have hb0 : (↑D.faber.scale.p : WithTop ℚ) ≤ D.normal0.1.orderTop :=
    (WithTop.coe_le_coe.mpr hpdelta.le).trans hn0
  let U := D.transverseFactorOfBounds D.faber.scale.p
    D.faber.scale.hp hb2 hb1 hb0
  have hX : GCD369CubeHahnRegular.constantCoeff U.Xn = 0 := by
    dsimp only [U, transverseFactorOfBounds]
    rw [constantCoeff_shift]
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact (WithTop.coe_lt_coe.mpr hpdelta).trans_le hn2
  have hY : GCD369CubeHahnRegular.constantCoeff U.Yn = 0 := by
    dsimp only [U, transverseFactorOfBounds]
    rw [constantCoeff_shift]
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact (WithTop.coe_lt_coe.mpr hpdelta).trans_le hn1
  have hZ : GCD369CubeHahnRegular.constantCoeff U.Zn = 0 := by
    dsimp only [U, transverseFactorOfBounds]
    rw [constantCoeff_shift]
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact (WithTop.coe_lt_coe.mpr hpdelta).trans_le hn0
  have hrows : GCD369CubeC7LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff U.Xn)
      (GCD369CubeHahnRegular.constantCoeff U.Yn)
      (GCD369CubeHahnRegular.constantCoeff U.Zn) D.u D.v C7 := by
    simpa only [U] using D.c7BeforeLeadingFaberRowsAt_of_bounds
      C7 C5 C4 C3 C2 C1 R1 R2 R3 R4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4 hb2 hb1 hb0
  by_contra hC7
  have hnocommon := GCD369CubeC7LeadingFaberRowsAt_noCommonRoot
    (GCD369CubeHahnRegular.constantCoeff U.Xn)
    (GCD369CubeHahnRegular.constantCoeff U.Yn)
    (GCD369CubeHahnRegular.constantCoeff U.Zn)
    D.u D.v C7 hC7 D.hprojective hrows
  obtain ⟨r, hr⟩ := GCD369CubeExistsDepressedCubicRoot D.u D.v
  exact hnocommon r hr (by rw [hX, hY, hZ]; ring)

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubePolynomialSource

/-- Source-facing strict `c7` routing for the constant-core infinity packet,
after the weight-one source coefficient has vanished. -/
theorem infinity_c7_eq_zero_strict_before
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hd0 : S.faberConstantParameters.d = 0)
    (hbefore :
      2 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p <
        2 * T.delta) :
    S.faberConstantParameters.c7 = 0 := by
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  obtain ⟨hd, hc7, hc5, hc4, hc3, hc2, hc1,
      hr1, hr2, hr3, hr4⟩ :=
    S.infinityFaberPoleData_constant_loads hpole
  apply T.c7_eq_zero_strict_before
    P.c7 P.c5 P.c4 P.c3 P.c2 P.c1
      R.rho1 R.rho2 R.rho3 R.rho4
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    simpa only [P, hd0] using hd
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hc7
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hc5
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hc4
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hc3
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hc2
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hc1
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hr1
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hr2
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hr3
  · rw [S.infinityCommonCoefficientData_faber hsdegree]
    exact hr4
  · exact hbefore

end GCD369CubePolynomialSource

#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseFactor.c7BeforeLeadingFaberRowsAt
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.c7_eq_zero_strict_before
#print axioms GCD369CubePolynomialSource.infinity_c7_eq_zero_strict_before
