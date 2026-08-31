import FiniteRho1Extraction

/-! # Source coefficient extraction for the first `rho2` load

When the weight-one through weight-eight source parameters and the first
invariant are the zero constant, `rho2` is a literal ground-field constant
`R`, and the later invariants are arbitrary ground-field constants, the
complete scaled Faber equations reduce at exponent `11 p` to the four
primitive zero-high rows used by `TransverseFactor.rhoTwoLeadingFaberRowsAt`.
-/

noncomputable section
open Polynomial

namespace GCD369CubeHahnPoleScale

/-- A ground-field constant, scaled to weight `w`, has coefficient `c` at
the exact weighted exponent `w p`. -/
theorem weightedRegular_constant_coeff
    {k : Type*} [Field k] (S : GCD369CubeHahnPoleScale k)
    (w : ℕ) (c : k) :
    (S.weightedRegular w (GCD369CubeHahnRegular.constant c)).1.coeff
      ((w : ℚ) * S.p) = c := by
  have h : S.weightedRegular w (GCD369CubeHahnRegular.constant c) =
      GCD369CubeHahnRegular.monomial S.p S.hp.le ^ w *
        GCD369CubeHahnRegular.constant c := by
    apply Subtype.ext
    change S.t ^ w * HahnSeries.C c =
      (HahnSeries.single S.p 1) ^ w * HahnSeries.C c
    simp [GCD369CubeHahnPoleScale.t]
  rw [h]
  simpa using
    GCD369CubeHahnRegular.coeff_monomial_pow_mul_at
      S.p S.hp w (GCD369CubeHahnRegular.constant c)

end GCD369CubeHahnPoleScale

namespace GCD369CubeHahnFaberPoleData

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- When `d`, `c7`, `c5`, `c4`, `c3`, `c2`, `c1`, and `rho1` are the zero
constant, `rho2` is the ground-field constant `R`, and `rho3`, `rho4` are
arbitrary ground-field constants, the four primitive zero-high Hahn
coefficients at exponent `11 p` are `0`, `186624 * R`, `0`, and `0`. -/
theorem rho2NCoeff
    {k : Type*} [Field k] [CharZero k]
    (F : GCD369CubeHahnFaberPoleData k)
    (R R3 R4 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant 0)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant 0)
    (hr1 : F.rho1 = GCD369CubeHahnRegular.constant 0)
    (hr2 : F.rho2 = GCD369CubeHahnRegular.constant R)
    (hr3 : F.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : F.rho4 = GCD369CubeHahnRegular.constant R4) :
    (729 * GCD369CubeFaberN1
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1.coeff
        (((11 : ℕ) : ℚ) * F.scale.p) = 0 ∧
    (2187 * GCD369CubeFaberN2
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1.coeff
        (((11 : ℕ) : ℚ) * F.scale.p) = 186624 * R ∧
    (GCD369CubeFaberN3
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1.coeff
        (((11 : ℕ) : ℚ) * F.scale.p) = 0 ∧
    (6561 * GCD369CubeFaberN4
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1.coeff
        (((11 : ℕ) : ℚ) * F.scale.p) = 0 := by
  let e : ℚ := ((11 : ℕ) : ℚ) * F.scale.p
  have he : 0 ≤ e := mul_nonneg (Nat.cast_nonneg 11) F.scale.hp.le
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal e he
  let q := Ideal.Quotient.mk I
  have hweight (w : ℕ) (hw : 11 < w) :
      e < (w : ℚ) * F.scale.p := by
    dsimp only [e]
    exact mul_lt_mul_of_pos_right
      (show ((11 : ℕ) : ℚ) < (w : ℚ) by exact_mod_cast hw) F.scale.hp
  have hkill (w : ℕ) (hw : 11 < w) (c : k)
      (x : GCD369CubeHahnRegular k)
      (hx : x = GCD369CubeHahnRegular.constant c) :
      q (F.scale.weightedRegular w x) = 0 := by
    rw [hx, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale w c he (hweight w hw)
  have hconst0 (w : ℕ) (x : GCD369CubeHahnRegular k)
      (hx : x = GCD369CubeHahnRegular.constant 0) :
      q (F.scale.weightedRegular w x) = 0 := by
    have hx0 : F.scale.weightedRegular w x = 0 := by
      rw [hx, map_zero]
      apply Subtype.ext
      simp [GCD369CubeHahnPoleScale.weightedRegular]
    rw [hx0, map_zero]
  have hdq := hconst0 1 F.d hd
  have hc7q := hconst0 2 F.c7 hc7
  have hc5q := hconst0 4 F.c5 hc5
  have hc4q := hconst0 5 F.c4 hc4
  have hc3q := hconst0 6 F.c3 hc3
  have hc2q := hconst0 7 F.c2 hc2
  have hc1q := hconst0 8 F.c1 hc1
  have hr1q := hconst0 10 F.rho1 hr1
  have hr3q := hkill 12 (by norm_num) R3 F.rho3 hr3
  have hr4q := hkill 13 (by norm_num) R4 F.rho4 hr4
  have hrowZero (full zeroFull : GCD369CubeHahnRegular k)
      (hmap : q full = q zeroFull) (hscaled_zero : q full = 0) :
      zeroFull.1.coeff e = 0 := by
    have hqzero : q zeroFull = 0 := hmap ▸ hscaled_zero
    have hmem : zeroFull ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hqzero
    exact HahnSeries.coeff_eq_zero_of_lt_orderTop hmem
  constructor
  · let full := GCD369CubeFaberFullN1
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4
      (F.scale.weightedRegular 1 F.d)
      (F.scale.weightedRegular 2 F.c7)
      (F.scale.weightedRegular 4 F.c5)
      (F.scale.weightedRegular 5 F.c4)
      (F.scale.weightedRegular 6 F.c3)
      (F.scale.weightedRegular 7 F.c2)
      (F.scale.weightedRegular 8 F.c1)
    let zeroFull := GCD369CubeFaberFullN1
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4 0 0 0 0 0 0 0
    have hmap : q full = q zeroFull := by
      dsimp only [full, zeroFull]
      rw [(GCD369CubeFaberFullN_map q _ _ _ _ _ _ _ _ _ _ _ _).1,
        (GCD369CubeFaberFullN_map q _ _ _ _ _ 0 0 0 0 0 0 0).1,
        hdq, hc7q, hc5q, hc4q, hc3q, hc2q, hc1q]
      simp
    have hscaled : full = 62208 * F.scale.weightedRegular 10 F.rho1 := by
      apply Subtype.ext
      exact F.scaledFullN1
    have hqzero : q full = 0 := by
      rw [hscaled, map_mul, hr1q, mul_zero]
    have hz := hrowZero full zeroFull hmap hqzero
    dsimp only [zeroFull] at hz
    rw [(GCD369CubeFaberFullN_zeroHigh
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1] at hz
    exact hz
  constructor
  · let full := GCD369CubeFaberFullN2
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4
      (F.scale.weightedRegular 1 F.d)
      (F.scale.weightedRegular 2 F.c7)
      (F.scale.weightedRegular 4 F.c5)
      (F.scale.weightedRegular 5 F.c4)
      (F.scale.weightedRegular 6 F.c3)
      (F.scale.weightedRegular 7 F.c2)
      (F.scale.weightedRegular 8 F.c1)
    let zeroFull := GCD369CubeFaberFullN2
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4 0 0 0 0 0 0 0
    have hmap : q full = q zeroFull := by
      dsimp only [full, zeroFull]
      rw [(GCD369CubeFaberFullN_map q _ _ _ _ _ _ _ _ _ _ _ _).2.1,
        (GCD369CubeFaberFullN_map q _ _ _ _ _ 0 0 0 0 0 0 0).2.1,
        hdq, hc7q, hc5q, hc4q, hc3q, hc2q, hc1q]
      simp
    have hscaled : full = 186624 * F.scale.weightedRegular 11 F.rho2 := by
      apply Subtype.ext
      exact F.scaledFullN2
    let rhs := 186624 * F.scale.weightedRegular 11
      (GCD369CubeHahnRegular.constant R)
    have hq : q zeroFull = q rhs := by
      dsimp only [rhs]
      rw [← hmap, hscaled, hr2]
    have hcoeff : zeroFull.1.coeff e = rhs.1.coeff e :=
      GCD369CubeHahnRegular.coeff_eq_of_sub_mem_higherOrderIdeal he
        (Ideal.Quotient.eq.mp hq)
    dsimp only [zeroFull, rhs] at hcoeff
    rw [(GCD369CubeFaberFullN_zeroHigh
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).2.1] at hcoeff
    have hnat :
        (186624 * F.scale.weightedRegular 11
          (GCD369CubeHahnRegular.constant R)).1.coeff e =
        (186624 : k) *
          (F.scale.weightedRegular 11
            (GCD369CubeHahnRegular.constant R)).1.coeff e :=
      GCD369CubeHahnRegular.coeff_nat_mul 186624 _ e
    rw [hnat, F.scale.weightedRegular_constant_coeff 11 R] at hcoeff
    exact hcoeff
  constructor
  · let full := GCD369CubeFaberFullN3
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4
      (F.scale.weightedRegular 1 F.d)
      (F.scale.weightedRegular 2 F.c7)
      (F.scale.weightedRegular 4 F.c5)
      (F.scale.weightedRegular 5 F.c4)
      (F.scale.weightedRegular 6 F.c3)
      (F.scale.weightedRegular 7 F.c2)
      (F.scale.weightedRegular 8 F.c1)
    let zeroFull := GCD369CubeFaberFullN3
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4 0 0 0 0 0 0 0
    have hmap : q full = q zeroFull := by
      dsimp only [full, zeroFull]
      rw [(GCD369CubeFaberFullN_map q _ _ _ _ _ _ _ _ _ _ _ _).2.2.1,
        (GCD369CubeFaberFullN_map q _ _ _ _ _ 0 0 0 0 0 0 0).2.2.1,
        hdq, hc7q, hc5q, hc4q, hc3q, hc2q, hc1q]
      simp
    have hscaled : full = 248832 * F.scale.weightedRegular 12 F.rho3 := by
      apply Subtype.ext
      exact F.scaledFullN3
    have hqzero : q full = 0 := by
      rw [hscaled, map_mul, hr3q, mul_zero]
    have hz := hrowZero full zeroFull hmap hqzero
    dsimp only [zeroFull] at hz
    rw [(GCD369CubeFaberFullN_zeroHigh
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).2.2.1] at hz
    have hcoeff :
        (243 * GCD369CubeFaberN3
          F.scale.regular0 F.scale.regular1 F.scale.regular2
          F.scale.regular3 F.scale.regular4).1.coeff e =
        (243 : k) *
          (GCD369CubeFaberN3
            F.scale.regular0 F.scale.regular1 F.scale.regular2
            F.scale.regular3 F.scale.regular4).1.coeff e :=
      GCD369CubeHahnRegular.coeff_nat_mul 243 _ e
    rw [hcoeff] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · let full := GCD369CubeFaberFullN4
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4
      (F.scale.weightedRegular 1 F.d)
      (F.scale.weightedRegular 2 F.c7)
      (F.scale.weightedRegular 4 F.c5)
      (F.scale.weightedRegular 5 F.c4)
      (F.scale.weightedRegular 6 F.c3)
      (F.scale.weightedRegular 7 F.c2)
      (F.scale.weightedRegular 8 F.c1)
    let zeroFull := GCD369CubeFaberFullN4
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4 0 0 0 0 0 0 0
    have hmap : q full = q zeroFull := by
      dsimp only [full, zeroFull]
      rw [(GCD369CubeFaberFullN_map q _ _ _ _ _ _ _ _ _ _ _ _).2.2.2,
        (GCD369CubeFaberFullN_map q _ _ _ _ _ 0 0 0 0 0 0 0).2.2.2,
        hdq, hc7q, hc5q, hc4q, hc3q, hc2q, hc1q]
      simp
    have hscaled : full = 1679616 * F.scale.weightedRegular 13 F.rho4 := by
      apply Subtype.ext
      exact F.scaledFullN4
    have hqzero : q full = 0 := by
      rw [hscaled, map_mul, hr4q, mul_zero]
    have hz := hrowZero full zeroFull hmap hqzero
    dsimp only [zeroFull] at hz
    rw [(GCD369CubeFaberFullN_zeroHigh
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).2.2.2] at hz
    exact hz

end GCD369CubeHahnFaberPoleData

#print axioms GCD369CubeHahnRegular.coeff_eq_of_sub_mem_higherOrderIdeal
#print axioms GCD369CubeHahnPoleScale.weightedRegular_constant_coeff
#print axioms GCD369CubeHahnFaberPoleData.rho2NCoeff
