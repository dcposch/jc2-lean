import FiniteC5Source

/-! # Source coefficient extraction for the first `c5` load

When the weight-one parameter `d` and the weight-two parameter `c7` are
the zero constant and every later source parameter is a literal
ground-field constant, the complete scaled Faber equations reduce through
order `4 p` to the specialized `c5` numerators.  Their Hahn coefficients
at that cutoff therefore vanish.
-/

noncomputable section
open Polynomial

/-- Setting `d`, `c7`, and every parameter after `c5` to zero specializes
the four complete numerators to the integral `c5` rows over any
commutative ring. -/
theorem GCD369CubeFaberFullN_c5_specialize
    {R : Type*} [CommRing R] (a0 a1 a2 a3 a4 c5 : R) :
    GCD369CubeFaberFullN1 a0 a1 a2 a3 a4 0 0 c5 0 0 0 0 =
        GCD369CubeFaberC5N1 a0 a1 a2 a3 a4 c5 ∧
    GCD369CubeFaberFullN2 a0 a1 a2 a3 a4 0 0 c5 0 0 0 0 =
        GCD369CubeFaberC5N2 a0 a1 a2 a3 a4 c5 ∧
    GCD369CubeFaberFullN3 a0 a1 a2 a3 a4 0 0 c5 0 0 0 0 =
        GCD369CubeFaberC5N3 a0 a1 a2 a3 a4 c5 ∧
    GCD369CubeFaberFullN4 a0 a1 a2 a3 a4 0 0 c5 0 0 0 0 =
        GCD369CubeFaberC5N4 a0 a1 a2 a3 a4 c5 := by
  constructor
  · simp only [GCD369CubeFaberC5N1, GCD369CubeFaberN1]
    ring
  constructor
  · simp only [GCD369CubeFaberC5N2, GCD369CubeFaberN2]
    ring
  constructor
  · simp only [GCD369CubeFaberC5N3, GCD369CubeFaberN3]
    ring
  · simp only [GCD369CubeFaberC5N4, GCD369CubeFaberN4]
    ring

/-- The four integral `c5` rows commute with arbitrary commutative-ring
homomorphisms. -/
theorem GCD369CubeFaberC5_map
    {R L : Type*} [CommRing R] [CommRing L] (f : R →+* L)
    (a0 a1 a2 a3 a4 c5 : R) :
    f (GCD369CubeFaberC5N1 a0 a1 a2 a3 a4 c5) =
        GCD369CubeFaberC5N1 (f a0) (f a1) (f a2) (f a3) (f a4) (f c5) ∧
    f (GCD369CubeFaberC5N2 a0 a1 a2 a3 a4 c5) =
        GCD369CubeFaberC5N2 (f a0) (f a1) (f a2) (f a3) (f a4) (f c5) ∧
    f (GCD369CubeFaberC5N3 a0 a1 a2 a3 a4 c5) =
        GCD369CubeFaberC5N3 (f a0) (f a1) (f a2) (f a3) (f a4) (f c5) ∧
    f (GCD369CubeFaberC5N4 a0 a1 a2 a3 a4 c5) =
        GCD369CubeFaberC5N4 (f a0) (f a1) (f a2) (f a3) (f a4) (f c5) := by
  constructor
  · simp only [GCD369CubeFaberC5N1, GCD369CubeFaberN1,
      map_add, map_sub, map_mul, map_pow, map_ofNat]
  constructor
  · simp only [GCD369CubeFaberC5N2, GCD369CubeFaberN2,
      map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
  constructor
  · simp only [GCD369CubeFaberC5N3, GCD369CubeFaberN3,
      map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
  · simp only [GCD369CubeFaberC5N4, GCD369CubeFaberN4,
      map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]

namespace GCD369CubeHahnFaberPoleData

set_option maxRecDepth 10000 in
/-- When `d` and `c7` are the zero constant and every later source
parameter, together with the four invariants, is a literal ground-field
constant, the complete scaled equations reduce through order `4 p` to the
specialized `c5` numerators, whose coefficients at that cutoff vanish. -/
theorem c5NCoeff_zero
    {k : Type*} [Field k] [CharZero k]
    (F : GCD369CubeHahnFaberPoleData k)
    (C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : F.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : F.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : F.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : F.rho4 = GCD369CubeHahnRegular.constant R4) :
    (GCD369CubeFaberC5N1
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4
      (F.scale.weightedRegular 4 F.c5)).1.coeff
        (((4 : ℕ) : ℚ) * F.scale.p) = 0 ∧
    (GCD369CubeFaberC5N2
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4
      (F.scale.weightedRegular 4 F.c5)).1.coeff
        (((4 : ℕ) : ℚ) * F.scale.p) = 0 ∧
    (GCD369CubeFaberC5N3
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4
      (F.scale.weightedRegular 4 F.c5)).1.coeff
        (((4 : ℕ) : ℚ) * F.scale.p) = 0 ∧
    (GCD369CubeFaberC5N4
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4
      (F.scale.weightedRegular 4 F.c5)).1.coeff
        (((4 : ℕ) : ℚ) * F.scale.p) = 0 := by
  let e : ℚ := ((4 : ℕ) : ℚ) * F.scale.p
  have he : 0 ≤ e := mul_nonneg (Nat.cast_nonneg 4) F.scale.hp.le
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal e he
  let q := Ideal.Quotient.mk I
  have hweight (w : ℕ) (hw : 4 < w) :
      e < (w : ℚ) * F.scale.p := by
    dsimp only [e]
    exact mul_lt_mul_of_pos_right
      (show ((4 : ℕ) : ℚ) < (w : ℚ) by exact_mod_cast hw) F.scale.hp
  have hkill (w : ℕ) (hw : 4 < w) (c : k)
      (x : GCD369CubeHahnRegular k)
      (hx : x = GCD369CubeHahnRegular.constant c) :
      q (F.scale.weightedRegular w x) = 0 := by
    rw [hx, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale w c he (hweight w hw)
  have hd_zero : F.scale.weightedRegular 1 F.d = 0 := by
    rw [hd, map_zero]
    apply Subtype.ext
    simp [GCD369CubeHahnPoleScale.weightedRegular]
  have hdq : q (F.scale.weightedRegular 1 F.d) = 0 := by
    rw [hd_zero, map_zero]
  have hc7_zero : F.scale.weightedRegular 2 F.c7 = 0 := by
    rw [hc7, map_zero]
    apply Subtype.ext
    simp [GCD369CubeHahnPoleScale.weightedRegular]
  have hc7q : q (F.scale.weightedRegular 2 F.c7) = 0 := by
    rw [hc7_zero, map_zero]
  have hc4q := hkill 5 (by norm_num) C4 F.c4 hc4
  have hc3q := hkill 6 (by norm_num) C3 F.c3 hc3
  have hc2q := hkill 7 (by norm_num) C2 F.c2 hc2
  have hc1q := hkill 8 (by norm_num) C1 F.c1 hc1
  have hr1q := hkill 10 (by norm_num) R1 F.rho1 hr1
  have hr2q := hkill 11 (by norm_num) R2 F.rho2 hr2
  have hr3q := hkill 12 (by norm_num) R3 F.rho3 hr3
  have hr4q := hkill 13 (by norm_num) R4 F.rho4 hr4
  have hrow (full crow : GCD369CubeHahnRegular k)
      (hmap : q full = q crow) (hscaled_zero : q full = 0) :
      crow.1.coeff e = 0 := by
    have hqcrow_zero : q crow = 0 := hmap ▸ hscaled_zero
    have hcrow_mem : crow ∈ I :=
      Ideal.Quotient.eq_zero_iff_mem.mp hqcrow_zero
    have hcrow_order : (↑e : WithTop ℚ) < crow.1.orderTop := hcrow_mem
    exact HahnSeries.coeff_eq_zero_of_lt_orderTop hcrow_order
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
    let crow := GCD369CubeFaberC5N1
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4
      (F.scale.weightedRegular 4 F.c5)
    have hqfull_crow : q full = q crow := by
      dsimp only [full, crow]
      rw [(GCD369CubeFaberFullN_map q _ _ _ _ _ _ _ _ _ _ _ _).1,
        (GCD369CubeFaberC5_map q _ _ _ _ _ _).1,
        hdq, hc7q, hc4q, hc3q, hc2q, hc1q]
      exact (GCD369CubeFaberFullN_c5_specialize _ _ _ _ _ _).1
    have hscaled : full = 62208 * F.scale.weightedRegular 10 F.rho1 := by
      apply Subtype.ext
      exact F.scaledFullN1
    have hqfull_zero : q full = 0 := by
      rw [hscaled, map_mul, hr1q, mul_zero]
    exact hrow full crow hqfull_crow hqfull_zero
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
    let crow := GCD369CubeFaberC5N2
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4
      (F.scale.weightedRegular 4 F.c5)
    have hqfull_crow : q full = q crow := by
      dsimp only [full, crow]
      rw [(GCD369CubeFaberFullN_map q _ _ _ _ _ _ _ _ _ _ _ _).2.1,
        (GCD369CubeFaberC5_map q _ _ _ _ _ _).2.1,
        hdq, hc7q, hc4q, hc3q, hc2q, hc1q]
      exact (GCD369CubeFaberFullN_c5_specialize _ _ _ _ _ _).2.1
    have hscaled : full = 186624 * F.scale.weightedRegular 11 F.rho2 := by
      apply Subtype.ext
      exact F.scaledFullN2
    have hqfull_zero : q full = 0 := by
      rw [hscaled, map_mul, hr2q, mul_zero]
    exact hrow full crow hqfull_crow hqfull_zero
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
    let crow := GCD369CubeFaberC5N3
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4
      (F.scale.weightedRegular 4 F.c5)
    have hqfull_crow : q full = q crow := by
      dsimp only [full, crow]
      rw [(GCD369CubeFaberFullN_map q _ _ _ _ _ _ _ _ _ _ _ _).2.2.1,
        (GCD369CubeFaberC5_map q _ _ _ _ _ _).2.2.1,
        hdq, hc7q, hc4q, hc3q, hc2q, hc1q]
      exact (GCD369CubeFaberFullN_c5_specialize _ _ _ _ _ _).2.2.1
    have hscaled : full = 248832 * F.scale.weightedRegular 12 F.rho3 := by
      apply Subtype.ext
      exact F.scaledFullN3
    have hqfull_zero : q full = 0 := by
      rw [hscaled, map_mul, hr3q, mul_zero]
    exact hrow full crow hqfull_crow hqfull_zero
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
    let crow := GCD369CubeFaberC5N4
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4
      (F.scale.weightedRegular 4 F.c5)
    have hqfull_crow : q full = q crow := by
      dsimp only [full, crow]
      rw [(GCD369CubeFaberFullN_map q _ _ _ _ _ _ _ _ _ _ _ _).2.2.2,
        (GCD369CubeFaberC5_map q _ _ _ _ _ _).2.2.2,
        hdq, hc7q, hc4q, hc3q, hc2q, hc1q]
      exact (GCD369CubeFaberFullN_c5_specialize _ _ _ _ _ _).2.2.2
    have hscaled : full = 1679616 * F.scale.weightedRegular 13 F.rho4 := by
      apply Subtype.ext
      exact F.scaledFullN4
    have hqfull_zero : q full = 0 := by
      rw [hscaled, map_mul, hr4q, mul_zero]
    exact hrow full crow hqfull_crow hqfull_zero

end GCD369CubeHahnFaberPoleData

#print axioms GCD369CubeFaberFullN_c5_specialize
#print axioms GCD369CubeFaberC5_map
#print axioms GCD369CubeHahnFaberPoleData.c5NCoeff_zero
