import FiniteTargetLoads

/-! # Source coefficient extraction for the first `rho1` load

When the weight-one parameter `d` and every later source parameter
`c7`, `c5`, `c4`, `c3`, `c2`, `c1` are the zero constant, `rho1` is a
literal ground-field constant `R`, and the remaining invariants are
arbitrary ground-field constants, the complete scaled Faber equations
reduce through order `10 p` to the universal zero-high primitive rows.
Their Hahn coefficients at that cutoff are the four values used by
`TransverseFactor.rhoOneLeadingFaberRowsAt`: `62208 * R`, `0`, `0`, `0`.
-/

noncomputable section

namespace GCD369CubeHahnRegular

/-- At the exact exponent of a positive monomial, multiplication by a
ground-field constant exposes that constant. -/
theorem coeff_monomial_mul_constant
    {k : Type*} [Field k] (delta : ℚ) (hdelta : 0 < delta) (c : k) :
    (monomial delta hdelta.le * constant c).1.coeff delta = c := by
  have h := coeff_monomial_pow_mul_at delta hdelta 1 (constant c)
  simpa [pow_one, one_mul, constantCoeff_constant] using h

/-- Congruence modulo the higher-order ideal preserves the coefficient at
the cutoff exponent. -/
theorem coeff_eq_of_sub_mem_higherOrderIdeal
    {k : Type*} [Field k] {e : ℚ} (he : 0 ≤ e)
    {x y : GCD369CubeHahnRegular k}
    (hxy : x - y ∈ higherOrderIdeal e he) :
    x.1.coeff e = y.1.coeff e := by
  have hzero : (x - y).1.coeff e = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop hxy
  change x.1.coeff e - y.1.coeff e = 0 at hzero
  exact sub_eq_zero.mp hzero

end GCD369CubeHahnRegular

namespace GCD369CubeHahnPoleScale

/-- A positive-weight ground-field constant is exactly the monomial of its
weighted exponent times that constant. -/
theorem weightedRegular_constant_eq_monomial
    {k : Type*} [Field k] (S : GCD369CubeHahnPoleScale k)
    (w : ℕ) (_hw : 0 < w) (c : k) :
    S.weightedRegular w (GCD369CubeHahnRegular.constant c) =
      GCD369CubeHahnRegular.monomial
          ((w : ℚ) * S.p)
          (mul_nonneg (Nat.cast_nonneg w) S.hp.le) *
        GCD369CubeHahnRegular.constant c := by
  apply Subtype.ext
  change S.t ^ w * HahnSeries.C c =
    HahnSeries.single ((w : ℚ) * S.p) 1 * HahnSeries.C c
  simp only [t, HahnSeries.single_pow, one_pow, nsmul_eq_mul]

end GCD369CubeHahnPoleScale

namespace GCD369CubeHahnFaberPoleData

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- When `d`, `c7`, `c5`, `c4`, `c3`, `c2`, and `c1` are the zero constant,
`rho1` is the constant `R`, and the later invariants are literal
ground-field constants, the four primitive zero-high Hahn coefficients at
exponent `10 p` are `62208 * R`, `0`, `0`, `0`.  The third row is the
unscaled primitive `N3` required by the first-`rho1` packet: the full
zero-high identity supplies `243 * N3`. -/
theorem rho1NCoeff
    {k : Type*} [Field k] [CharZero k]
    (F : GCD369CubeHahnFaberPoleData k)
    (R R2 R3 R4 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant 0)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant 0)
    (hr1 : F.rho1 = GCD369CubeHahnRegular.constant R)
    (hr2 : F.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : F.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : F.rho4 = GCD369CubeHahnRegular.constant R4) :
    (729 * GCD369CubeFaberN1
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1.coeff
        (((10 : ℕ) : ℚ) * F.scale.p) = 62208 * R ∧
    (2187 * GCD369CubeFaberN2
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1.coeff
        (((10 : ℕ) : ℚ) * F.scale.p) = 0 ∧
    (GCD369CubeFaberN3
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1.coeff
        (((10 : ℕ) : ℚ) * F.scale.p) = 0 ∧
    (6561 * GCD369CubeFaberN4
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1.coeff
        (((10 : ℕ) : ℚ) * F.scale.p) = 0 := by
  let e : ℚ := ((10 : ℕ) : ℚ) * F.scale.p
  have he : 0 ≤ e := mul_nonneg (Nat.cast_nonneg 10) F.scale.hp.le
  have hepos : 0 < e :=
    mul_pos (Nat.cast_pos.mpr (by norm_num : (0 : ℕ) < 10)) F.scale.hp
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal e he
  let q := Ideal.Quotient.mk I
  have hweight (w : ℕ) (hw : 10 < w) :
      e < (w : ℚ) * F.scale.p := by
    dsimp only [e]
    exact mul_lt_mul_of_pos_right
      (show ((10 : ℕ) : ℚ) < (w : ℚ) by exact_mod_cast hw) F.scale.hp
  have hkill (w : ℕ) (hw : 10 < w) (c : k)
      (x : GCD369CubeHahnRegular k)
      (hx : x = GCD369CubeHahnRegular.constant c) :
      q (F.scale.weightedRegular w x) = 0 := by
    rw [hx, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale w c he (hweight w hw)
  have hconst0 (w : ℕ) (x : GCD369CubeHahnRegular k)
      (hx : x = GCD369CubeHahnRegular.constant 0) :
      F.scale.weightedRegular w x = 0 := by
    rw [hx, map_zero]
    apply Subtype.ext
    simp [GCD369CubeHahnPoleScale.weightedRegular]
  have hd0 := hconst0 1 F.d hd
  have hc70 := hconst0 2 F.c7 hc7
  have hc50 := hconst0 4 F.c5 hc5
  have hc40 := hconst0 5 F.c4 hc4
  have hc30 := hconst0 6 F.c3 hc3
  have hc20 := hconst0 7 F.c2 hc2
  have hc10 := hconst0 8 F.c1 hc1
  have hdq : q (F.scale.weightedRegular 1 F.d) = 0 := by rw [hd0, map_zero]
  have hc7q : q (F.scale.weightedRegular 2 F.c7) = 0 := by rw [hc70, map_zero]
  have hc5q : q (F.scale.weightedRegular 4 F.c5) = 0 := by rw [hc50, map_zero]
  have hc4q : q (F.scale.weightedRegular 5 F.c4) = 0 := by rw [hc40, map_zero]
  have hc3q : q (F.scale.weightedRegular 6 F.c3) = 0 := by rw [hc30, map_zero]
  have hc2q : q (F.scale.weightedRegular 7 F.c2) = 0 := by rw [hc20, map_zero]
  have hc1q : q (F.scale.weightedRegular 8 F.c1) = 0 := by rw [hc10, map_zero]
  have hr2q := hkill 11 (by norm_num) R2 F.rho2 hr2
  have hr3q := hkill 12 (by norm_num) R3 F.rho3 hr3
  have hr4q := hkill 13 (by norm_num) R4 F.rho4 hr4
  have hcoeff_rho1 :
      (F.scale.weightedRegular 10
        (GCD369CubeHahnRegular.constant R)).1.coeff e = R := by
    rw [F.scale.weightedRegular_constant_eq_monomial 10 (by norm_num) R]
    exact GCD369CubeHahnRegular.coeff_monomial_mul_constant e hepos R
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
    have hcoeff :
        full.1.coeff e = 62208 * R := by
      rw [hscaled, hr1]
      have hnat :
          (62208 * F.scale.weightedRegular 10
            (GCD369CubeHahnRegular.constant R)).1.coeff e =
          (62208 : k) *
            (F.scale.weightedRegular 10
              (GCD369CubeHahnRegular.constant R)).1.coeff e :=
        GCD369CubeHahnRegular.coeff_nat_mul 62208 _ e
      rw [hnat, hcoeff_rho1]
    have hz : zeroFull.1.coeff e = 62208 * R := by
      have hsub : full - zeroFull ∈ I := (Ideal.Quotient.eq).mp hmap
      rw [← hcoeff]
      exact (GCD369CubeHahnRegular.coeff_eq_of_sub_mem_higherOrderIdeal
        he hsub).symm
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
    have hqfull_zero : q full = 0 := by
      rw [hscaled, map_mul, hr2q, mul_zero]
    have hqzero : q zeroFull = 0 := hmap ▸ hqfull_zero
    have hz : zeroFull.1.coeff e = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_orderTop
        (Ideal.Quotient.eq_zero_iff_mem.mp hqzero)
    dsimp only [zeroFull] at hz
    rw [(GCD369CubeFaberFullN_zeroHigh
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).2.1] at hz
    exact hz
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
    have hqfull_zero : q full = 0 := by
      rw [hscaled, map_mul, hr3q, mul_zero]
    have hqzero : q zeroFull = 0 := hmap ▸ hqfull_zero
    have hz : zeroFull.1.coeff e = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_orderTop
        (Ideal.Quotient.eq_zero_iff_mem.mp hqzero)
    dsimp only [zeroFull] at hz
    rw [(GCD369CubeFaberFullN_zeroHigh
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).2.2.1] at hz
    have hnat :
        (243 * GCD369CubeFaberN3
          F.scale.regular0 F.scale.regular1 F.scale.regular2
          F.scale.regular3 F.scale.regular4).1.coeff e =
        (243 : k) *
          (GCD369CubeFaberN3
            F.scale.regular0 F.scale.regular1 F.scale.regular2
            F.scale.regular3 F.scale.regular4).1.coeff e :=
      GCD369CubeHahnRegular.coeff_nat_mul 243 _ e
    rw [hnat] at hz
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
    have hqfull_zero : q full = 0 := by
      rw [hscaled, map_mul, hr4q, mul_zero]
    have hqzero : q zeroFull = 0 := hmap ▸ hqfull_zero
    have hz : zeroFull.1.coeff e = 0 :=
      HahnSeries.coeff_eq_zero_of_lt_orderTop
        (Ideal.Quotient.eq_zero_iff_mem.mp hqzero)
    dsimp only [zeroFull] at hz
    rw [(GCD369CubeFaberFullN_zeroHigh
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).2.2.2] at hz
    exact hz

end GCD369CubeHahnFaberPoleData

#print axioms GCD369CubeHahnRegular.coeff_monomial_mul_constant
#print axioms GCD369CubeHahnRegular.coeff_eq_of_sub_mem_higherOrderIdeal
#print axioms GCD369CubeHahnPoleScale.weightedRegular_constant_eq_monomial
#print axioms GCD369CubeHahnFaberPoleData.rho1NCoeff
