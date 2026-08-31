import FiniteC4EarlyNormal

/-! # Early transverse jets before the first weight-seven load

If a common-cubic transverse jet occurs before the weight-seven `c2` scale,
and the weight-one, weight-two, weight-four, weight-five, and weight-six
parameters have already vanished, then every remaining source and target
load disappears in the corresponding higher-order quotient.  The four
complete Faber equations therefore reduce to the universal zero-load
normal rows.  A nonzero first jet consequently forces the limiting cubic
onto its double-root discriminant.
-/

noncomputable section

namespace GCD369CubeHahnFaberPoleData

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- Below the weight-seven scale, after the weight-one, weight-two,
weight-four, weight-five, and weight-six loads have vanished, the complete
source equations have exactly the zero-high-constant leading
coefficients. -/
theorem zeroHighNCoeff_zero_before_c2
    {k : Type*} [Field k] [CharZero k]
    (F : GCD369CubeHahnFaberPoleData k)
    (hd : F.d = 0)
    (hc7 : F.c7 = 0)
    (hc5 : F.c5 = 0)
    (hc4 : F.c4 = 0)
    (hc3 : F.c3 = 0)
    (e : ℚ) (he : 0 ≤ e) (hearly : e < 7 * F.scale.p) :
    (729 * GCD369CubeFaberN1
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1.coeff e = 0 ∧
    (2187 * GCD369CubeFaberN2
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1.coeff e = 0 ∧
    (243 * GCD369CubeFaberN3
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1.coeff e = 0 ∧
    (6561 * GCD369CubeFaberN4
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1.coeff e = 0 := by
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal e he
  let q := Ideal.Quotient.mk I
  have hweight (w : ℕ) (hw : 7 ≤ w) :
      e < (w : ℚ) * F.scale.p := by
    calc
      e < (7 : ℚ) * F.scale.p := by simpa using hearly
      _ ≤ (w : ℚ) * F.scale.p := by
        exact mul_le_mul_of_nonneg_right
          (show (7 : ℚ) ≤ (w : ℚ) by exact_mod_cast hw) F.scale.hp.le
  have hkill (w : ℕ) (hw : 7 ≤ w)
      (x : GCD369CubeHahnRegular k) :
      q (F.scale.weightedRegular w x) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change (↑e : WithTop ℚ) <
      (F.scale.weightedRegular w x).1.orderTop
    exact (WithTop.coe_lt_coe.mpr (hweight w hw)).trans_le
      (F.scale.weightedRegular_orderTop_lower w x)
  have hdq : q (F.scale.weightedRegular 1 F.d) = 0 := by
    have hzw : F.scale.weightedRegular 1 F.d = 0 := by
      apply Subtype.ext
      change F.scale.t ^ 1 * F.d.1 = 0
      rw [hd]
      simp
    rw [hzw, map_zero]
  have hc7q : q (F.scale.weightedRegular 2 F.c7) = 0 := by
    have hzw : F.scale.weightedRegular 2 F.c7 = 0 := by
      apply Subtype.ext
      change F.scale.t ^ 2 * F.c7.1 = 0
      rw [hc7]
      simp
    rw [hzw, map_zero]
  have hc5q : q (F.scale.weightedRegular 4 F.c5) = 0 := by
    have hzw : F.scale.weightedRegular 4 F.c5 = 0 := by
      apply Subtype.ext
      change F.scale.t ^ 4 * F.c5.1 = 0
      rw [hc5]
      simp
    rw [hzw, map_zero]
  have hc4q : q (F.scale.weightedRegular 5 F.c4) = 0 := by
    have hzw : F.scale.weightedRegular 5 F.c4 = 0 := by
      apply Subtype.ext
      change F.scale.t ^ 5 * F.c4.1 = 0
      rw [hc4]
      simp
    rw [hzw, map_zero]
  have hc3q : q (F.scale.weightedRegular 6 F.c3) = 0 := by
    have hzw : F.scale.weightedRegular 6 F.c3 = 0 := by
      apply Subtype.ext
      change F.scale.t ^ 6 * F.c3.1 = 0
      rw [hc3]
      simp
    rw [hzw, map_zero]
  have hc2q := hkill 7 (by norm_num) F.c2
  have hc1q := hkill 8 (by norm_num) F.c1
  have hr1q := hkill 10 (by norm_num) F.rho1
  have hr2q := hkill 11 (by norm_num) F.rho2
  have hr3q := hkill 12 (by norm_num) F.rho3
  have hr4q := hkill 13 (by norm_num) F.rho4
  have hrow (full zeroFull : GCD369CubeHahnRegular k)
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
    have hz := hrow full zeroFull hmap hqzero
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
    have hqzero : q full = 0 := by
      rw [hscaled, map_mul, hr2q, mul_zero]
    have hz := hrow full zeroFull hmap hqzero
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
    have hqzero : q full = 0 := by
      rw [hscaled, map_mul, hr3q, mul_zero]
    have hz := hrow full zeroFull hmap hqzero
    dsimp only [zeroFull] at hz
    rw [(GCD369CubeFaberFullN_zeroHigh
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).2.2.1] at hz
    exact hz
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
    have hz := hrow full zeroFull hmap hqzero
    dsimp only [zeroFull] at hz
    rw [(GCD369CubeFaberFullN_zeroHigh
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).2.2.2] at hz
    exact hz

end GCD369CubeHahnFaberPoleData

namespace GCD369CubeHahnCommonValueData

/-- Any transverse factor strictly before the first weight-seven load, after
the weight-one, weight-two, weight-four, weight-five, and weight-six
parameters have vanished, satisfies the four universal zero-load normal
equations on its residue jet. -/
theorem TransverseFactor.zeroLoadLeadingRows_before_c2
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (hd : F.d = 0)
    (hc7 : F.c7 = 0)
    (hc5 : F.c5 = 0)
    (hc4 : F.c4 = 0)
    (hc3 : F.c3 = 0)
    (hearly : 2 * T.delta < 7 * F.scale.p) :
    GCD369CubeNormalRow1
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u = 0 ∧
    GCD369CubeNormalRow2
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v = 0 ∧
    GCD369CubeNormalRow3
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v = 0 ∧
    GCD369CubeNormalRow4
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v = 0 := by
  have hz := F.zeroHighNCoeff_zero_before_c2 hd hc7 hc5 hc4 hc3
    (2 * T.delta) (mul_nonneg (by norm_num) T.hdelta.le) hearly
  rw [← hscale] at hz
  rcases hz with ⟨h1, h2, h3, h4⟩
  constructor
  · have hc :
        (729 * GCD369CubeFaberN1
          S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
          S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
          S.normal.sextic.scale.regular4).1.coeff (2 * T.delta) =
        -32 * GCD369CubeNormalRow1
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u := by
      convert T.zeroHighN1Coeff using 1 <;> norm_num
    rw [hc] at h1
    exact (mul_eq_zero.mp h1).resolve_left (by norm_num)
  constructor
  · have hc :
        (2187 * GCD369CubeFaberN2
          S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
          S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
          S.normal.sextic.scale.regular4).1.coeff (2 * T.delta) =
        32 * GCD369CubeNormalRow2
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v := by
      convert T.zeroHighN2Coeff using 1 <;> norm_num
    rw [hc] at h2
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  constructor
  · have hcoeff :
        (243 * GCD369CubeFaberN3
          S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
          S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
          S.normal.sextic.scale.regular4).1.coeff (2 * T.delta) =
        (243 : k) *
          (GCD369CubeFaberN3
            S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
            S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
            S.normal.sextic.scale.regular4).1.coeff (2 * T.delta) := by
      exact GCD369CubeHahnRegular.coeff_nat_mul 243 _ _
    rw [hcoeff] at h3
    have h3' :
        (GCD369CubeFaberN3
          S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
          S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
          S.normal.sextic.scale.regular4).1.coeff (2 * T.delta) = 0 :=
      (mul_eq_zero.mp h3).resolve_left (by norm_num)
    have hc :
        (GCD369CubeFaberN3
          S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
          S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
          S.normal.sextic.scale.regular4).1.coeff (2 * T.delta) =
        128 * GCD369CubeNormalRow3
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v := by
      convert T.zeroHighN3Coeff using 1 <;> norm_num
    rw [hc] at h3'
    exact (mul_eq_zero.mp h3').resolve_left (by norm_num)
  · have hc :
        (6561 * GCD369CubeFaberN4
          S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
          S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
          S.normal.sextic.scale.regular4).1.coeff (2 * T.delta) =
        32 * GCD369CubeNormalRow4
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v := by
      convert T.zeroHighN4Coeff using 1 <;> norm_num
    rw [hc] at h4
    exact (mul_eq_zero.mp h4).resolve_left (by norm_num)

/-- A nonzero first transverse jet before the `c2` scale, after the
weight-one, weight-two, weight-four, weight-five, and weight-six
parameters have vanished, forces the limiting common cubic to be
singular. -/
theorem TransverseScale.discriminant_zero_before_c2
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (hd : F.d = 0)
    (hc7 : F.c7 = 0)
    (hc5 : F.c5 = 0)
    (hc4 : F.c4 = 0)
    (hc3 : F.c3 = 0)
    (hearly : 2 * T.delta < 7 * F.scale.p) :
    4 * S.u ^ 3 + 27 * S.v ^ 2 = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := T.factor.zeroLoadLeadingRows_before_c2 F hscale
    hd hc7 hc5 hc4 hc3 hearly
  obtain ⟨r, _hr, _hX, hu, hv, _hY, _hZ, _hx, _hphi⟩ :=
    GCD369CubeZeroLoadNormal_root_data
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn)
      S.u S.v (GCD369CubeHahnRegular.constantCoeff S.normal.sextic.regularX)
      S.hprojective T.hleading h1 h2 h3 h4 S.leadingCubicRoot
  rw [hu, hv]
  ring

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnFaberPoleData.zeroHighNCoeff_zero_before_c2
#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.zeroLoadLeadingRows_before_c2
#print axioms GCD369CubeHahnCommonValueData.TransverseScale.discriminant_zero_before_c2
