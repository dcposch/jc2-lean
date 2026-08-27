import InfinityC2Tie
import InfinityC7Late

/-! # The strict-late weight-seven cell at infinity

After `d=c7=c5=c4=c3=0`, every remaining source or target load starts at
weight at least seven.  Thus, when `3δ < 7p`, the intrinsic cubic transverse term is
the exact first term of the terminal numerator, contradicting the singular
constant-core degree lattice.
-/

noncomputable section

namespace GCD369CubeHahnFaberPoleData

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Below the weight-seven scale, after `d=c7=c5=c4=c3=0`, the four complete source
equations reduce modulo the cutoff to their zero-load numerators. -/
theorem zeroLoadN_mem_higherOrderIdeal_of_lt_seven_p
    {k : Type*} [Field k] [CharZero k]
    (F : GCD369CubeHahnFaberPoleData k)
    (e : ℚ) (he : 0 ≤ e) (hlt : e < 7 * F.scale.p)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant 0) :
    729 * GCD369CubeFaberN1
        F.scale.regular0 F.scale.regular1 F.scale.regular2
        F.scale.regular3 F.scale.regular4 ∈
          GCD369CubeHahnRegular.higherOrderIdeal e he ∧
    2187 * GCD369CubeFaberN2
        F.scale.regular0 F.scale.regular1 F.scale.regular2
        F.scale.regular3 F.scale.regular4 ∈
          GCD369CubeHahnRegular.higherOrderIdeal e he ∧
    243 * GCD369CubeFaberN3
        F.scale.regular0 F.scale.regular1 F.scale.regular2
        F.scale.regular3 F.scale.regular4 ∈
          GCD369CubeHahnRegular.higherOrderIdeal e he ∧
    6561 * GCD369CubeFaberN4
        F.scale.regular0 F.scale.regular1 F.scale.regular2
        F.scale.regular3 F.scale.regular4 ∈
          GCD369CubeHahnRegular.higherOrderIdeal e he := by
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal e he
  let q := Ideal.Quotient.mk I
  have hweight (w : ℕ) (hw : 7 ≤ w) :
      e < (w : ℚ) * F.scale.p := by
    exact hlt.trans_le (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hw) F.scale.hp.le)
  have hkill (w : ℕ) (hw : 7 ≤ w)
      (x : GCD369CubeHahnRegular k) :
      q (F.scale.weightedRegular w x) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (WithTop.coe_lt_coe.mpr (hweight w hw)).trans_le
      (F.scale.weightedRegular_orderTop_lower w x)
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
  have hc2q := hkill 7 (by norm_num) F.c2
  have hc1q := hkill 8 (by norm_num) F.c1
  have hr1q := hkill 10 (by norm_num) F.rho1
  have hr2q := hkill 11 (by norm_num) F.rho2
  have hr3q := hkill 12 (by norm_num) F.rho3
  have hr4q := hkill 13 (by norm_num) F.rho4
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
    let zero := GCD369CubeFaberFullN1
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4 0 0 0 0 0 0 0
    have hq : q full = q zero := by
      dsimp only [full, zero]
      rw [(GCD369CubeFaberFullN_map q _ _ _ _ _ _ _ _ _ _ _ _).1,
        (GCD369CubeFaberFullN_map q _ _ _ _ _ 0 0 0 0 0 0 0).1,
        hdq, hc7q, hc5q, hc4q, hc3q, hc2q, hc1q]
      simp
    have hfull : full = 62208 * F.scale.weightedRegular 10 F.rho1 := by
      apply Subtype.ext
      exact F.scaledFullN1
    have hqfull : q full = 0 := by
      rw [hfull, map_mul, hr1q, mul_zero]
    have hmem : zero ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (hq ▸ hqfull)
    dsimp only [zero] at hmem
    rw [(GCD369CubeFaberFullN_zeroHigh
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).1] at hmem
    exact hmem
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
    let zero := GCD369CubeFaberFullN2
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4 0 0 0 0 0 0 0
    have hq : q full = q zero := by
      dsimp only [full, zero]
      rw [(GCD369CubeFaberFullN_map q _ _ _ _ _ _ _ _ _ _ _ _).2.1,
        (GCD369CubeFaberFullN_map q _ _ _ _ _ 0 0 0 0 0 0 0).2.1,
        hdq, hc7q, hc5q, hc4q, hc3q, hc2q, hc1q]
      simp
    have hfull : full = 186624 * F.scale.weightedRegular 11 F.rho2 := by
      apply Subtype.ext
      exact F.scaledFullN2
    have hqfull : q full = 0 := by
      rw [hfull, map_mul, hr2q, mul_zero]
    have hmem : zero ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (hq ▸ hqfull)
    dsimp only [zero] at hmem
    rw [(GCD369CubeFaberFullN_zeroHigh
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).2.1] at hmem
    exact hmem
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
    let zero := GCD369CubeFaberFullN3
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4 0 0 0 0 0 0 0
    have hq : q full = q zero := by
      dsimp only [full, zero]
      rw [(GCD369CubeFaberFullN_map q _ _ _ _ _ _ _ _ _ _ _ _).2.2.1,
        (GCD369CubeFaberFullN_map q _ _ _ _ _ 0 0 0 0 0 0 0).2.2.1,
        hdq, hc7q, hc5q, hc4q, hc3q, hc2q, hc1q]
      simp
    have hfull : full = 248832 * F.scale.weightedRegular 12 F.rho3 := by
      apply Subtype.ext
      exact F.scaledFullN3
    have hqfull : q full = 0 := by
      rw [hfull, map_mul, hr3q, mul_zero]
    have hmem : zero ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (hq ▸ hqfull)
    dsimp only [zero] at hmem
    rw [(GCD369CubeFaberFullN_zeroHigh
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).2.2.1] at hmem
    exact hmem
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
    let zero := GCD369CubeFaberFullN4
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4 0 0 0 0 0 0 0
    have hq : q full = q zero := by
      dsimp only [full, zero]
      rw [(GCD369CubeFaberFullN_map q _ _ _ _ _ _ _ _ _ _ _ _).2.2.2,
        (GCD369CubeFaberFullN_map q _ _ _ _ _ 0 0 0 0 0 0 0).2.2.2,
        hdq, hc7q, hc5q, hc4q, hc3q, hc2q, hc1q]
      simp
    have hfull : full = 1679616 * F.scale.weightedRegular 13 F.rho4 := by
      apply Subtype.ext
      exact F.scaledFullN4
    have hqfull : q full = 0 := by
      rw [hfull, map_mul, hr4q, mul_zero]
    have hmem : zero ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (hq ▸ hqfull)
    dsimp only [zero] at hmem
    rw [(GCD369CubeFaberFullN_zeroHigh
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4).2.2.2] at hmem
    exact hmem

/-- Below the weight-seven scale, the complete terminal numerator differs
from the zero-load specialization only by terms strictly after the cutoff. -/
theorem fullN5_sub_zeroSpecialized_mem_higherOrderIdeal_of_lt_seven_p
    {k : Type*} [Field k] [CharZero k]
    (F : GCD369CubeHahnFaberPoleData k)
    (e : ℚ) (he : 0 ≤ e) (hlt : e < 7 * F.scale.p)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant 0) :
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
      F.scale.regular3 F.scale.regular4 0 0 0 0 0 0 0 ∈
        GCD369CubeHahnRegular.higherOrderIdeal e he := by
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal e he
  let q := Ideal.Quotient.mk I
  have hweight (w : ℕ) (hw : 7 ≤ w) :
      e < (w : ℚ) * F.scale.p := by
    exact hlt.trans_le (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hw) F.scale.hp.le)
  have hkill (w : ℕ) (hw : 7 ≤ w)
      (x : GCD369CubeHahnRegular k) :
      q (F.scale.weightedRegular w x) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (WithTop.coe_lt_coe.mpr (hweight w hw)).trans_le
      (F.scale.weightedRegular_orderTop_lower w x)
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
  have hc2q := hkill 7 (by norm_num) F.c2
  have hc1q := hkill 8 (by norm_num) F.c1
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
  let zero : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4 0 0 0 0 0 0 0
  have hq : q full = q zero := by
    dsimp only [full, zero]
    rw [GCD369CubeFaberFullN5_map, GCD369CubeFaberFullN5_map,
      hdq, hc7q, hc5q, hc4q, hc3q, hc2q, hc1q]
    simp
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [map_sub, hq, sub_self]

end GCD369CubeHahnFaberPoleData

namespace GCD369CubeHahnCommonCoefficientData

/-- Before the weight-seven load, vanishing through `c3` gives the four
universal zero-load normal rows at the canonical transverse scale. -/
theorem TransverseScale.zeroLoadLeadingRows_before_c2
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0)
    (hearly : 2 * T.delta < 7 * D.faber.scale.p) :
    GCD369CubeNormalRow1
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u = 0 ∧
    GCD369CubeNormalRow2
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v = 0 ∧
    GCD369CubeNormalRow3
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v = 0 ∧
    GCD369CubeNormalRow4
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    D.faber.zeroLoadN_mem_higherOrderIdeal_of_lt_seven_p
      (2 * T.delta) (mul_nonneg (by norm_num) T.hdelta.le)
      hearly hd hc7 hc5 hc4 hc3
  have hz1 :
      (729 * GCD369CubeFaberN1
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4).1.coeff (2 * T.delta) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop h1
  have hz2 :
      (2187 * GCD369CubeFaberN2
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4).1.coeff (2 * T.delta) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop h2
  have hz3 :
      (243 * GCD369CubeFaberN3
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4).1.coeff (2 * T.delta) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop h3
  have hz4 :
      (6561 * GCD369CubeFaberN4
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4).1.coeff (2 * T.delta) = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_orderTop h4
  constructor
  · have hc :
        (729 * GCD369CubeFaberN1
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4).1.coeff (2 * T.delta) =
        -32 * GCD369CubeNormalRow1
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u := by
      convert T.zeroHighN1Coeff using 1
      all_goals norm_num
    rw [hc] at hz1
    exact (mul_eq_zero.mp hz1).resolve_left (by norm_num)
  constructor
  · have hc :
        (2187 * GCD369CubeFaberN2
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4).1.coeff (2 * T.delta) =
        32 * GCD369CubeNormalRow2
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v := by
      convert T.zeroHighN2Coeff using 1
      all_goals norm_num
    rw [hc] at hz2
    exact (mul_eq_zero.mp hz2).resolve_left (by norm_num)
  constructor
  · have hcoeff :
        (243 * GCD369CubeFaberN3
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4).1.coeff (2 * T.delta) =
        (243 : k) *
          (GCD369CubeFaberN3
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4).1.coeff (2 * T.delta) :=
      GCD369CubeHahnRegular.coeff_nat_mul 243 _ _
    rw [hcoeff] at hz3
    have hz3' := (mul_eq_zero.mp hz3).resolve_left (by norm_num)
    have hc :
        (GCD369CubeFaberN3
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4).1.coeff (2 * T.delta) =
        128 * GCD369CubeNormalRow3
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v := by
      convert T.zeroHighN3Coeff using 1
      all_goals norm_num
    rw [hc] at hz3'
    exact (mul_eq_zero.mp hz3').resolve_left (by norm_num)
  · have hc :
        (6561 * GCD369CubeFaberN4
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4).1.coeff (2 * T.delta) =
        32 * GCD369CubeNormalRow4
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v := by
      convert T.zeroHighN4Coeff using 1
      all_goals norm_num
    rw [hc] at hz4
    exact (mul_eq_zero.mp hz4).resolve_left (by norm_num)

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubeHahnFaberPoleData

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- On the singular common-cubic component, if the first possible
weight-seven term starts strictly after the intrinsic cubic term, the latter
is the exact first term of the fifth numerator. -/
theorem fullN5_orderTop_eq_three_delta_of_singular_c2_late
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k)
    (T : D.TransverseScale)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0)
    (r A : k) (hr : r ≠ 0) (hA : A ≠ 0)
    (hu : D.u = -3 * r ^ 2)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r * A)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r ^ 2 * A)
    (hlate : 3 * T.delta < 7 * D.faber.scale.p) :
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
        (↑(3 * T.delta) : WithTop ℚ) := by
  have he : 0 ≤ 3 * T.delta :=
    mul_nonneg (by norm_num) T.hdelta.le
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal (3 * T.delta) he
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let dload : GCD369CubeHahnRegular k :=
    D.faber.scale.weightedRegular 1 D.faber.d
  let C : GCD369CubeHahnRegular k :=
    GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU
  let Main : GCD369CubeHahnRegular k := 839808 * H ^ 3 * C
  let N : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4 dload
    (D.faber.scale.weightedRegular 2 D.faber.c7)
    (D.faber.scale.weightedRegular 4 D.faber.c5)
    (D.faber.scale.weightedRegular 5 D.faber.c4)
    (D.faber.scale.weightedRegular 6 D.faber.c3)
    (D.faber.scale.weightedRegular 7 D.faber.c2)
    (D.faber.scale.weightedRegular 8 D.faber.c1)
  let N0 : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4 0 0 0 0 0 0 0
  have hdload : dload = 0 := by
    dsimp only [dload]
    rw [hd]
    apply Subtype.ext
    simp [GCD369CubeHahnPoleScale.weightedRegular]
  have hCcoeff : GCD369CubeHahnRegular.constantCoeff C =
      -3 * r ^ 2 * A ^ 3 := by
    dsimp only [C]
    rw [GCD369CubeNormalRow5Cubic_map,
      D.constantCoeff_cubicU, hX, hY, hZ, hu]
    exact GCD369CubeNormalRow5Cubic_doubleRoot r A
  have hfactorCoeff :
      GCD369CubeHahnRegular.constantCoeff (839808 * C) ≠ 0 := by
    rw [map_mul, map_ofNat, hCcoeff]
    exact mul_ne_zero (by norm_num)
      (mul_ne_zero
        (mul_ne_zero (by norm_num) (pow_ne_zero 2 hr))
        (pow_ne_zero 3 hA))
  have hMainFactor : Main = H ^ 3 * (839808 * C) := by
    dsimp only [Main]
    ring
  have hMainOrder : Main.1.orderTop =
      (↑(3 * T.delta) : WithTop ℚ) := by
    rw [hMainFactor]
    convert
      (GCD369CubeHahnRegular.orderTop_monomial_pow_mul_eq_of_constantCoeff_ne
        T.delta T.hdelta 3 (839808 * C) hfactorCoeff) using 1
    all_goals norm_num [H]
  obtain ⟨hzero1, hzero2, _hzero3, _hzero4⟩ :=
    D.faber.zeroLoadN_mem_higherOrderIdeal_of_lt_seven_p
      (3 * T.delta) he hlate hd hc7 hc5 hc4 hc3
  change _ ∈ I at hzero1 hzero2
  have hzero1D :
      GCD369CubeFaberD1
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 0 ∈ I := by
    simpa [GCD369CubeFaberD1] using hzero1
  have hzero2D :
      GCD369CubeFaberD2
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 0 ∈ I := by
    simpa [GCD369CubeFaberD2] using hzero2
  have hterm1 :
      24 * D.cubicU ^ 2 *
        GCD369CubeFaberD1
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4 0 ∈ I :=
    I.mul_mem_left _ hzero1D
  have hterm2 :
      (-24 * D.cubicV) *
        GCD369CubeFaberD2
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4 0 ∈ I :=
    I.mul_mem_left _ hzero2D
  obtain ⟨Rem, _hRemCoeff, hrelation⟩ := T.dTerminalRelation
  have hrelation' : N0 =
      24 * D.cubicU ^ 2 *
          GCD369CubeFaberD1
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4 0 -
        24 * D.cubicV *
          GCD369CubeFaberD2
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4 0 + Main := by
    have h := hrelation
    have hdload' : D.faber.scale.weightedRegular 1 D.faber.d = 0 := by
      simpa only [dload] using hdload
    rw [hdload'] at h
    simpa only [N0, H, C, Main, zero_mul, add_zero] using h
  have hN0Main : N0 - Main ∈ I := by
    have heq : N0 - Main =
        (24 * D.cubicU ^ 2 *
          GCD369CubeFaberD1
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4 0) +
        ((-24 * D.cubicV) *
          GCD369CubeFaberD2
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4 0) := by
      rw [hrelation']
      ring
    rw [heq]
    exact I.add_mem hterm1 hterm2
  have hNdiff : N - N0 ∈ I := by
    simpa only [N, N0, dload] using
      D.faber.fullN5_sub_zeroSpecialized_mem_higherOrderIdeal_of_lt_seven_p
        (3 * T.delta) he hlate hd hc7 hc5 hc4 hc3
  have hNMain : N - Main ∈ I := by
    have heq : N - Main = (N - N0) + (N0 - Main) := by ring
    rw [heq]
    exact I.add_mem hNdiff hN0Main
  have hsum : N = Main + (N - Main) := by ring
  have hltOrder : Main.1.orderTop < (N - Main).1.orderTop := by
    rw [hMainOrder]
    exact hNMain
  change N.1.orderTop = (↑(3 * T.delta) : WithTop ℚ)
  rw [hsum]
  change (Main.1 + (N - Main).1).orderTop = _
  rw [HahnSeries.orderTop_add_eq_left hltOrder, hMainOrder]

end GCD369CubeHahnFaberPoleData

namespace GCD369CubePolynomialSource

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Source-facing weight-seven late-cell contradiction once the singular
transverse residue is in its standard double-root chart. -/
theorem infinity_c2_singular_late_inconsistent_of_parametrization
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hdP : S.faberConstantParameters.d = 0)
    (hc7P : S.faberConstantParameters.c7 = 0)
    (hc5P : S.faberConstantParameters.c5 = 0)
    (hc4P : S.faberConstantParameters.c4 = 0)
    (hc3P : S.faberConstantParameters.c3 = 0)
    (hdisc :
      4 * (S.infinityCommonCoefficientData hsdegree).u ^ 3 +
        27 * (S.infinityCommonCoefficientData hsdegree).v ^ 2 = 0)
    (r A : k) (hr : r ≠ 0) (hA : A ≠ 0)
    (hu : (S.infinityCommonCoefficientData hsdegree).u = -3 * r ^ 2)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r * A)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r ^ 2 * A)
    (hlate : 3 * T.delta <
      7 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p) :
    False := by
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let D := S.infinityCommonCoefficientData hsdegree
  let P := S.faberConstantParameters
  obtain ⟨hdraw, hc7raw, hc5raw, hc4raw, hc3raw, _hc2, _hc1,
      _hr1, _hr2, _hr3, _hr4⟩ :=
    S.infinityFaberPoleData_constant_loads hpole
  have hd : D.faber.d = GCD369CubeHahnRegular.constant 0 := by
    have h : D.faber.d = GCD369CubeHahnRegular.constant P.d := by
      simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree]
        using hdraw
    rw [hdP] at h
    exact h
  have hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0 := by
    have h : D.faber.c7 = GCD369CubeHahnRegular.constant P.c7 := by
      simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree]
        using hc7raw
    rw [hc7P] at h
    exact h
  have hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0 := by
    have h : D.faber.c5 = GCD369CubeHahnRegular.constant P.c5 := by
      simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree]
        using hc5raw
    rw [hc5P] at h
    exact h
  have hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0 := by
    have h : D.faber.c4 = GCD369CubeHahnRegular.constant P.c4 := by
      simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree]
        using hc4raw
    rw [hc4P] at h
    exact h
  have hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0 := by
    have h : D.faber.c3 = GCD369CubeHahnRegular.constant P.c3 := by
      simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree]
        using hc3raw
    rw [hc3P] at h
    exact h
  have hNorder :=
    GCD369CubeHahnFaberPoleData.fullN5_orderTop_eq_three_delta_of_singular_c2_late
      D T hd hc7 hc5 hc4 hc3 r A hr hA hu hX hY hZ hlate
  have hterminalOrder :
      (GCD369CubeFaberR5
        (D.faber.scale.regular0 : HahnSeries ℚ k)
        D.faber.scale.regular1 D.faber.scale.regular2
        D.faber.scale.regular3 D.faber.scale.regular4
        (D.faber.scale.weightedRegular 1 D.faber.d)
        (D.faber.scale.weightedRegular 2 D.faber.c7)
        (D.faber.scale.weightedRegular 4 D.faber.c5)
        (D.faber.scale.weightedRegular 5 D.faber.c4)
        (D.faber.scale.weightedRegular 6 D.faber.c3)
        (D.faber.scale.weightedRegular 7 D.faber.c2)
        (D.faber.scale.weightedRegular 8 D.faber.c1)).order =
          3 * T.delta :=
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
      (3 * T.delta) hNorder
  have hscaled :
      GCD369CubeFaberR5
        (D.faber.scale.regular0 : HahnSeries ℚ k)
        D.faber.scale.regular1 D.faber.scale.regular2
        D.faber.scale.regular3 D.faber.scale.regular4
        (D.faber.scale.weightedRegular 1 D.faber.d)
        (D.faber.scale.weightedRegular 2 D.faber.c7)
        (D.faber.scale.weightedRegular 4 D.faber.c5)
        (D.faber.scale.weightedRegular 5 D.faber.c4)
        (D.faber.scale.weightedRegular 6 D.faber.c3)
        (D.faber.scale.weightedRegular 7 D.faber.c2)
        (D.faber.scale.weightedRegular 8 D.faber.c1) =
      D.faber.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant := by
    have hs := S.infinityFaberPoleData_scaled_terminal hpole
    change _ = D.faber.scale.t ^ 14 *
      GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant at hs
    exact hs
  have hscaledOrder :
      (D.faber.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order =
          3 * T.delta := by
    rw [← hscaled]
    exact hterminalOrder
  apply S.infinity_terminal_three_delta_not_before_load_of_singular
    hsdegree T 7 (by norm_num) hdisc hlate
  simpa only [hpole, D, S.infinityCommonCoefficientData_faber hsdegree]
    using hscaledOrder

/-- After `d=c7=c5=c4=c3=0`, the strict region `3δ < 7p` is inconsistent for every
constant-core infinity source. -/
theorem infinity_c2_singular_late_inconsistent
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hdP : S.faberConstantParameters.d = 0)
    (hc7P : S.faberConstantParameters.c7 = 0)
    (hc5P : S.faberConstantParameters.c5 = 0)
    (hc4P : S.faberConstantParameters.c4 = 0)
    (hc3P : S.faberConstantParameters.c3 = 0)
    (hlate : 3 * T.delta <
      7 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p) :
    False := by
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let D := S.infinityCommonCoefficientData hsdegree
  let P := S.faberConstantParameters
  obtain ⟨hdraw, hc7raw, hc5raw, hc4raw, hc3raw, _hc2, _hc1,
      _hr1, _hr2, _hr3, _hr4⟩ :=
    S.infinityFaberPoleData_constant_loads hpole
  have hd : D.faber.d = GCD369CubeHahnRegular.constant 0 := by
    have h : D.faber.d = GCD369CubeHahnRegular.constant P.d := by
      simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree]
        using hdraw
    rw [hdP] at h
    exact h
  have hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0 := by
    have h : D.faber.c7 = GCD369CubeHahnRegular.constant P.c7 := by
      simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree]
        using hc7raw
    rw [hc7P] at h
    exact h
  have hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0 := by
    have h : D.faber.c5 = GCD369CubeHahnRegular.constant P.c5 := by
      simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree]
        using hc5raw
    rw [hc5P] at h
    exact h
  have hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0 := by
    have h : D.faber.c4 = GCD369CubeHahnRegular.constant P.c4 := by
      simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree]
        using hc4raw
    rw [hc4P] at h
    exact h
  have hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0 := by
    have h : D.faber.c3 = GCD369CubeHahnRegular.constant P.c3 := by
      simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree]
        using hc3raw
    rw [hc3P] at h
    exact h
  have hearly : 2 * T.delta < 7 * D.faber.scale.p := by
    linarith [T.hdelta]
  obtain ⟨h1, h2, h3, h4⟩ :=
    T.zeroLoadLeadingRows_before_c2 hd hc7 hc5 hc4 hc3 hearly
  obtain ⟨r, hA, hu, hv, hY, hZ⟩ :=
    GCD369CubeZeroLoadNormal_parametrization
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn)
      D.u D.v T.hleading h1 h2 h3 h4
  have hr : r ≠ 0 := by
    intro hr0
    have hu0 : D.u = 0 := by rw [hu, hr0]; norm_num
    have hv0 : D.v = 0 := by rw [hv, hr0]; norm_num
    exact D.hprojective.elim (fun h => h hu0) (fun h => h hv0)
  have hdisc : 4 * D.u ^ 3 + 27 * D.v ^ 2 = 0 := by
    rw [hu, hv]
    ring
  exact S.infinity_c2_singular_late_inconsistent_of_parametrization
    hsdegree T hdP hc7P hc5P hc4P hc3P hdisc r
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      hr hA hu rfl hY hZ hlate

/-- Target-normalized source wrapper: canonical parameter uniqueness supplies
`d=c3=0`, so only the genuine earlier load vanishings are assumed. -/
theorem targetNormalized_infinity_c2_singular_late_inconsistent
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (hd0 : S.faberConstantParameters.d = 0)
    (T : let U := S.targetNormalizedSource
      (U.infinityCommonCoefficientData (by
        simpa [U, targetNormalizedSource] using hsdegree)).TransverseScale)
    (hc70 : S.targetNormalizedSource.faberConstantParameters.c7 = 0)
    (hc50 : S.targetNormalizedSource.faberConstantParameters.c5 = 0)
    (hc40 : S.targetNormalizedSource.faberConstantParameters.c4 = 0)
    (hlate : let U := S.targetNormalizedSource
      let hsdegreeU : U.s.natDegree = 0 := by
        simpa [U, targetNormalizedSource] using hsdegree
      3 * T.delta <
        7 * (U.infinityCommonCoefficientData hsdegreeU).faber.scale.p) :
    False := by
  let U := S.targetNormalizedSource
  let Q := U.faberConstantParameters
  have hsdegreeU : U.s.natDegree = 0 := by
    simpa [U, targetNormalizedSource] using hsdegree
  obtain ⟨hQd, _hQc7, _hQc6, _hQc5, _hQc4, hQc3,
      _hQc2, _hQc1, _hQc0⟩ :=
    S.targetNormalizedCanonicalParameters hd0
  apply U.infinity_c2_singular_late_inconsistent hsdegreeU T
  · simpa only [Q, U] using hQd
  · simpa only [U] using hc70
  · simpa only [U] using hc50
  · simpa only [U] using hc40
  · simpa only [Q, U] using hQc3
  · exact hlate

end GCD369CubePolynomialSource

#print axioms
  GCD369CubeHahnFaberPoleData.zeroLoadN_mem_higherOrderIdeal_of_lt_seven_p
#print axioms
  GCD369CubeHahnFaberPoleData.fullN5_sub_zeroSpecialized_mem_higherOrderIdeal_of_lt_seven_p
#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.zeroLoadLeadingRows_before_c2
#print axioms
  GCD369CubeHahnFaberPoleData.fullN5_orderTop_eq_three_delta_of_singular_c2_late
#print axioms
  GCD369CubePolynomialSource.infinity_c2_singular_late_inconsistent
#print axioms
  GCD369CubePolynomialSource.targetNormalized_infinity_c2_singular_late_inconsistent
