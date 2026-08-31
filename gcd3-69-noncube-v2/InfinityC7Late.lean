import InfinitySingularDegree

/-! # The singular late branch for the first post-`d` load

When `d = 0` and the weight-two `c7` load starts after the intrinsic cubic
transverse term, every target load is invisible through order `3 * delta`.
This file isolates that order comparison for the lightweight infinity
coefficient packet.
-/

noncomputable section

namespace GCD369CubeHahnFaberPoleData

/-- With `d = 0`, if the weight-two load lies after a cutoff, then the first
two zero-load numerators vanish strictly beyond that cutoff. -/
theorem zeroLoadN12_mem_higherOrderIdeal_of_lt_two_p
    {k : Type*} [Field k] [CharZero k]
    (F : GCD369CubeHahnFaberPoleData k)
    (e : ℚ) (he : 0 ≤ e) (hlt : e < 2 * F.scale.p)
    (C7 C5 C4 C3 C2 C1 R1 R2 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : F.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : F.rho2 = GCD369CubeHahnRegular.constant R2) :
    GCD369CubeFaberD1
        F.scale.regular0 F.scale.regular1 F.scale.regular2
        F.scale.regular3 F.scale.regular4 0 ∈
          GCD369CubeHahnRegular.higherOrderIdeal e he ∧
    GCD369CubeFaberD2
        F.scale.regular0 F.scale.regular1 F.scale.regular2
        F.scale.regular3 F.scale.regular4 0 ∈
          GCD369CubeHahnRegular.higherOrderIdeal e he := by
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal e he
  let q := Ideal.Quotient.mk I
  have hweight (w : ℕ) (hw : 2 ≤ w) : e < (w : ℚ) * F.scale.p := by
    have hwp : 2 * F.scale.p ≤ (w : ℚ) * F.scale.p := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hw
      · exact F.scale.hp.le
    exact hlt.trans_le hwp
  have hdq : q (F.scale.weightedRegular 1 F.d) = 0 := by
    rw [hd]
    have hz : F.scale.weightedRegular 1
        (GCD369CubeHahnRegular.constant (0 : k)) = 0 := by
      apply Subtype.ext
      simp [GCD369CubeHahnPoleScale.weightedRegular]
    rw [hz, map_zero]
  have hc7q : q (F.scale.weightedRegular 2 F.c7) = 0 := by
    rw [hc7, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 2 C7 he (hweight 2 (by norm_num))
  have hc5q : q (F.scale.weightedRegular 4 F.c5) = 0 := by
    rw [hc5, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 4 C5 he (hweight 4 (by norm_num))
  have hc4q : q (F.scale.weightedRegular 5 F.c4) = 0 := by
    rw [hc4, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 5 C4 he (hweight 5 (by norm_num))
  have hc3q : q (F.scale.weightedRegular 6 F.c3) = 0 := by
    rw [hc3, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 6 C3 he (hweight 6 (by norm_num))
  have hc2q : q (F.scale.weightedRegular 7 F.c2) = 0 := by
    rw [hc2, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 7 C2 he (hweight 7 (by norm_num))
  have hc1q : q (F.scale.weightedRegular 8 F.c1) = 0 := by
    rw [hc1, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 8 C1 he (hweight 8 (by norm_num))
  have hr1q : q (F.scale.weightedRegular 10 F.rho1) = 0 := by
    rw [hr1, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 10 R1 he (hweight 10 (by norm_num))
  have hr2q : q (F.scale.weightedRegular 11 F.rho2) = 0 := by
    rw [hr2, Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale 11 R2 he (hweight 11 (by norm_num))
  let full1 := GCD369CubeFaberFullN1
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
    (F.scale.weightedRegular 1 F.d)
    (F.scale.weightedRegular 2 F.c7)
    (F.scale.weightedRegular 4 F.c5)
    (F.scale.weightedRegular 5 F.c4)
    (F.scale.weightedRegular 6 F.c3)
    (F.scale.weightedRegular 7 F.c2)
    (F.scale.weightedRegular 8 F.c1)
  let full2 := GCD369CubeFaberFullN2
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
    (F.scale.weightedRegular 1 F.d)
    (F.scale.weightedRegular 2 F.c7)
    (F.scale.weightedRegular 4 F.c5)
    (F.scale.weightedRegular 5 F.c4)
    (F.scale.weightedRegular 6 F.c3)
    (F.scale.weightedRegular 7 F.c2)
    (F.scale.weightedRegular 8 F.c1)
  let zero1 := GCD369CubeFaberD1
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4 0
  let zero2 := GCD369CubeFaberD2
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4 0
  have hq1 : q full1 = q zero1 := by
    dsimp only [full1, zero1]
    rw [(GCD369CubeFaberFullN_map q _ _ _ _ _ _ _ _ _ _ _ _).1,
      (GCD369CubeFaberD_map q _ _ _ _ _ _).1,
      hdq, hc7q, hc5q, hc4q, hc3q, hc2q, hc1q]
    exact (GCD369CubeFaberFullN_d_specialize _ _ _ _ _ 0).1
  have hq2 : q full2 = q zero2 := by
    dsimp only [full2, zero2]
    rw [(GCD369CubeFaberFullN_map q _ _ _ _ _ _ _ _ _ _ _ _).2.1,
      (GCD369CubeFaberD_map q _ _ _ _ _ _).2.1,
      hdq, hc7q, hc5q, hc4q, hc3q, hc2q, hc1q]
    exact (GCD369CubeFaberFullN_d_specialize _ _ _ _ _ 0).2.1
  have hfull1 : full1 = 62208 * F.scale.weightedRegular 10 F.rho1 := by
    apply Subtype.ext
    exact F.scaledFullN1
  have hfull2 : full2 = 186624 * F.scale.weightedRegular 11 F.rho2 := by
    apply Subtype.ext
    exact F.scaledFullN2
  have hqfull1 : q full1 = 0 := by
    rw [hfull1, map_mul, hr1q, mul_zero]
  have hqfull2 : q full2 = 0 := by
    rw [hfull2, map_mul, hr2q, mul_zero]
  constructor
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact hq1 ▸ hqfull1
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact hq2 ▸ hqfull2

/-- If `d = 0` and `2p` is after a cutoff, all active-load contributions to
the fifth numerator vanish modulo that cutoff. -/
theorem fullN5_sub_zeroSpecialized_mem_higherOrderIdeal_of_lt_two_p
    {k : Type*} [Field k] [CharZero k]
    (F : GCD369CubeHahnFaberPoleData k)
    (e : ℚ) (he : 0 ≤ e) (hlt : e < 2 * F.scale.p)
    (C7 C5 C4 C3 C2 C1 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
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
      F.scale.regular3 F.scale.regular4 0 0 0 0 0 0 0 ∈
        GCD369CubeHahnRegular.higherOrderIdeal e he := by
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal e he
  let q := Ideal.Quotient.mk I
  have hweight (w : ℕ) (hw : 2 ≤ w) : e < (w : ℚ) * F.scale.p := by
    exact hlt.trans_le (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hw) F.scale.hp.le)
  have hdq : q (F.scale.weightedRegular 1 F.d) = 0 := by
    rw [hd]
    have hz : F.scale.weightedRegular 1
        (GCD369CubeHahnRegular.constant (0 : k)) = 0 := by
      apply Subtype.ext
      simp [GCD369CubeHahnPoleScale.weightedRegular]
    rw [hz, map_zero]
  have hq (w : ℕ) (C : k) (hw : 2 ≤ w) :
      q (F.scale.weightedRegular w (GCD369CubeHahnRegular.constant C)) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact GCD369CubeHahnRegular.weightedRegular_constant_mem_higherOrderIdeal
      F.scale w C he (hweight w hw)
  have hc7q : q (F.scale.weightedRegular 2 F.c7) = 0 := by rw [hc7]; exact hq 2 C7 (by norm_num)
  have hc5q : q (F.scale.weightedRegular 4 F.c5) = 0 := by rw [hc5]; exact hq 4 C5 (by norm_num)
  have hc4q : q (F.scale.weightedRegular 5 F.c4) = 0 := by rw [hc4]; exact hq 5 C4 (by norm_num)
  have hc3q : q (F.scale.weightedRegular 6 F.c3) = 0 := by rw [hc3]; exact hq 6 C3 (by norm_num)
  have hc2q : q (F.scale.weightedRegular 7 F.c2) = 0 := by rw [hc2]; exact hq 7 C2 (by norm_num)
  have hc1q : q (F.scale.weightedRegular 8 F.c1) = 0 := by rw [hc1]; exact hq 8 C1 (by norm_num)
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
  have hqeq : q full = q zero := by
    dsimp only [full, zero]
    rw [GCD369CubeFaberFullN5_map, GCD369CubeFaberFullN5_map,
      hdq, hc7q, hc5q, hc4q, hc3q, hc2q, hc1q]
    simp
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [map_sub, hqeq, sub_self]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- On the singular common-cubic component, if the first possible `c7` term
starts strictly after the intrinsic cubic term, then the latter is the exact
first term of the fifth numerator. -/
theorem fullN5_orderTop_eq_three_delta_of_singular_c7_late
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k)
    (T : D.TransverseScale)
    (C7 C5 C4 C3 C2 C1 R1 R2 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (r A : k) (hr : r ≠ 0) (hA : A ≠ 0)
    (hu : D.u = -3 * r ^ 2)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r * A)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r ^ 2 * A)
    (hlate : 3 * T.delta < 2 * D.faber.scale.p) :
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
  obtain ⟨hzero1, hzero2⟩ :=
    D.faber.zeroLoadN12_mem_higherOrderIdeal_of_lt_two_p
      (3 * T.delta) he hlate C7 C5 C4 C3 C2 C1 R1 R2
      hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2
  change _ ∈ I at hzero1 hzero2
  have hterm1 :
      24 * D.cubicU ^ 2 *
        GCD369CubeFaberD1
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4 0 ∈ I :=
    I.mul_mem_left _ hzero1
  have hterm2 :
      (-24 * D.cubicV) *
        GCD369CubeFaberD2
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4 0 ∈ I :=
    I.mul_mem_left _ hzero2
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
      D.faber.fullN5_sub_zeroSpecialized_mem_higherOrderIdeal_of_lt_two_p
        (3 * T.delta) he hlate C7 C5 C4 C3 C2 C1
        hd hc7 hc5 hc4 hc3 hc2 hc1
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
/-- Source-facing late-cell contradiction once the singular transverse
residue has been put in its standard double-root chart. -/
theorem infinity_c7_singular_late_inconsistent_of_parametrization
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hdP : S.faberConstantParameters.d = 0)
    (hdisc :
      4 * (S.infinityCommonCoefficientData hsdegree).u ^ 3 +
        27 * (S.infinityCommonCoefficientData hsdegree).v ^ 2 = 0)
    (r A : k) (hr : r ≠ 0) (hA : A ≠ 0)
    (hu : (S.infinityCommonCoefficientData hsdegree).u = -3 * r ^ 2)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r * A)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r ^ 2 * A)
    (hlate : 3 * T.delta <
      2 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p) :
    False := by
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let D := S.infinityCommonCoefficientData hsdegree
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  obtain ⟨hd, hc7, hc5, hc4, hc3, hc2, hc1,
      hr1, hr2, _hr3, _hr4⟩ :=
    S.infinityFaberPoleData_constant_loads hpole
  have hdD : D.faber.d = GCD369CubeHahnRegular.constant 0 := by
    have hd0 : D.faber.d = GCD369CubeHahnRegular.constant P.d := by
      simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree]
        using hd
    rw [hdP] at hd0
    exact hd0
  have hc7D : D.faber.c7 = GCD369CubeHahnRegular.constant P.c7 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc7
  have hc5D : D.faber.c5 = GCD369CubeHahnRegular.constant P.c5 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc5
  have hc4D : D.faber.c4 = GCD369CubeHahnRegular.constant P.c4 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc4
  have hc3D : D.faber.c3 = GCD369CubeHahnRegular.constant P.c3 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc3
  have hc2D : D.faber.c2 = GCD369CubeHahnRegular.constant P.c2 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc2
  have hc1D : D.faber.c1 = GCD369CubeHahnRegular.constant P.c1 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hc1
  have hr1D : D.faber.rho1 = GCD369CubeHahnRegular.constant R.rho1 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree] using hr1
  have hr2D : D.faber.rho2 = GCD369CubeHahnRegular.constant R.rho2 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree] using hr2
  have hNorder :=
    GCD369CubeHahnFaberPoleData.fullN5_orderTop_eq_three_delta_of_singular_c7_late
      D T P.c7 P.c5 P.c4 P.c3 P.c2 P.c1 R.rho1 R.rho2
      hdD hc7D hc5D hc4D hc3D hc2D hc1D hr1D hr2D
      r A hr hA hu hX hY hZ hlate
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
    hsdegree T 2 (by norm_num) hdisc hlate
  simpa only [hpole, D, S.infinityCommonCoefficientData_faber hsdegree]
    using hscaledOrder

end GCD369CubePolynomialSource

#print axioms
  GCD369CubeHahnFaberPoleData.fullN5_orderTop_eq_three_delta_of_singular_c7_late
#print axioms
  GCD369CubePolynomialSource.infinity_c7_singular_late_inconsistent_of_parametrization
