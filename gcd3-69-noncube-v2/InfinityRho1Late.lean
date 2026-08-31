import InfinityC1Late
import FiniteRho1EarlyNormal

/-! # The strict-late weight-ten rho1 cell at infinity

After `d=c7=c5=c4=c3=c2=c1=0`, rho1 is the first remaining load.  Since
rho1 is absent from `FullN5`, when `3δ < 10p` the intrinsic cubic term is
the exact first term of the terminal numerator, contradicting the singular
constant-core degree lattice.
-/

noncomputable section

namespace GCD369CubeHahnFaberPoleData

/-- Below weight ten the first two zero-high numerators vanish strictly
beyond the chosen cutoff. -/
theorem zeroLoadN12_mem_higherOrderIdeal_before_rho1
    {k : Type*} [Field k] [CharZero k]
    (F : GCD369CubeHahnFaberPoleData k)
    (e : ℚ) (he : 0 ≤ e) (hlt : e < 10 * F.scale.p)
    (hd : F.d = 0) (hc7 : F.c7 = 0) (hc5 : F.c5 = 0)
    (hc4 : F.c4 = 0) (hc3 : F.c3 = 0) (hc2 : F.c2 = 0)
    (hc1 : F.c1 = 0) :
    729 * GCD369CubeFaberN1
        F.scale.regular0 F.scale.regular1 F.scale.regular2
        F.scale.regular3 F.scale.regular4 ∈
          GCD369CubeHahnRegular.higherOrderIdeal e he ∧
    2187 * GCD369CubeFaberN2
        F.scale.regular0 F.scale.regular1 F.scale.regular2
        F.scale.regular3 F.scale.regular4 ∈
          GCD369CubeHahnRegular.higherOrderIdeal e he := by
  let e' : ℚ := (e + 10 * F.scale.p) / 2
  have hee' : e < e' := by dsimp only [e']; linarith
  have he' : 0 ≤ e' := le_trans he hee'.le
  have he'lt : e' < 10 * F.scale.p := by dsimp only [e']; linarith
  have horder
      (N : GCD369CubeHahnRegular k)
      (hz : ∀ q : ℚ, 0 ≤ q → q < 10 * F.scale.p → N.1.coeff q = 0) :
      (↑e : WithTop ℚ) < N.1.orderTop := by
    have hle : (↑e' : WithTop ℚ) ≤ N.1.orderTop := by
      rw [HahnSeries.le_orderTop_iff_forall]
      intro q hq
      have hqe' : q < e' := WithTop.coe_lt_coe.mp hq
      by_cases hq0 : 0 ≤ q
      · exact hz q hq0 (hqe'.trans he'lt)
      · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg N
          (lt_of_not_ge hq0)
    exact (WithTop.coe_lt_coe.mpr hee').trans_le hle
  constructor
  · apply horder
    intro q hq0 hq10
    exact (F.zeroHighNCoeff_zero_before_rho1
      hd hc7 hc5 hc4 hc3 hc2 hc1 q hq0 hq10).1
  · apply horder
    intro q hq0 hq10
    exact (F.zeroHighNCoeff_zero_before_rho1
      hd hc7 hc5 hc4 hc3 hc2 hc1 q hq0 hq10).2.1

/-- Once all seven source loads vanish, `FullN5` is literally its zero-load
specialization; target first integrals, including rho1, do not occur in it. -/
theorem fullN5_eq_zeroSpecialized_before_rho1
    {k : Type*} [Field k] [CharZero k]
    (F : GCD369CubeHahnFaberPoleData k)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant 0)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant 0) :
    GCD369CubeFaberFullN5
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4
      (F.scale.weightedRegular 1 F.d)
      (F.scale.weightedRegular 2 F.c7)
      (F.scale.weightedRegular 4 F.c5)
      (F.scale.weightedRegular 5 F.c4)
      (F.scale.weightedRegular 6 F.c3)
      (F.scale.weightedRegular 7 F.c2)
      (F.scale.weightedRegular 8 F.c1) =
    GCD369CubeFaberFullN5
      F.scale.regular0 F.scale.regular1 F.scale.regular2
      F.scale.regular3 F.scale.regular4 0 0 0 0 0 0 0 := by
  have hzeroWeighted (w : ℕ) (x : GCD369CubeHahnRegular k)
      (hx : x = GCD369CubeHahnRegular.constant 0) :
      F.scale.weightedRegular w x = 0 := by
    rw [hx]
    apply Subtype.ext
    simp [GCD369CubeHahnPoleScale.weightedRegular]
  rw [hzeroWeighted 1 F.d hd, hzeroWeighted 2 F.c7 hc7,
    hzeroWeighted 4 F.c5 hc5, hzeroWeighted 5 F.c4 hc4,
    hzeroWeighted 6 F.c3 hc3, hzeroWeighted 7 F.c2 hc2,
    hzeroWeighted 8 F.c1 hc1]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- In the strict-late rho1 cell the intrinsic cubic term has exact terminal
order `3δ`. -/
theorem fullN5_orderTop_eq_three_delta_of_singular_rho1_late
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k)
    (T : D.TransverseScale)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant 0)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant 0)
    (r A : k) (hr : r ≠ 0) (hA : A ≠ 0)
    (hu : D.u = -3 * r ^ 2)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r * A)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r ^ 2 * A)
    (hlate : 3 * T.delta < 10 * D.faber.scale.p) :
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
  let C : GCD369CubeHahnRegular k :=
    GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU
  let Main : GCD369CubeHahnRegular k := 839808 * H ^ 3 * C
  let N : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
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
  let N0 : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4 0 0 0 0 0 0 0
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
  have hd0 : D.faber.d = 0 := by simpa using hd
  have hc70 : D.faber.c7 = 0 := by simpa using hc7
  have hc50 : D.faber.c5 = 0 := by simpa using hc5
  have hc40 : D.faber.c4 = 0 := by simpa using hc4
  have hc30 : D.faber.c3 = 0 := by simpa using hc3
  have hc20 : D.faber.c2 = 0 := by simpa using hc2
  have hc10 : D.faber.c1 = 0 := by simpa using hc1
  obtain ⟨hzero1, hzero2⟩ :=
    D.faber.zeroLoadN12_mem_higherOrderIdeal_before_rho1
      (3 * T.delta) he hlate hd0 hc70 hc50 hc40 hc30 hc20 hc10
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
    have hdload : D.faber.scale.weightedRegular 1 D.faber.d = 0 := by
      rw [hd]
      apply Subtype.ext
      simp [GCD369CubeHahnPoleScale.weightedRegular]
    rw [hdload] at h
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
  have hNN0 : N = N0 := by
    simpa only [N, N0] using
      D.faber.fullN5_eq_zeroSpecialized_before_rho1
        hd hc7 hc5 hc4 hc3 hc2 hc1
  have hNMain : N - Main ∈ I := by simpa only [hNN0] using hN0Main
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
/-- Source-facing strict-late rho1 contradiction after choosing the standard
double-root chart of the singular transverse residue. -/
theorem infinity_rho1_singular_late_inconsistent_of_parametrization
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hdP : S.faberConstantParameters.d = 0)
    (hc7P : S.faberConstantParameters.c7 = 0)
    (hc5P : S.faberConstantParameters.c5 = 0)
    (hc4P : S.faberConstantParameters.c4 = 0)
    (hc3P : S.faberConstantParameters.c3 = 0)
    (hc2P : S.faberConstantParameters.c2 = 0)
    (hc1P : S.faberConstantParameters.c1 = 0)
    (hdisc :
      4 * (S.infinityCommonCoefficientData hsdegree).u ^ 3 +
        27 * (S.infinityCommonCoefficientData hsdegree).v ^ 2 = 0)
    (r A : k) (hr : r ≠ 0) (hA : A ≠ 0)
    (hu : (S.infinityCommonCoefficientData hsdegree).u = -3 * r ^ 2)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r * A)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r ^ 2 * A)
    (hlate : 3 * T.delta <
      10 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p) :
    False := by
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let D := S.infinityCommonCoefficientData hsdegree
  let P := S.faberConstantParameters
  obtain ⟨hdraw, hc7raw, hc5raw, hc4raw, hc3raw, hc2raw, hc1raw,
      _hr1, _hr2, _hr3, _hr4⟩ :=
    S.infinityFaberPoleData_constant_loads hpole
  have hd : D.faber.d = GCD369CubeHahnRegular.constant 0 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree,
      hdP] using hdraw
  have hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree,
      hc7P] using hc7raw
  have hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree,
      hc5P] using hc5raw
  have hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree,
      hc4P] using hc4raw
  have hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree,
      hc3P] using hc3raw
  have hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant 0 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree,
      hc2P] using hc2raw
  have hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant 0 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree,
      hc1P] using hc1raw
  have hNorder :=
    GCD369CubeHahnFaberPoleData.fullN5_orderTop_eq_three_delta_of_singular_rho1_late
      D T hd hc7 hc5 hc4 hc3 hc2 hc1
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
    hsdegree T 10 (by norm_num) hdisc hlate
  simpa only [hpole, D, S.infinityCommonCoefficientData_faber hsdegree]
    using hscaledOrder

/-- With all source loads through c1 zero, the strict region `3δ < 10p`
is impossible for a constant-core infinity source. -/
theorem infinity_rho1_singular_late_inconsistent
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hdP : S.faberConstantParameters.d = 0)
    (hc7P : S.faberConstantParameters.c7 = 0)
    (hc5P : S.faberConstantParameters.c5 = 0)
    (hc4P : S.faberConstantParameters.c4 = 0)
    (hc3P : S.faberConstantParameters.c3 = 0)
    (hc2P : S.faberConstantParameters.c2 = 0)
    (hc1P : S.faberConstantParameters.c1 = 0)
    (hlate : 3 * T.delta <
      10 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p) :
    False := by
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let D := S.infinityCommonCoefficientData hsdegree
  let P := S.faberConstantParameters
  obtain ⟨hdraw, hc7raw, hc5raw, hc4raw, hc3raw, hc2raw, _hc1,
      _hr1, _hr2, _hr3, _hr4⟩ :=
    S.infinityFaberPoleData_constant_loads hpole
  have hd : D.faber.d = GCD369CubeHahnRegular.constant 0 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree,
      hdP] using hdraw
  have hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant 0 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree,
      hc7P] using hc7raw
  have hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant 0 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree,
      hc5P] using hc5raw
  have hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant 0 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree,
      hc4P] using hc4raw
  have hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant 0 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree,
      hc3P] using hc3raw
  have hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant 0 := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree,
      hc2P] using hc2raw
  have hearly : 2 * T.delta < 8 * D.faber.scale.p := by
    have hp := D.faber.scale.hp
    linarith
  obtain ⟨h1, h2, h3, h4⟩ :=
    T.zeroLoadLeadingRows_before_c1 hd hc7 hc5 hc4 hc3 hc2 hearly
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
  exact S.infinity_rho1_singular_late_inconsistent_of_parametrization
    hsdegree T hdP hc7P hc5P hc4P hc3P hc2P hc1P hdisc r
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      hr hA hu rfl hY hZ hlate

/-- Target-normalized wrapper for the strict-late rho1 cell. -/
theorem targetNormalized_infinity_rho1_singular_late_inconsistent
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
    (hc10 : S.targetNormalizedSource.faberConstantParameters.c1 = 0)
    (hlate : let U := S.targetNormalizedSource
      let hsdegreeU : U.s.natDegree = 0 := by
        simpa [U, targetNormalizedSource] using hsdegree
      3 * T.delta <
        10 * (U.infinityCommonCoefficientData hsdegreeU).faber.scale.p) :
    False := by
  let U := S.targetNormalizedSource
  let Q := U.faberConstantParameters
  have hsdegreeU : U.s.natDegree = 0 := by
    simpa [U, targetNormalizedSource] using hsdegree
  obtain ⟨hQd, _hQc7, _hQc6, _hQc5, _hQc4, hQc3,
      _hQc2, _hQc1, _hQc0⟩ :=
    S.targetNormalizedCanonicalParameters hd0
  apply U.infinity_rho1_singular_late_inconsistent hsdegreeU T
  · simpa only [Q, U] using hQd
  · simpa only [U] using hc70
  · simpa only [U] using hc50
  · simpa only [U] using hc40
  · simpa only [Q, U] using hQc3
  · simpa only [U] using hc20
  · simpa only [U] using hc10
  · exact hlate

end GCD369CubePolynomialSource

#print axioms
  GCD369CubeHahnFaberPoleData.zeroLoadN12_mem_higherOrderIdeal_before_rho1
#print axioms
  GCD369CubeHahnFaberPoleData.fullN5_eq_zeroSpecialized_before_rho1
#print axioms
  GCD369CubeHahnFaberPoleData.fullN5_orderTop_eq_three_delta_of_singular_rho1_late
#print axioms
  GCD369CubePolynomialSource.infinity_rho1_singular_late_inconsistent
#print axioms
  GCD369CubePolynomialSource.targetNormalized_infinity_rho1_singular_late_inconsistent
