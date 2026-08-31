import InfinityDLoad
import InfinityExactSquare
import FiniteDoubleLoadEndpointLift

/-! # The balanced weight-one load at infinity

This file closes the only timing omitted by `InfinityDLoad`: the triple
resonance `p = 3 * delta`, where the weight-one load, the second moving-root
correction, and the intrinsic cubic term occur together.
-/

noncomputable section

namespace GCD369CubeHahnRegular

/-- If the first three moving-double-root rows vanish below `delta`, then all
three moving-root deviations start no earlier than `delta / 2`.  This is the
source-independent scale-exclusion argument used at the balanced resonance. -/
theorem doubleBlowup_deviations_order_half_lower_of_rows
    {k : Type*} [Field k] [CharZero k]
    (delta : ℚ) (hdelta : 0 < delta)
    (A r D B C : GCD369CubeHahnRegular k)
    (hD0 : constantCoeff D = 0)
    (hB0 : constantCoeff B = 0)
    (hC0 : constantCoeff C = 0)
    (hA : constantCoeff A ≠ 0)
    (hr : constantCoeff r ≠ 0)
    (hrows : ∀ e : ℚ, 0 ≤ e → e < delta →
      ((A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C).1.coeff e = 0) ∧
      ((2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
          3 * A * B * D - 3 * B * C).1.coeff e = 0) ∧
      ((-2 * A ^ 2 * r ^ 2 * D + 6 * B ^ 2 * r ^ 2 +
          2 * A ^ 2 * D ^ 2 - 2 * B ^ 2 * D - 4 * A * C * D +
          3 * C ^ 2).1.coeff e = 0)) :
    (↑(delta / 2) : WithTop ℚ) ≤ D.1.orderTop ∧
      (↑(delta / 2) : WithTop ℚ) ≤ B.1.orderTop ∧
      (↑(delta / 2) : WithTop ℚ) ≤ C.1.orderTop := by
  let Row1 : GCD369CubeHahnRegular k :=
    A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C
  let Row2 : GCD369CubeHahnRegular k :=
    2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
      3 * A * B * D - 3 * B * C
  let Row3 : GCD369CubeHahnRegular k :=
    -2 * A ^ 2 * r ^ 2 * D + 6 * B ^ 2 * r ^ 2 +
      2 * A ^ 2 * D ^ 2 - 2 * B ^ 2 * D - 4 * A * C * D + 3 * C ^ 2
  by_cases hnonzero : D ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0
  · let J : TripleScale D B C := tripleScale D B C hD0 hB0 hC0 hnonzero
    have hnot : ¬ J.mu < delta / 2 := by
      intro hsmall
      have htwo : 2 * J.mu < delta := by linarith
      have hR1 : (↑(2 * J.mu) : WithTop ℚ) ≤ Row1.1.orderTop := by
        rw [HahnSeries.le_orderTop_iff_forall]
        intro q hq
        have hq' : q < 2 * J.mu := WithTop.coe_lt_coe.mp hq
        by_cases hq0 : 0 ≤ q
        · simpa only [Row1] using (hrows q hq0 (by linarith)).1
        · exact coeff_eq_zero_of_neg Row1 (lt_of_not_ge hq0)
      have hR2 : (↑(2 * J.mu) : WithTop ℚ) ≤ Row2.1.orderTop := by
        rw [HahnSeries.le_orderTop_iff_forall]
        intro q hq
        have hq' : q < 2 * J.mu := WithTop.coe_lt_coe.mp hq
        by_cases hq0 : 0 ≤ q
        · simpa only [Row2] using (hrows q hq0 (by linarith)).2.1
        · exact coeff_eq_zero_of_neg Row2 (lt_of_not_ge hq0)
      have hz := hrows (2 * J.mu) (by linarith [J.hmu]) htwo
      have hz1 : Row1.1.coeff (2 * J.mu) = 0 := by
        simpa only [Row1] using hz.1
      have hz2 : Row2.1.coeff (2 * J.mu) = 0 := by
        simpa only [Row2] using hz.2.1
      have hz3 : Row3.1.coeff (2 * J.mu) = 0 := by
        simpa only [Row3] using hz.2.2
      exact doubleBlowup_quadratic_inconsistent A r D B C J hA hr
        (by simpa only [Row1] using hR1)
        (by simpa only [Row2] using hR2)
        (by simpa only [Row1] using hz1)
        (by simpa only [Row2] using hz2)
        (by simpa only [Row3] using hz3)
    have hmu : delta / 2 ≤ J.mu := le_of_not_gt hnot
    have hcoe : (↑(delta / 2) : WithTop ℚ) ≤ (↑J.mu : WithTop ℚ) :=
      WithTop.coe_le_coe.mpr hmu
    have hDmu : (↑J.mu : WithTop ℚ) ≤ D.1.orderTop := by
      have hm := monomial_mul_orderTop_lower J.mu J.hmu.le J.Dn
      exact hm.trans_eq
        (congrArg (fun z : GCD369CubeHahnRegular k => z.1.orderTop) J.hD).symm
    have hBmu : (↑J.mu : WithTop ℚ) ≤ B.1.orderTop := by
      have hm := monomial_mul_orderTop_lower J.mu J.hmu.le J.Bn
      exact hm.trans_eq
        (congrArg (fun z : GCD369CubeHahnRegular k => z.1.orderTop) J.hB).symm
    have hCmu : (↑J.mu : WithTop ℚ) ≤ C.1.orderTop := by
      have hm := monomial_mul_orderTop_lower J.mu J.hmu.le J.Cn
      exact hm.trans_eq
        (congrArg (fun z : GCD369CubeHahnRegular k => z.1.orderTop) J.hC).symm
    exact ⟨hcoe.trans hDmu, hcoe.trans hBmu, hcoe.trans hCmu⟩
  · simp only [not_or, not_ne_iff] at hnonzero
    rcases hnonzero with ⟨hDz, hBz, hCz⟩
    subst D
    subst B
    subst C
    simp

/-- Once the three deviations start at `mu` and the first two rows continue
through `2 * mu`, their balanced coefficients are the universal quadratic
correction packet.  No choice of a square root or leading `B` coefficient is
part of the statement. -/
theorem doubleBlowup_balanced_coefficients_of_order
    {k : Type*} [Field k] [CharZero k]
    (mu : ℚ) (hmu : 0 < mu)
    (A r D B C : GCD369CubeHahnRegular k)
    (hA : constantCoeff A ≠ 0) (hr : constantCoeff r ≠ 0)
    (hD : (↑mu : WithTop ℚ) ≤ D.1.orderTop)
    (hB : (↑mu : WithTop ℚ) ≤ B.1.orderTop)
    (hC : (↑mu : WithTop ℚ) ≤ C.1.orderTop)
    (hR1 : (↑(2 * mu) : WithTop ℚ) ≤
      (A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C).1.orderTop)
    (hR2 : (↑(2 * mu) : WithTop ℚ) ≤
      (2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
        3 * A * B * D - 3 * B * C).1.orderTop) :
    ∃ d b q : k,
      (A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C).1.coeff
          (2 * mu) =
        constantCoeff A ^ 2 * d - 2 * constantCoeff A * q - b ^ 2 ∧
      (2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
          3 * A * B * D - 3 * B * C).1.coeff (2 * mu) =
        2 * constantCoeff A ^ 2 * constantCoeff r * d -
          3 * constantCoeff A * constantCoeff r * q +
          3 * constantCoeff r * b ^ 2 ∧
      (4374 * (-3 * r ^ 2 + D) *
          (A * B * r ^ 2 + 2 * B ^ 2 * r + A * C * r +
            3 * A * B * D - 3 * B * C)).1.coeff (2 * mu) =
        -13122 * constantCoeff A * constantCoeff r ^ 3 * q -
          65610 * constantCoeff r ^ 3 * b ^ 2 := by
  let M : GCD369CubeHahnRegular k := monomial mu hmu.le
  let Dn : GCD369CubeHahnRegular k := shift D mu hD
  let Bn : GCD369CubeHahnRegular k := shift B mu hB
  let Cn : GCD369CubeHahnRegular k := shift C mu hC
  have hDfact : M * Dn = D := by
    simpa only [M, Dn] using monomial_mul_shift D mu hmu.le hD
  have hBfact : M * Bn = B := by
    simpa only [M, Bn] using monomial_mul_shift B mu hmu.le hB
  have hCfact : M * Cn = C := by
    simpa only [M, Cn] using monomial_mul_shift C mu hmu.le hC
  let Qn : GCD369CubeHahnRegular k := Cn + r * Bn
  let FRow1 : GCD369CubeHahnRegular k :=
    M * (A ^ 2 * Dn - 2 * A * Qn) - M ^ 2 * Bn ^ 2
  let FRow2 : GCD369CubeHahnRegular k :=
    M * (2 * A ^ 2 * r * Dn - 3 * A * r * Qn) +
      M ^ 2 * (3 * A * Bn * Dn - 3 * Bn * Cn)
  have hfac1 :
      A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C = FRow1 := by
    dsimp only [FRow1, Qn]
    rw [← hDfact, ← hBfact, ← hCfact]
    ring
  have hfac2 :
      2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 - 3 * A * C * r +
          3 * A * B * D - 3 * B * C = FRow2 := by
    dsimp only [FRow2, Qn]
    rw [← hDfact, ← hBfact, ← hCfact]
    ring
  have hF1 : (↑(2 * mu) : WithTop ℚ) ≤ FRow1.1.orderTop :=
    hR1.trans_eq
      (congrArg (fun z : GCD369CubeHahnRegular k => z.1.orderTop) hfac1)
  have hF2 : (↑(2 * mu) : WithTop ℚ) ≤ FRow2.1.orderTop :=
    hR2.trans_eq
      (congrArg (fun z : GCD369CubeHahnRegular k => z.1.orderTop) hfac2)
  have hlift := doubleBlowup_kernelRemainders_order_lower_of_factoredRows
    mu hmu A r Dn Bn Cn hA hr
      (by simpa only [FRow1, M, Qn] using hF1)
      (by simpa only [FRow2, M, Qn] using hF2)
  let d : GCD369CubeHahnRegular k := shift Dn mu hlift.1
  let q : GCD369CubeHahnRegular k := shift Qn mu hlift.2
  have hdnfact : M * d = Dn := by
    simpa only [M, d] using monomial_mul_shift Dn mu hmu.le hlift.1
  have hqnfact : M * q = Qn := by
    simpa only [M, q] using monomial_mul_shift Qn mu hmu.le hlift.2
  let Dq : GCD369CubeHahnRegular k := M ^ 2 * d
  let Bq : GCD369CubeHahnRegular k := M * Bn
  let Cq : GCD369CubeHahnRegular k := M ^ 2 * q - M * r * Bn
  have hDq : D = Dq := by
    calc
      D = M * Dn := hDfact.symm
      _ = M * (M * d) := congrArg (fun z => M * z) hdnfact.symm
      _ = Dq := by dsimp only [Dq]; ring
  have hBq : B = Bq := by simpa only [Bq] using hBfact.symm
  have hCn : Cn = M * q - r * Bn := by
    dsimp only [Qn] at hqnfact
    linear_combination -hqnfact
  have hCq : C = Cq := by
    calc
      C = M * Cn := hCfact.symm
      _ = M * (M * q - r * Bn) := congrArg (fun z => M * z) hCn
      _ = Cq := by dsimp only [Cq]; ring
  have hquad := doubleBlowup_quadratic_coefficients mu hmu A r d Bn q
  have hq4 := doubleBlowup_quadratic_row4_coefficient mu hmu A r d Bn q
  refine ⟨constantCoeff d, constantCoeff Bn, constantCoeff q, ?_, ?_, ?_⟩
  · rw [hDq, hBq, hCq]
    simpa only [Dq, Bq, Cq, M] using hquad.1
  · rw [hDq, hBq, hCq]
    simpa only [Dq, Bq, Cq, M] using hquad.2.1
  · rw [hDq, hBq, hCq]
    simpa only [Dq, Bq, Cq, M] using hq4

end GCD369CubeHahnRegular

namespace GCD369CubeHahnCommonCoefficientData

/-- Exact zero-high rows in the canonical moving-double-root coordinates of
the infinity coefficient packet. -/
theorem TransverseScale.doubleRoot_zeroHigh_expansions
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (r : GCD369CubeHahnRegular k)
    (hroot : 2 * D.cubicU * r + 3 * D.cubicV = 0) :
    let A := T.Xn
    let d := D.cubicU + 3 * r ^ 2
    let B := T.Yn - r * A
    let C := T.Zn + 2 * r ^ 2 * A
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (729 * GCD369CubeFaberN1
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 =
      (-32 * (729 *
        (A ^ 2 * d - 2 * A * B * r - B ^ 2 - 2 * A * C))) * H ^ 2) ∧
    (2187 * GCD369CubeFaberN2
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 =
      (32 * (-1458 *
        (2 * A ^ 2 * r * d - 3 * A * B * r ^ 2 -
          3 * A * C * r + 3 * A * B * d - 3 * B * C))) * H ^ 2) ∧
    (GCD369CubeFaberN3
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 =
      (128 *
        (-2 * A ^ 2 * r ^ 2 * d + 6 * B ^ 2 * r ^ 2 +
          2 * A ^ 2 * d ^ 2 - 2 * B ^ 2 * d - 4 * A * C * d +
          3 * C ^ 2)) * H ^ 2 - (64 * A ^ 3) * H ^ 3) ∧
    (6561 * GCD369CubeFaberN4
        D.faber.scale.regular0 D.faber.scale.regular1
        D.faber.scale.regular2 D.faber.scale.regular3
        D.faber.scale.regular4 =
      (32 * (4374 * (-3 * r ^ 2 + d) *
        (A * B * r ^ 2 + 2 * B ^ 2 * r + A * C * r +
          3 * A * B * d - 3 * B * C))) * H ^ 2 -
        (314928 * (r * A + B) * A ^ 2) * H ^ 3) := by
  dsimp only
  let A : GCD369CubeHahnRegular k := T.Xn
  let d : GCD369CubeHahnRegular k := D.cubicU + 3 * r ^ 2
  let B : GCD369CubeHahnRegular k := T.Yn - r * A
  let C : GCD369CubeHahnRegular k := T.Zn + 2 * r ^ 2 * A
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let e : GCD369CubeHahnRegular k := D.cubicV - 2 * r ^ 3
  have hA : T.Xn = A := rfl
  have hY : T.Yn = r * A + B := by dsimp only [B]; ring
  have hZ : T.Zn = -2 * r ^ 2 * A + C := by dsimp only [C]; ring
  have hU : D.cubicU = -3 * r ^ 2 + d := by dsimp only [d]; ring
  have hV : D.cubicV = 2 * r ^ 3 + e := by dsimp only [e]; ring
  have hre : 3 * e + 2 * d * r = 0 := by
    dsimp only [e, d]
    linear_combination hroot
  have hrow1 := GCD369CubeDoubleBlowupRow1 A B C r d
  have hrow2 := GCD369CubeDoubleBlowupRow2 A B C r d e hre
  have hrow3 := GCD369CubeDoubleBlowupRow3 A B C r d e hre
  have hrow4 := GCD369CubeDoubleBlowupRow4 A B C r d e hre
  have h1 := T.zeroHighN1Expansion
  have h2 := T.zeroHighN2Expansion
  have h3 := T.zeroHighN3Expansion
  have h4 := T.zeroHighN4Expansion
  rw [monomial_eq_regularMonomial] at h1 h2 h3 h4
  rw [hA, hY, hZ, hU, hrow1] at h1
  rw [hA, hY, hZ, hU, hV, hrow2] at h2
  rw [hA, hY, hZ, hU, hV, hrow3] at h3
  rw [hA, hY, hZ, hU, hV, hrow4] at h4
  exact ⟨by simpa only [A, d, B, C, H] using h1,
    by simpa only [A, d, B, C, H] using h2,
    by simpa only [A, d, B, C, H] using h3,
    by simpa only [A, d, B, C, H] using h4⟩

/-- Before the active `d` exponent, the literal source equations make the
first three moving-root rows vanish at every residual exponent below
`delta`. -/
theorem TransverseScale.doubleRoot_rowCoeffs_zero_before_d
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant D0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hrho1 : D.faber.rho1 = GCD369CubeHahnRegular.constant Rho1)
    (hrho2 : D.faber.rho2 = GCD369CubeHahnRegular.constant Rho2)
    (hrho3 : D.faber.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : D.faber.rho4 = GCD369CubeHahnRegular.constant Rho4)
    (r : GCD369CubeHahnRegular k)
    (hroot : 2 * D.cubicU * r + 3 * D.cubicV = 0)
    (e : ℚ) (he : 0 ≤ e) (heDelta : e < T.delta)
    (hearly : 2 * T.delta + e < D.faber.scale.p) :
    let A := T.Xn
    let d := D.cubicU + 3 * r ^ 2
    let B := T.Yn - r * A
    let C := T.Zn + 2 * r ^ 2 * A
    ((A ^ 2 * d - 2 * A * B * r - B ^ 2 - 2 * A * C).1.coeff e = 0) ∧
    ((2 * A ^ 2 * r * d - 3 * A * B * r ^ 2 - 3 * A * C * r +
        3 * A * B * d - 3 * B * C).1.coeff e = 0) ∧
    ((-2 * A ^ 2 * r ^ 2 * d + 6 * B ^ 2 * r ^ 2 +
        2 * A ^ 2 * d ^ 2 - 2 * B ^ 2 * d - 4 * A * C * d +
        3 * C ^ 2).1.coeff e = 0) := by
  dsimp only
  let A : GCD369CubeHahnRegular k := T.Xn
  let d : GCD369CubeHahnRegular k := D.cubicU + 3 * r ^ 2
  let B : GCD369CubeHahnRegular k := T.Yn - r * A
  let C : GCD369CubeHahnRegular k := T.Zn + 2 * r ^ 2 * A
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let R1 : GCD369CubeHahnRegular k :=
    A ^ 2 * d - 2 * A * B * r - B ^ 2 - 2 * A * C
  let R2 : GCD369CubeHahnRegular k :=
    2 * A ^ 2 * r * d - 3 * A * B * r ^ 2 - 3 * A * C * r +
      3 * A * B * d - 3 * B * C
  let R3 : GCD369CubeHahnRegular k :=
    -2 * A ^ 2 * r ^ 2 * d + 6 * B ^ 2 * r ^ 2 +
      2 * A ^ 2 * d ^ 2 - 2 * B ^ 2 * d - 4 * A * C * d + 3 * C ^ 2
  let N1 : GCD369CubeHahnRegular k := GCD369CubeFaberN1
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3 D.faber.scale.regular4
  let N2 : GCD369CubeHahnRegular k := GCD369CubeFaberN2
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3 D.faber.scale.regular4
  let N3 : GCD369CubeHahnRegular k := GCD369CubeFaberN3
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3 D.faber.scale.regular4
  have hz := D.faber.zeroHighNCoeff_zero_before_d
    D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
    (2 * T.delta + e) (by nlinarith [T.hdelta]) hearly
  have hexp := T.doubleRoot_zeroHigh_expansions r hroot
  have hexp1 : 729 * N1 = (-32 * (729 * R1)) * H ^ 2 := by
    simpa only [N1, R1, A, d, B, C, H] using hexp.1
  have hexp2 : 2187 * N2 = (32 * (-1458 * R2)) * H ^ 2 := by
    simpa only [N2, R2, A, d, B, C, H] using hexp.2.1
  have hexp3 : N3 = (128 * R3) * H ^ 2 - (64 * A ^ 3) * H ^ 3 := by
    simpa only [N3, R3, A, d, B, C, H] using hexp.2.2.1
  have hshift1 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (-32 * (729 * R1)) T.delta e T.hdelta.le 2
  have hshift2 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (32 * (-1458 * R2)) T.delta e T.hdelta.le 2
  have hshift3 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (128 * R3) T.delta e T.hdelta.le 2
  change ((-32 * (729 * R1)) * H ^ 2).1.coeff
      (e + (2 : ℚ) * T.delta) = (-32 * (729 * R1)).1.coeff e at hshift1
  change ((32 * (-1458 * R2)) * H ^ 2).1.coeff
      (e + (2 : ℚ) * T.delta) = (32 * (-1458 * R2)).1.coeff e at hshift2
  change ((128 * R3) * H ^ 2).1.coeff
      (e + (2 : ℚ) * T.delta) = (128 * R3).1.coeff e at hshift3
  have hc1 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * T.delta + e)) hexp1
  have hc2 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * T.delta + e)) hexp2
  have hc3 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff (2 * T.delta + e)) hexp3
  rw [show 2 * T.delta + e = e + (2 : ℚ) * T.delta by ring,
    hshift1] at hc1
  rw [show 2 * T.delta + e = e + (2 : ℚ) * T.delta by ring,
    hshift2] at hc2
  have hcubicShift := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (64 * A ^ 3) T.delta (e - T.delta) T.hdelta.le 3
  change ((64 * A ^ 3) * H ^ 3).1.coeff
      ((e - T.delta) + (3 : ℚ) * T.delta) =
        (64 * A ^ 3).1.coeff (e - T.delta) at hcubicShift
  have hcubicZero : (64 * A ^ 3).1.coeff (e - T.delta) = 0 :=
    GCD369CubeHahnRegular.coeff_eq_zero_of_neg (64 * A ^ 3)
      (sub_neg.mpr heDelta)
  change N3.1.coeff (2 * T.delta + e) =
    ((128 * R3) * H ^ 2).1.coeff (2 * T.delta + e) -
      ((64 * A ^ 3) * H ^ 3).1.coeff (2 * T.delta + e) at hc3
  rw [show 2 * T.delta + e = e + (2 : ℚ) * T.delta by ring,
    hshift3] at hc3
  rw [show e + (2 : ℚ) * T.delta =
      (e - T.delta) + (3 : ℚ) * T.delta by ring,
    hcubicShift, hcubicZero, sub_zero] at hc3
  have hz1scaled : (-32 * (729 * R1)).1.coeff e = 0 := by
    calc
      _ = (729 * N1).1.coeff (e + 2 * T.delta) := hc1.symm
      _ = (729 * N1).1.coeff (2 * T.delta + e) := by
        rw [show e + 2 * T.delta = 2 * T.delta + e by ring]
      _ = 0 := by simpa only [N1] using hz.1
  have hz2scaled : (32 * (-1458 * R2)).1.coeff e = 0 := by
    calc
      _ = (2187 * N2).1.coeff (e + 2 * T.delta) := hc2.symm
      _ = (2187 * N2).1.coeff (2 * T.delta + e) := by
        rw [show e + 2 * T.delta = 2 * T.delta + e by ring]
      _ = 0 := by simpa only [N2] using hz.2.1
  have hz3N : N3.1.coeff (2 * T.delta + e) = 0 := by
    have hnat : (243 * N3).1.coeff (2 * T.delta + e) =
        (243 : k) * N3.1.coeff (2 * T.delta + e) :=
      GCD369CubeHahnRegular.coeff_nat_mul 243 N3 (2 * T.delta + e)
    have hscaled : (243 * N3).1.coeff (2 * T.delta + e) = 0 := by
      simpa only [N3] using hz.2.2.1
    rw [hnat] at hscaled
    exact (mul_eq_zero.mp hscaled).resolve_left (by norm_num)
  have hz3scaled : (128 * R3).1.coeff e = 0 := by
    calc
      _ = N3.1.coeff (e - T.delta + 3 * T.delta) := hc3.symm
      _ = N3.1.coeff (2 * T.delta + e) := by
        rw [show e - T.delta + 3 * T.delta = 2 * T.delta + e by ring]
      _ = 0 := hz3N
  have hscalar1 : -32 * (729 * R1) = (-23328 : ℤ) * R1 := by ring
  have hscalar2 : 32 * (-1458 * R2) = (-46656 : ℤ) * R2 := by ring
  rw [hscalar1, GCD369CubeHahnRegular.coeff_int_mul] at hz1scaled
  rw [hscalar2, GCD369CubeHahnRegular.coeff_int_mul] at hz2scaled
  have hcoeff128 : (128 * R3).1.coeff e =
      (128 : k) * R3.1.coeff e :=
    GCD369CubeHahnRegular.coeff_nat_mul 128 R3 e
  rw [hcoeff128] at hz3scaled
  have hR1zero : R1.1.coeff e = 0 :=
    (mul_eq_zero.mp hz1scaled).resolve_left (by norm_num)
  have hR2zero : R2.1.coeff e = 0 :=
    (mul_eq_zero.mp hz2scaled).resolve_left (by norm_num)
  have hR3zero : R3.1.coeff e = 0 :=
    (mul_eq_zero.mp hz3scaled).resolve_left (by norm_num)
  exact ⟨by simpa only [R1, A, d, B, C] using hR1zero,
    by simpa only [R2, A, d, B, C] using hR2zero,
    by simpa only [R3, A, d, B, C] using hR3zero⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- At `p = 3 * delta`, the first, second, and fourth literal source rows
are the residual normal-row coefficients, the pure `d` load, and (in row
four) the intrinsic cubic constant. -/
theorem TransverseScale.dLoadedNormalRowsAt_balanced
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant D0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hrho1 : D.faber.rho1 = GCD369CubeHahnRegular.constant Rho1)
    (hrho2 : D.faber.rho2 = GCD369CubeHahnRegular.constant Rho2)
    (hrho4 : D.faber.rho4 = GCD369CubeHahnRegular.constant Rho4)
    (r A0 : k)
    (hu : D.u = -3 * r ^ 2) (hv : D.v = 2 * r ^ 3)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r * A0)
    (htie : D.faber.scale.p = 3 * T.delta) :
    ((-32 * GCD369CubeNormalRow1
        T.Xn T.Yn T.Zn D.cubicU).1.coeff T.delta +
          D0 * (798720 * r ^ 9) = 0) ∧
    ((32 * GCD369CubeNormalRow2
        T.Xn T.Yn T.Zn D.cubicU D.cubicV).1.coeff T.delta +
          D0 * (-2156544 * r ^ 10) = 0) ∧
    ((32 * GCD369CubeNormalRow4
        T.Xn T.Yn T.Zn D.cubicU D.cubicV).1.coeff T.delta -
          314928 * r * A0 ^ 3 + D0 * (26956800 * r ^ 12) = 0) := by
  let F := D.faber
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let N1 : GCD369CubeHahnRegular k := GCD369CubeFaberN1
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
  let N2 : GCD369CubeHahnRegular k := GCD369CubeFaberN2
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
  let N4 : GCD369CubeHahnRegular k := GCD369CubeFaberN4
    F.scale.regular0 F.scale.regular1 F.scale.regular2
    F.scale.regular3 F.scale.regular4
  let Row1 : GCD369CubeHahnRegular k :=
    GCD369CubeNormalRow1 T.Xn T.Yn T.Zn D.cubicU
  let Row2 : GCD369CubeHahnRegular k :=
    GCD369CubeNormalRow2 T.Xn T.Yn T.Zn D.cubicU D.cubicV
  let Row4 : GCD369CubeHahnRegular k :=
    GCD369CubeNormalRow4 T.Xn T.Yn T.Zn D.cubicU D.cubicV
  let P1 : GCD369CubeHahnRegular k :=
    27648 * F.scale.regular0 * F.scale.regular3 +
      27648 * F.scale.regular1 * F.scale.regular2 -
      9216 * F.scale.regular1 * F.scale.regular4 ^ 2 -
      18432 * F.scale.regular2 * F.scale.regular3 * F.scale.regular4 -
      3072 * F.scale.regular3 ^ 3 +
      5120 * F.scale.regular3 * F.scale.regular4 ^ 3
  let P2 : GCD369CubeHahnRegular k :=
    82944 * F.scale.regular0 * F.scale.regular2 -
      27648 * F.scale.regular0 * F.scale.regular4 ^ 2 +
      41472 * F.scale.regular1 ^ 2 -
      55296 * F.scale.regular1 * F.scale.regular3 * F.scale.regular4 -
      27648 * F.scale.regular2 ^ 2 * F.scale.regular4 -
      27648 * F.scale.regular2 * F.scale.regular3 ^ 2 +
      15360 * F.scale.regular2 * F.scale.regular4 ^ 3 +
      23040 * F.scale.regular3 ^ 2 * F.scale.regular4 ^ 2 -
      2048 * F.scale.regular4 ^ 5
  let P4 : GCD369CubeHahnRegular k :=
    373248 * F.scale.regular0 ^ 2 -
      248832 * F.scale.regular0 * F.scale.regular2 * F.scale.regular4 -
      124416 * F.scale.regular0 * F.scale.regular3 ^ 2 +
      55296 * F.scale.regular0 * F.scale.regular4 ^ 3 -
      124416 * F.scale.regular1 ^ 2 * F.scale.regular4 -
      373248 * F.scale.regular1 * F.scale.regular2 * F.scale.regular3 +
      207360 * F.scale.regular1 * F.scale.regular3 * F.scale.regular4 ^ 2 -
      82944 * F.scale.regular2 ^ 3 +
      124416 * F.scale.regular2 ^ 2 * F.scale.regular4 ^ 2 +
      248832 * F.scale.regular2 * F.scale.regular3 ^ 2 * F.scale.regular4 -
      46080 * F.scale.regular2 * F.scale.regular4 ^ 4 +
      20736 * F.scale.regular3 ^ 4 -
      92160 * F.scale.regular3 ^ 2 * F.scale.regular4 ^ 3 +
      5120 * F.scale.regular4 ^ 6
  let d1 : GCD369CubeHahnRegular k :=
    F.scale.weightedRegular 1 (GCD369CubeHahnRegular.constant D0)
  have hload1 : GCD369CubeHahnRegular.constantCoeff P1 =
      798720 * r ^ 9 := by
    dsimp only [P1, F]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    change
      27648 * F.scale.leading0 * F.scale.leading3 +
        27648 * F.scale.leading1 * F.scale.leading2 -
        9216 * F.scale.leading1 * F.scale.leading4 ^ 2 -
        18432 * F.scale.leading2 * F.scale.leading3 * F.scale.leading4 -
        3072 * F.scale.leading3 ^ 3 +
        5120 * F.scale.leading3 * F.scale.leading4 ^ 3 = _
    rw [D.ha0, D.ha1, D.ha2, D.ha3, D.ha4, hu, hv]
    convert (GCD369Cube_dLoadRemainders_doubleRoot r).1 using 1 <;> ring
  have hload2 : GCD369CubeHahnRegular.constantCoeff P2 =
      -2156544 * r ^ 10 := by
    dsimp only [P2, F]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    change
      82944 * F.scale.leading0 * F.scale.leading2 -
        27648 * F.scale.leading0 * F.scale.leading4 ^ 2 +
        41472 * F.scale.leading1 ^ 2 -
        55296 * F.scale.leading1 * F.scale.leading3 * F.scale.leading4 -
        27648 * F.scale.leading2 ^ 2 * F.scale.leading4 -
        27648 * F.scale.leading2 * F.scale.leading3 ^ 2 +
        15360 * F.scale.leading2 * F.scale.leading4 ^ 3 +
        23040 * F.scale.leading3 ^ 2 * F.scale.leading4 ^ 2 -
        2048 * F.scale.leading4 ^ 5 = _
    rw [D.ha0, D.ha1, D.ha2, D.ha3, D.ha4, hu, hv]
    convert (GCD369Cube_dLoadRemainders_doubleRoot r).2.1 using 1 <;> ring
  have hload4 : GCD369CubeHahnRegular.constantCoeff P4 =
      26956800 * r ^ 12 := by
    dsimp only [P4, F]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    change
      373248 * F.scale.leading0 ^ 2 -
        248832 * F.scale.leading0 * F.scale.leading2 * F.scale.leading4 -
        124416 * F.scale.leading0 * F.scale.leading3 ^ 2 +
        55296 * F.scale.leading0 * F.scale.leading4 ^ 3 -
        124416 * F.scale.leading1 ^ 2 * F.scale.leading4 -
        373248 * F.scale.leading1 * F.scale.leading2 * F.scale.leading3 +
        207360 * F.scale.leading1 * F.scale.leading3 * F.scale.leading4 ^ 2 -
        82944 * F.scale.leading2 ^ 3 +
        124416 * F.scale.leading2 ^ 2 * F.scale.leading4 ^ 2 +
        248832 * F.scale.leading2 * F.scale.leading3 ^ 2 * F.scale.leading4 -
        46080 * F.scale.leading2 * F.scale.leading4 ^ 4 +
        20736 * F.scale.leading3 ^ 4 -
        92160 * F.scale.leading3 ^ 2 * F.scale.leading4 ^ 3 +
        5120 * F.scale.leading4 ^ 6 = _
    rw [D.ha0, D.ha1, D.ha2, D.ha3, D.ha4, hu, hv]
    convert (GCD369Cube_dLoadRemainders_doubleRoot r).2.2 using 1 <;> ring
  have hweight1 : (d1 * P1).1.coeff F.scale.p =
      D0 * GCD369CubeHahnRegular.constantCoeff P1 := by
    simpa only [d1] using
      F.scale.weightedRegular_one_constant_mul_coeff D0 P1
  have hweight2 : (d1 * P2).1.coeff F.scale.p =
      D0 * GCD369CubeHahnRegular.constantCoeff P2 := by
    simpa only [d1] using
      F.scale.weightedRegular_one_constant_mul_coeff D0 P2
  have hweight4 : (d1 * P4).1.coeff F.scale.p =
      D0 * GCD369CubeHahnRegular.constantCoeff P4 := by
    simpa only [d1] using
      F.scale.weightedRegular_one_constant_mul_coeff D0 P4
  have hz1 := F.dN1Coeff_zero C7 C5 C4 C3 C2 C1 Rho1
    hc7 hc5 hc4 hc3 hc2 hc1 hrho1
  have hz2 := F.dN2Coeff_zero C7 C5 C4 C3 C2 C1 Rho2
    hc7 hc5 hc4 hc3 hc2 hc1 hrho2
  have hz4 := F.dN4Coeff_zero C7 C5 C4 C3 C2 C1 Rho4
    hc7 hc5 hc4 hc3 hc2 hc1 hrho4
  rw [hd] at hz1 hz2 hz4
  change (729 * N1).1.coeff F.scale.p + (d1 * P1).1.coeff F.scale.p = 0 at hz1
  change (2187 * N2).1.coeff F.scale.p + (d1 * P2).1.coeff F.scale.p = 0 at hz2
  change (6561 * N4).1.coeff F.scale.p + (d1 * P4).1.coeff F.scale.p = 0 at hz4
  rw [hweight1, hload1] at hz1
  rw [hweight2, hload2] at hz2
  rw [hweight4, hload4] at hz4
  have hexp1 := T.zeroHighN1Expansion
  have hexp2 := T.zeroHighN2Expansion
  have hexp4 := T.zeroHighN4Expansion
  rw [monomial_eq_regularMonomial] at hexp1 hexp2 hexp4
  have hc1 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff F.scale.p) hexp1
  have hc2 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff F.scale.p) hexp2
  have hc4 := congrArg
    (fun z : GCD369CubeHahnRegular k => z.1.coeff F.scale.p) hexp4
  have hshift1 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (-32 * Row1) T.delta T.delta T.hdelta.le 2
  have hshift2 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (32 * Row2) T.delta T.delta T.hdelta.le 2
  have hshift4 := GCD369CubeHahnRegular.coeff_mul_monomial_pow_add
    (32 * Row4) T.delta T.delta T.hdelta.le 2
  change ((-32 * Row1) * H ^ 2).1.coeff
      (T.delta + (2 : ℚ) * T.delta) = (-32 * Row1).1.coeff T.delta at hshift1
  change ((32 * Row2) * H ^ 2).1.coeff
      (T.delta + (2 : ℚ) * T.delta) = (32 * Row2).1.coeff T.delta at hshift2
  change ((32 * Row4) * H ^ 2).1.coeff
      (T.delta + (2 : ℚ) * T.delta) = (32 * Row4).1.coeff T.delta at hshift4
  have hcubic := GCD369CubeHahnRegular.coeff_mul_monomial_pow_at
    T.delta T.hdelta 3 (314928 * T.Yn * T.Xn ^ 2)
  change ((314928 * T.Yn * T.Xn ^ 2) * H ^ 3).1.coeff
      (3 * T.delta) = GCD369CubeHahnRegular.constantCoeff
        (314928 * T.Yn * T.Xn ^ 2) at hcubic
  have hcubicval :
      ((314928 * T.Yn * T.Xn ^ 2) * H ^ 3).1.coeff F.scale.p =
        314928 * r * A0 ^ 3 := by
    rw [htie, hcubic]
    simp only [map_mul, map_pow, map_ofNat, hY, hX]
    ring
  change (729 * N1).1.coeff F.scale.p =
      ((-32 * Row1) * H ^ 2).1.coeff F.scale.p at hc1
  change (2187 * N2).1.coeff F.scale.p =
      ((32 * Row2) * H ^ 2).1.coeff F.scale.p at hc2
  change (6561 * N4).1.coeff F.scale.p =
      ((32 * Row4) * H ^ 2).1.coeff F.scale.p -
        ((314928 * T.Yn * T.Xn ^ 2) * H ^ 3).1.coeff F.scale.p at hc4
  rw [htie, show 3 * T.delta = T.delta + (2 : ℚ) * T.delta by ring,
    hshift1] at hc1
  rw [htie, show 3 * T.delta = T.delta + (2 : ℚ) * T.delta by ring,
    hshift2] at hc2
  rw [htie, show 3 * T.delta = T.delta + (2 : ℚ) * T.delta by ring,
    hshift4] at hc4
  have hcubicval' :
      ((314928 * T.Yn * T.Xn ^ 2) * H ^ 3).1.coeff
          (T.delta + 2 * T.delta) = 314928 * r * A0 ^ 3 := by
    rw [← show 3 * T.delta = T.delta + 2 * T.delta by ring,
      ← htie]
    exact hcubicval
  rw [hcubicval'] at hc4
  rw [htie, show 3 * T.delta = T.delta + 2 * T.delta by ring] at hz1 hz2 hz4
  rw [hc1] at hz1
  rw [hc2] at hz2
  rw [hc4] at hz4
  exact ⟨by simpa only [Row1] using hz1,
    by simpa only [Row2] using hz2,
    by simpa only [Row4] using hz4⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- The balanced first, second, and fourth source rows force the coefficient
of the fifth terminal numerator at `p = 3 * delta` to be nonzero. -/
theorem TransverseScale.dBalancedTerminal_nonzero
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant D0)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hrho1 : D.faber.rho1 = GCD369CubeHahnRegular.constant Rho1)
    (hrho2 : D.faber.rho2 = GCD369CubeHahnRegular.constant Rho2)
    (hrho3 : D.faber.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : D.faber.rho4 = GCD369CubeHahnRegular.constant Rho4)
    (r A0 : k) (hr : r ≠ 0) (hA0 : A0 ≠ 0)
    (hu : D.u = -3 * r ^ 2) (hv : D.v = 2 * r ^ 3)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r * A0)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r ^ 2 * A0)
    (htie : D.faber.scale.p = 3 * T.delta) :
    -2519424 * r ^ 2 * A0 ^ 3 - 554729472 * r ^ 13 * D0 ≠ 0 := by
  have hU : GCD369CubeHahnRegular.constantCoeff D.cubicU ≠ 0 := by
    rw [D.constantCoeff_cubicU, hu]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hr)
  let rr : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.movingDoubleRoot D.cubicU D.cubicV hU
  have hrr : GCD369CubeHahnRegular.constantCoeff rr = r := by
    exact GCD369CubeHahnRegular.constantCoeff_movingDoubleRoot
      D.cubicU D.cubicV hU r
      (by rw [D.constantCoeff_cubicU, hu])
      (by rw [D.constantCoeff_cubicV, hv]) hr
  have hroot : 2 * D.cubicU * rr + 3 * D.cubicV = 0 :=
    GCD369CubeHahnRegular.movingDoubleRoot_relation D.cubicU D.cubicV hU
  let A : GCD369CubeHahnRegular k := T.Xn
  let ddev : GCD369CubeHahnRegular k := D.cubicU + 3 * rr ^ 2
  let Bdev : GCD369CubeHahnRegular k := T.Yn - rr * A
  let Cdev : GCD369CubeHahnRegular k := T.Zn + 2 * rr ^ 2 * A
  let Row1 : GCD369CubeHahnRegular k :=
    A ^ 2 * ddev - 2 * A * Bdev * rr - Bdev ^ 2 - 2 * A * Cdev
  let Row2 : GCD369CubeHahnRegular k :=
    2 * A ^ 2 * rr * ddev - 3 * A * Bdev * rr ^ 2 -
      3 * A * Cdev * rr + 3 * A * Bdev * ddev - 3 * Bdev * Cdev
  let Row3 : GCD369CubeHahnRegular k :=
    -2 * A ^ 2 * rr ^ 2 * ddev + 6 * Bdev ^ 2 * rr ^ 2 +
      2 * A ^ 2 * ddev ^ 2 - 2 * Bdev ^ 2 * ddev -
      4 * A * Cdev * ddev + 3 * Cdev ^ 2
  let Row4 : GCD369CubeHahnRegular k :=
    4374 * (-3 * rr ^ 2 + ddev) *
      (A * Bdev * rr ^ 2 + 2 * Bdev ^ 2 * rr + A * Cdev * rr +
        3 * A * Bdev * ddev - 3 * Bdev * Cdev)
  have hd0 : GCD369CubeHahnRegular.constantCoeff ddev = 0 := by
    dsimp only [ddev]
    simp only [map_add, map_mul, map_pow, map_ofNat,
      D.constantCoeff_cubicU, hrr, hu]
    ring
  have hB0 : GCD369CubeHahnRegular.constantCoeff Bdev = 0 := by
    dsimp only [Bdev, A]
    simp only [map_sub, map_mul, hY, hrr, hX]
    ring
  have hC0 : GCD369CubeHahnRegular.constantCoeff Cdev = 0 := by
    dsimp only [Cdev, A]
    simp only [map_add, map_mul, map_pow, map_ofNat, hZ, hrr, hX]
    ring
  have hrows : ∀ e : ℚ, 0 ≤ e → e < T.delta →
      Row1.1.coeff e = 0 ∧ Row2.1.coeff e = 0 ∧ Row3.1.coeff e = 0 := by
    intro e he hedelta
    have h := T.doubleRoot_rowCoeffs_zero_before_d
      D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
      rr hroot e he hedelta (by rw [htie]; linarith)
    simpa only [Row1, Row2, Row3, A, ddev, Bdev, Cdev] using h
  have hhalf :=
    GCD369CubeHahnRegular.doubleBlowup_deviations_order_half_lower_of_rows
      T.delta T.hdelta A rr ddev Bdev Cdev hd0 hB0 hC0
      (by simpa only [A, hX] using hA0)
      (by simpa only [hrr] using hr)
      (by
        intro e he hedelta
        simpa only [Row1, Row2, Row3] using hrows e he hedelta)
  have hR1 : (↑T.delta : WithTop ℚ) ≤ Row1.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro e he
    have he' : e < T.delta := WithTop.coe_lt_coe.mp he
    by_cases he0 : 0 ≤ e
    · exact (hrows e he0 he').1
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg Row1
        (lt_of_not_ge he0)
  have hR2 : (↑T.delta : WithTop ℚ) ≤ Row2.1.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro e he
    have he' : e < T.delta := WithTop.coe_lt_coe.mp he
    by_cases he0 : 0 ≤ e
    · exact (hrows e he0 he').2.1
    · exact GCD369CubeHahnRegular.coeff_eq_zero_of_neg Row2
        (lt_of_not_ge he0)
  let mu : ℚ := T.delta / 2
  have hmu : 0 < mu := by dsimp only [mu]; linarith [T.hdelta]
  have htwomu : 2 * mu = T.delta := by dsimp only [mu]; ring
  obtain ⟨d0, b0, q0, hq1, hq2, hq4⟩ :=
    GCD369CubeHahnRegular.doubleBlowup_balanced_coefficients_of_order
      mu hmu A rr ddev Bdev Cdev
      (by simpa only [A, hX] using hA0)
      (by simpa only [hrr] using hr)
      (by simpa only [mu] using hhalf.1)
      (by simpa only [mu] using hhalf.2.1)
      (by simpa only [mu] using hhalf.2.2)
      (by simpa only [htwomu, Row1] using hR1)
      (by simpa only [htwomu, Row2] using hR2)
  rw [htwomu] at hq1 hq2 hq4
  have hYeq : T.Yn = rr * A + Bdev := by dsimp only [Bdev, A]; ring
  have hZeq : T.Zn = -2 * rr ^ 2 * A + Cdev := by
    dsimp only [Cdev, A]
    ring
  have hUeq : D.cubicU = -3 * rr ^ 2 + ddev := by
    dsimp only [ddev]
    ring
  let e : GCD369CubeHahnRegular k := D.cubicV - 2 * rr ^ 3
  have hVeq : D.cubicV = 2 * rr ^ 3 + e := by dsimp only [e]; ring
  have hre : 3 * e + 2 * ddev * rr = 0 := by
    dsimp only [e, ddev]
    linear_combination hroot
  have hrow1 : GCD369CubeNormalRow1 T.Xn T.Yn T.Zn D.cubicU =
      729 * Row1 := by
    rw [show T.Xn = A by rfl, hYeq, hZeq, hUeq]
    simpa only [Row1] using
      (GCD369CubeDoubleBlowupRow1 A Bdev Cdev rr ddev)
  have hrow2 : GCD369CubeNormalRow2 T.Xn T.Yn T.Zn
      D.cubicU D.cubicV = -1458 * Row2 := by
    rw [show T.Xn = A by rfl, hYeq, hZeq, hUeq, hVeq]
    simpa only [Row2] using
      (GCD369CubeDoubleBlowupRow2 A Bdev Cdev rr ddev e hre)
  have hrow4 : GCD369CubeNormalRow4 T.Xn T.Yn T.Zn
      D.cubicU D.cubicV = Row4 := by
    rw [show T.Xn = A by rfl, hYeq, hZeq, hUeq, hVeq]
    simpa only [Row4] using
      (GCD369CubeDoubleBlowupRow4 A Bdev Cdev rr ddev e hre)
  obtain ⟨hload1, hload2, hload4⟩ := T.dLoadedNormalRowsAt_balanced
    D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho4
    r A0 hu hv hX hY htie
  have hs1 : -32 * (729 * Row1) = (-23328 : ℤ) * Row1 := by ring
  have hs2 : 32 * (-1458 * Row2) = (-46656 : ℤ) * Row2 := by ring
  rw [hrow1, hs1, GCD369CubeHahnRegular.coeff_int_mul, hq1] at hload1
  rw [hrow2, hs2, GCD369CubeHahnRegular.coeff_int_mul, hq2] at hload2
  rw [hrow4] at hload4
  have hcoeff32 : (32 * Row4).1.coeff T.delta =
      (32 : k) * Row4.1.coeff T.delta :=
    GCD369CubeHahnRegular.coeff_nat_mul 32 Row4 T.delta
  rw [hcoeff32, hq4] at hload4
  simp only [A, hX, hrr] at hload1 hload2 hload4
  apply GCD369CubeDLoadBalancedTerminal_nonzero
    A0 r d0 q0 (b0 ^ 2) D0 hA0 hr
  · linear_combination hload1
  · linear_combination hload2
  · linear_combination hload4

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubeHahnFaberPoleData

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- At the balanced singular timing, the nonzero combined intrinsic/load
coefficient is the exact first coefficient of the full fifth numerator. -/
theorem fullN5_orderTop_eq_p_of_singular_balanced
    {k : Type*} [Field k] [CharZero k]
    (D : GCD369CubeHahnCommonCoefficientData k)
    (T : D.TransverseScale)
    (Kd C7 C5 C4 C3 C2 C1 R1 R2 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant Kd)
    (hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (r A : k) (hr : r ≠ 0) (hA : A ≠ 0)
    (hu : D.u = -3 * r ^ 2) (hv : D.v = 2 * r ^ 3)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r * A)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r ^ 2 * A)
    (htie : D.faber.scale.p = 3 * T.delta)
    (hterminal :
      -2519424 * r ^ 2 * A ^ 3 - 554729472 * r ^ 13 * Kd ≠ 0) :
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
        (↑D.faber.scale.p : WithTop ℚ) := by
  let I : Ideal (GCD369CubeHahnRegular k) :=
    GCD369CubeHahnRegular.higherOrderIdeal
      D.faber.scale.p D.faber.scale.hp.le
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let dload : GCD369CubeHahnRegular k :=
    D.faber.scale.weightedRegular 1 D.faber.d
  let C : GCD369CubeHahnRegular k :=
    GCD369CubeNormalRow5Cubic T.Xn T.Yn T.Zn D.cubicU
  let Intrinsic : GCD369CubeHahnRegular k := 839808 * H ^ 3 * C
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
  let Nd : GCD369CubeHahnRegular k := GCD369CubeFaberFullN5
    D.faber.scale.regular0 D.faber.scale.regular1
    D.faber.scale.regular2 D.faber.scale.regular3
    D.faber.scale.regular4 dload 0 0 0 0 0 0
  obtain ⟨Rem, hRemCoeff, hrelation⟩ := T.dTerminalRelation
  let Load : GCD369CubeHahnRegular k := dload * Rem
  let Main : GCD369CubeHahnRegular k := Intrinsic + Load
  have hCcoeff : GCD369CubeHahnRegular.constantCoeff C =
      -3 * r ^ 2 * A ^ 3 := by
    dsimp only [C]
    rw [GCD369CubeNormalRow5Cubic_map,
      D.constantCoeff_cubicU, hX, hY, hZ, hu]
    exact GCD369CubeNormalRow5Cubic_doubleRoot r A
  have hRemCoeff' : GCD369CubeHahnRegular.constantCoeff Rem =
      -554729472 * r ^ 13 := by
    calc
      GCD369CubeHahnRegular.constantCoeff Rem =
          540672 * D.u ^ 5 * D.v - 4055040 * D.u ^ 2 * D.v ^ 3 :=
        hRemCoeff
      _ = -554729472 * r ^ 13 := by
        rw [hu, hv]
        exact GCD369CubeDTerminalResidual_doubleRoot r
  have hload : dload =
      GCD369CubeHahnRegular.monomial
          D.faber.scale.p D.faber.scale.hp.le *
        GCD369CubeHahnRegular.constant Kd := by
    apply Subtype.ext
    dsimp only [dload, GCD369CubeHahnPoleScale.weightedRegular]
    change D.faber.scale.t ^ 1 * D.faber.d.1 =
      HahnSeries.single D.faber.scale.p 1 *
        (GCD369CubeHahnRegular.constant Kd).1
    rw [hd]
    simp [GCD369CubeHahnPoleScale.t]
  have hIntrinsicFactor : Intrinsic = H ^ 3 * (839808 * C) := by
    dsimp only [Intrinsic]
    ring
  have hIntrinsicLower : (↑D.faber.scale.p : WithTop ℚ) ≤
      Intrinsic.1.orderTop := by
    rw [hIntrinsicFactor, htie]
    convert GCD369CubeHahnRegular.orderTop_monomial_pow_mul_lower
      T.delta T.hdelta 3 (839808 * C) using 1 <;> norm_num [H]
  have hIntrinsicCoeff : Intrinsic.1.coeff D.faber.scale.p =
      -2519424 * r ^ 2 * A ^ 3 := by
    rw [hIntrinsicFactor, htie]
    have hc := GCD369CubeHahnRegular.coeff_monomial_pow_mul_at
      T.delta T.hdelta 3 (839808 * C)
    change (H ^ 3 * (839808 * C)).1.coeff (3 * T.delta) =
      GCD369CubeHahnRegular.constantCoeff (839808 * C) at hc
    rw [hc]
    simp only [map_mul, map_ofNat, hCcoeff]
    ring
  have hLoadFactor : Load =
      (GCD369CubeHahnRegular.monomial
          D.faber.scale.p D.faber.scale.hp.le) ^ 1 *
        (GCD369CubeHahnRegular.constant Kd * Rem) := by
    dsimp only [Load]
    rw [hload]
    ring
  have hLoadLower : (↑D.faber.scale.p : WithTop ℚ) ≤ Load.1.orderTop := by
    rw [hLoadFactor]
    simpa using GCD369CubeHahnRegular.orderTop_monomial_pow_mul_lower
      D.faber.scale.p D.faber.scale.hp 1
        (GCD369CubeHahnRegular.constant Kd * Rem)
  have hLoadCoeff : Load.1.coeff D.faber.scale.p =
      -554729472 * r ^ 13 * Kd := by
    rw [hLoadFactor]
    have hc := GCD369CubeHahnRegular.coeff_monomial_pow_mul_at
      D.faber.scale.p D.faber.scale.hp 1
        (GCD369CubeHahnRegular.constant Kd * Rem)
    have hc' :
        ((GCD369CubeHahnRegular.monomial
            D.faber.scale.p D.faber.scale.hp.le) ^ 1 *
          (GCD369CubeHahnRegular.constant Kd * Rem)).1.coeff
            D.faber.scale.p =
          GCD369CubeHahnRegular.constantCoeff
            (GCD369CubeHahnRegular.constant Kd * Rem) := by
      simpa using hc
    rw [hc']
    simp only [map_mul, GCD369CubeHahnRegular.constantCoeff_constant,
      hRemCoeff']
    ring
  have hMainLower : (↑D.faber.scale.p : WithTop ℚ) ≤ Main.1.orderTop := by
    dsimp only [Main]
    exact (le_min hIntrinsicLower hLoadLower).trans
      HahnSeries.min_orderTop_le_orderTop_add
  have hMainCoeff : Main.1.coeff D.faber.scale.p =
      -2519424 * r ^ 2 * A ^ 3 - 554729472 * r ^ 13 * Kd := by
    dsimp only [Main]
    change (Intrinsic.1 + Load.1).coeff D.faber.scale.p = _
    rw [HahnSeries.coeff_add, hIntrinsicCoeff, hLoadCoeff]
    ring
  have hMainCoeff_ne : Main.1.coeff D.faber.scale.p ≠ 0 := by
    rw [hMainCoeff]
    exact hterminal
  have hMainOrder : Main.1.orderTop =
      (↑D.faber.scale.p : WithTop ℚ) :=
    le_antisymm
      (HahnSeries.orderTop_le_of_coeff_ne_zero hMainCoeff_ne)
      hMainLower
  obtain ⟨hN1, hN2⟩ := D.faber.dN12_mem_higherOrderIdeal
    C7 C5 C4 C3 C2 C1 R1 R2
    hc7 hc5 hc4 hc3 hc2 hc1 hr1 hr2
  change _ ∈ I at hN1 hN2
  have hterm1 :
      24 * D.cubicU ^ 2 *
        GCD369CubeFaberD1
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4 dload ∈ I := I.mul_mem_left _ hN1
  have hterm2 :
      (-24 * D.cubicV) *
        GCD369CubeFaberD2
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4 dload ∈ I := I.mul_mem_left _ hN2
  have hrelation0 : Nd =
      24 * D.cubicU ^ 2 *
          GCD369CubeFaberD1
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4 dload -
        24 * D.cubicV *
          GCD369CubeFaberD2
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4 dload + Intrinsic + Load := by
    simpa only [Nd, H, dload, C, Intrinsic, Load] using hrelation
  have hrelation' : Nd =
      24 * D.cubicU ^ 2 *
          GCD369CubeFaberD1
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4 dload -
        24 * D.cubicV *
          GCD369CubeFaberD2
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4 dload + Main := by
    rw [hrelation0]
    dsimp only [Main]
    ring
  have hNdMain : Nd - Main ∈ I := by
    have heq : Nd - Main =
        (24 * D.cubicU ^ 2 *
          GCD369CubeFaberD1
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4 dload) +
        ((-24 * D.cubicV) *
          GCD369CubeFaberD2
            D.faber.scale.regular0 D.faber.scale.regular1
            D.faber.scale.regular2 D.faber.scale.regular3
            D.faber.scale.regular4 dload) := by
      rw [hrelation']
      ring
    rw [heq]
    exact I.add_mem hterm1 hterm2
  have hNdiff : N - Nd ∈ I := by
    simpa only [N, Nd, dload, I] using
      D.faber.fullN5_sub_dSpecialized_mem_higherOrderIdeal
        C7 C5 C4 C3 C2 C1 hc7 hc5 hc4 hc3 hc2 hc1
  have hNMain : N - Main ∈ I := by
    have heq : N - Main = (N - Nd) + (Nd - Main) := by ring
    rw [heq]
    exact I.add_mem hNdiff hNdMain
  have hsum : N = Main + (N - Main) := by ring
  have hlt : Main.1.orderTop < (N - Main).1.orderTop := by
    rw [hMainOrder]
    exact hNMain
  change N.1.orderTop = (↑D.faber.scale.p : WithTop ℚ)
  rw [hsum]
  change (Main.1 + (N - Main).1).orderTop = _
  rw [HahnSeries.orderTop_add_eq_left hlt, hMainOrder]

end GCD369CubeHahnFaberPoleData

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- A nonzero weight-one load is impossible at the unique triple resonance
`p = 3 * delta`. -/
theorem GCD369CubePolynomialSource.infinity_d_eq_zero_singular_balanced
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (htie :
      (S.infinityCommonCoefficientData hsdegree).faber.scale.p =
        3 * T.delta) :
    S.faberConstantParameters.d = 0 := by
  let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
  let D := S.infinityCommonCoefficientData hsdegree
  let P := S.faberConstantParameters
  let R := S.faberFirstIntegralConstants
  obtain ⟨hd, hc7, hc5, hc4, hc3, hc2, hc1,
      hr1, hr2, hr3, hr4⟩ :=
    S.infinityFaberPoleData_constant_loads hpole
  have hdD : D.faber.d = GCD369CubeHahnRegular.constant P.d := by
    simpa only [D, P, S.infinityCommonCoefficientData_faber hsdegree] using hd
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
  have hr3D : D.faber.rho3 = GCD369CubeHahnRegular.constant R.rho3 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree] using hr3
  have hr4D : D.faber.rho4 = GCD369CubeHahnRegular.constant R.rho4 := by
    simpa only [D, R, S.infinityCommonCoefficientData_faber hsdegree] using hr4
  by_contra hPd
  have hmiddle : 2 * T.delta < D.faber.scale.p := by
    rw [htie]
    linarith [T.hdelta]
  have hrows := T.zeroLoadLeadingRows_before_d
    P.d P.c7 P.c5 P.c4 P.c3 P.c2 P.c1
      R.rho1 R.rho2 R.rho3 R.rho4
    hdD hc7D hc5D hc4D hc3D hc2D hc1D
      hr1D hr2D hr3D hr4D hmiddle
  obtain ⟨r, hA, hu, hv, hY, hZ⟩ :=
    GCD369CubeZeroLoadNormal_parametrization
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn)
      D.u D.v T.hleading hrows.1 hrows.2.1 hrows.2.2.1 hrows.2.2.2
  have hr : r ≠ 0 := by
    intro hzero
    have hu0 : D.u = 0 := by rw [hu, hzero]; norm_num
    have hv0 : D.v = 0 := by rw [hv, hzero]; norm_num
    exact D.hprojective.elim (fun h => h hu0) (fun h => h hv0)
  have hterminal := T.dBalancedTerminal_nonzero
    P.d P.c7 P.c5 P.c4 P.c3 P.c2 P.c1
      R.rho1 R.rho2 R.rho3 R.rho4
    hdD hc7D hc5D hc4D hc3D hc2D hc1D
      hr1D hr2D hr3D hr4D
    r (GCD369CubeHahnRegular.constantCoeff T.Xn) hr hA
      hu hv rfl hY hZ htie
  have hNorder :=
    GCD369CubeHahnFaberPoleData.fullN5_orderTop_eq_p_of_singular_balanced
      D T P.d P.c7 P.c5 P.c4 P.c3 P.c2 P.c1 R.rho1 R.rho2
      hdD hc7D hc5D hc4D hc3D hc2D hc1D hr1D hr2D
      r (GCD369CubeHahnRegular.constantCoeff T.Xn) hr hA
      hu hv rfl hY hZ htie hterminal
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
          D.faber.scale.p :=
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
      D.faber.scale.p hNorder
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
  have hfirst :
      (D.faber.scale.t ^ 14 *
        GCD369CubeRatFuncHahnAtInfinity S.terminalFaberInvariant).order =
          1 * D.faber.scale.p := by
    rw [← hscaled]
    simpa using hterminalOrder
  have hscale : 13 *
      (S.infinityFaberPoleData hpole).scale.p = 1 := by
    simpa only [Nat.cast_one, sub_self, one_mul,
      show (14 : ℚ) - 1 = 13 by norm_num,
      D, S.infinityCommonCoefficientData_faber hsdegree] using
        S.infinity_terminal_scale_eq_of_order_eq_weight
          hsdegree hpole 1 hfirst
  have hu_ne : D.u ≠ 0 := by
    rw [hu]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hr)
  have h4D : D.faber.scale.leading4 ≠ 0 := by
    rw [D.ha4]
    exact mul_ne_zero (by norm_num) hu_ne
  have h4 : (S.infinityFaberPoleData hpole).scale.leading4 ≠ 0 := by
    simpa only [D, S.infinityCommonCoefficientData_faber hsdegree] using h4D
  have hlanding : GCD369CubeConstantPoleDegreeLanding :=
    S.infinityConstantPoleDegreeLanding_of_d_scale
      hsdegree hpole hscale h4
  exact GCD369CubeConstantPoleDegreeLandingEmpty hlanding

#print axioms
  GCD369CubePolynomialSource.infinity_d_eq_zero_singular_balanced

/-- The weight-one parameter vanishes at the constant-core infinity pole,
with no restriction on its timing relative to the transverse scale. -/
theorem GCD369CubePolynomialSource.infinity_d_eq_zero
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale) :
    S.faberConstantParameters.d = 0 := by
  rcases lt_trichotomy
      (S.infinityCommonCoefficientData hsdegree).faber.scale.p
      (2 * T.delta) with hbefore | htie | hafter
  · exact S.infinity_d_eq_zero_before_transverse hsdegree T hbefore
  · exact S.infinity_d_eq_zero_at_transverse hsdegree T htie
  · rcases lt_trichotomy
        (S.infinityCommonCoefficientData hsdegree).faber.scale.p
        (3 * T.delta) with hmiddle | hbalanced | hlate
    · exact S.infinity_d_eq_zero_singular_middle
        hsdegree T hafter hmiddle
    · exact S.infinity_d_eq_zero_singular_balanced
        hsdegree T hbalanced
    · exact S.infinity_d_eq_zero_singular_late
        hsdegree T hafter hlate

#print axioms GCD369CubePolynomialSource.infinity_d_eq_zero

/-- Every constant-core infinity pole has a genuine first transverse scale.
The only alternative would make the normalized sextic an exact cubic square,
which is incompatible with the nonzero Jacobian. -/
theorem GCD369CubePolynomialSource.infinity_transverseScale_nonempty
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0) :
    Nonempty (S.infinityCommonCoefficientData hsdegree).TransverseScale := by
  have hsplit := S.infinity_normals_zero_or_transverseScale hsdegree
  change
    ((S.infinityCommonCoefficientData hsdegree).normal2 = 0 ∧
      (S.infinityCommonCoefficientData hsdegree).normal1 = 0 ∧
      (S.infinityCommonCoefficientData hsdegree).normal0 = 0) ∨
      Nonempty (S.infinityCommonCoefficientData hsdegree).TransverseScale
    at hsplit
  rcases hsplit with hexact | htransverse
  · exact False.elim (S.infinity_exactNormals_zero_inconsistent hsdegree
      hexact.1 hexact.2.1 hexact.2.2)
  · exact htransverse

/-- Every constant-core polynomial source has zero weight-one Faber
parameter.  The exact-square alternative is impossible, while the remaining
alternative supplies the canonical first transverse scale consumed by
`infinity_d_eq_zero`. -/
theorem GCD369CubePolynomialSource.infinity_d_eq_zero_of_constantCore
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0) :
    S.faberConstantParameters.d = 0 := by
  obtain ⟨T⟩ := S.infinity_transverseScale_nonempty hsdegree
  exact S.infinity_d_eq_zero hsdegree T

#print axioms GCD369CubePolynomialSource.infinity_transverseScale_nonempty
#print axioms
  GCD369CubePolynomialSource.infinity_d_eq_zero_of_constantCore
