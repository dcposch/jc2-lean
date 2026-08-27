import InfinityDLoad
import FiniteC7EarlyNormal

/-! # Zero-load rows before the weight-two load at infinity

After the weight-one coefficient has vanished, a first transverse normal jet
strictly below the weight-two pole scale sees none of the later source or
target loads.  Its residue therefore satisfies the four universal zero-load
normal rows.  This argument uses only the infinity coefficient packet.
-/

noncomputable section

namespace GCD369CubeHahnCommonCoefficientData

/-- At the canonical coefficient transverse scale, vanishing of `d` and the
strict inequality `2 δ < 2 p` give the four universal zero-load rows. -/
theorem TransverseScale.zeroLoadLeadingRows_before_c7_coeff
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (hd : D.faber.d = 0)
    (hearly : 2 * T.delta < 2 * D.faber.scale.p) :
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
  have hz := D.faber.zeroHighNCoeff_zero_before_c7 hd
    (2 * T.delta) (mul_nonneg (by norm_num) T.hdelta.le) hearly
  rcases hz with ⟨h1, h2, h3, h4⟩
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
      convert T.zeroHighN1Coeff using 1 <;> norm_num
    rw [hc] at h1
    exact (mul_eq_zero.mp h1).resolve_left (by norm_num)
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
      convert T.zeroHighN2Coeff using 1 <;> norm_num
    rw [hc] at h2
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
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
            D.faber.scale.regular4).1.coeff (2 * T.delta) := by
      exact GCD369CubeHahnRegular.coeff_nat_mul 243 _ _
    rw [hcoeff] at h3
    have h3' :
        (GCD369CubeFaberN3
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4).1.coeff (2 * T.delta) = 0 :=
      (mul_eq_zero.mp h3).resolve_left (by norm_num)
    have hc :
        (GCD369CubeFaberN3
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4).1.coeff (2 * T.delta) =
        128 * GCD369CubeNormalRow3
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v := by
      convert T.zeroHighN3Coeff using 1 <;> norm_num
    rw [hc] at h3'
    exact (mul_eq_zero.mp h3').resolve_left (by norm_num)
  · have hc :
        (6561 * GCD369CubeFaberN4
          D.faber.scale.regular0 D.faber.scale.regular1
          D.faber.scale.regular2 D.faber.scale.regular3
          D.faber.scale.regular4).1.coeff (2 * T.delta) =
        32 * GCD369CubeNormalRow4
          (GCD369CubeHahnRegular.constantCoeff T.Xn)
          (GCD369CubeHahnRegular.constantCoeff T.Yn)
          (GCD369CubeHahnRegular.constantCoeff T.Zn) D.u D.v := by
      convert T.zeroHighN4Coeff using 1 <;> norm_num
    rw [hc] at h4
    exact (mul_eq_zero.mp h4).resolve_left (by norm_num)

/-- Constant-load spelling of the same result.  Only literal vanishing of
`d` is needed; all weights at least two are eliminated by their Hahn order. -/
theorem TransverseScale.zeroLoadLeadingRows_before_c7_of_constants
    {k : Type*} [Field k] [CharZero k]
    {D : GCD369CubeHahnCommonCoefficientData k} (T : D.TransverseScale)
    (C7 C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hd : D.faber.d = GCD369CubeHahnRegular.constant 0)
    (_hc7 : D.faber.c7 = GCD369CubeHahnRegular.constant C7)
    (_hc5 : D.faber.c5 = GCD369CubeHahnRegular.constant C5)
    (_hc4 : D.faber.c4 = GCD369CubeHahnRegular.constant C4)
    (_hc3 : D.faber.c3 = GCD369CubeHahnRegular.constant C3)
    (_hc2 : D.faber.c2 = GCD369CubeHahnRegular.constant C2)
    (_hc1 : D.faber.c1 = GCD369CubeHahnRegular.constant C1)
    (_hr1 : D.faber.rho1 = GCD369CubeHahnRegular.constant R1)
    (_hr2 : D.faber.rho2 = GCD369CubeHahnRegular.constant R2)
    (_hr3 : D.faber.rho3 = GCD369CubeHahnRegular.constant R3)
    (_hr4 : D.faber.rho4 = GCD369CubeHahnRegular.constant R4)
    (hearly : 2 * T.delta < 2 * D.faber.scale.p) :
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
  apply T.zeroLoadLeadingRows_before_c7_coeff
  · have hzero : GCD369CubeHahnRegular.constant (0 : k) = 0 := by
      apply Subtype.ext
      simp
    simpa only [hzero] using hd
  · exact hearly

end GCD369CubeHahnCommonCoefficientData

namespace GCD369CubePolynomialSource

/-- Source-facing zero-load row packet in the strict post-`d`, pre-`c7`
region of the constant-core infinity branch. -/
theorem infinity_zeroLoadLeadingRows_before_c7
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hd0 : S.faberConstantParameters.d = 0)
    (hearly :
      2 * T.delta <
        2 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p) :
    GCD369CubeNormalRow1
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn)
        (S.infinityCommonCoefficientData hsdegree).u = 0 ∧
    GCD369CubeNormalRow2
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn)
        (S.infinityCommonCoefficientData hsdegree).u
        (S.infinityCommonCoefficientData hsdegree).v = 0 ∧
    GCD369CubeNormalRow3
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn)
        (S.infinityCommonCoefficientData hsdegree).u
        (S.infinityCommonCoefficientData hsdegree).v = 0 ∧
    GCD369CubeNormalRow4
        (GCD369CubeHahnRegular.constantCoeff T.Xn)
        (GCD369CubeHahnRegular.constantCoeff T.Yn)
        (GCD369CubeHahnRegular.constantCoeff T.Zn)
        (S.infinityCommonCoefficientData hsdegree).u
        (S.infinityCommonCoefficientData hsdegree).v = 0 := by
  have hd :
      (S.infinityCommonCoefficientData hsdegree).faber.d = 0 := by
    let hpole := S.infinityNormalizedCoeffPole_of_constantCore hsdegree
    obtain ⟨hd, _hc7, _hc5, _hc4, _hc3, _hc2, _hc1,
        _hr1, _hr2, _hr3, _hr4⟩ :=
      S.infinityFaberPoleData_constant_loads hpole
    rw [S.infinityCommonCoefficientData_faber hsdegree]
    have hzero : GCD369CubeHahnRegular.constant (0 : k) = 0 := by
      apply Subtype.ext
      simp
    simpa only [hd0, hzero] using hd
  exact T.zeroLoadLeadingRows_before_c7_coeff hd hearly

end GCD369CubePolynomialSource

#print axioms
  GCD369CubeHahnCommonCoefficientData.TransverseScale.zeroLoadLeadingRows_before_c7_coeff
#print axioms GCD369CubePolynomialSource.infinity_zeroLoadLeadingRows_before_c7
