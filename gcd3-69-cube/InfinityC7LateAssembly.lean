import InfinityC7LateRows
import InfinityC7Late

/-! # Assembly of the singular late `c7` branch at infinity

The post-`d` zero-load rows put the first transverse residue in the standard
double-root chart.  When its cubic-order term is still strictly before the
weight-two load, the existing infinity terminal-order obstruction closes the
branch without any nonvanishing assumption on `c7`.
-/

noncomputable section

namespace GCD369CubePolynomialSource

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- After `d = 0`, the region `3 δ < 2 p` is inconsistent for every
constant-core infinity source, independently of whether `c7` vanishes. -/
theorem infinity_c7_singular_late_inconsistent
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0)
    (T : (S.infinityCommonCoefficientData hsdegree).TransverseScale)
    (hd0 : S.faberConstantParameters.d = 0)
    (hlate :
      3 * T.delta <
        2 * (S.infinityCommonCoefficientData hsdegree).faber.scale.p) :
    False := by
  let D := S.infinityCommonCoefficientData hsdegree
  have hearly : 2 * T.delta < 2 * D.faber.scale.p := by
    have hdelta := T.hdelta
    linarith
  obtain ⟨h1, h2, h3, h4⟩ :=
    S.infinity_zeroLoadLeadingRows_before_c7 hsdegree T hd0 hearly
  obtain ⟨r, hX, hu, hv, hY, hZ⟩ :=
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
  exact S.infinity_c7_singular_late_inconsistent_of_parametrization
    hsdegree T hd0 hdisc r
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      hr hX hu rfl hY hZ hlate

end GCD369CubePolynomialSource

#print axioms GCD369CubePolynomialSource.infinity_c7_singular_late_inconsistent
