import FiniteEarlyLoadRouting
import ArbitraryLoads

/-! # Arbitrary early loads strictly before the first transverse normal

Any prescribed positive scale strictly below the canonical first
transverse order produces a zero-residue jet.  An arbitrary nonzero
early Faber load on those residues therefore forbids a common root,
contradicting the recovered leading cubic root.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- An arbitrary nonzero early Faber load cannot occupy a prescribed
positive scale strictly before the canonical first transverse normal. -/
theorem TransverseScale.arbitraryEarlyLoad_strict_before_transverse
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (s : ℚ) (hs : 0 < s) (hbefore : s < T.delta) :
    let U := S.transverseFactorOfBounds s hs
      ((WithTop.coe_le_coe.mpr hbefore.le).trans T.normal_orderTop_lower.1)
      ((WithTop.coe_le_coe.mpr hbefore.le).trans T.normal_orderTop_lower.2.1)
      ((WithTop.coe_le_coe.mpr hbefore.le).trans T.normal_orderTop_lower.2.2)
    GCD369CubeArbitraryEarlyFaberLoad
      (GCD369CubeHahnRegular.constantCoeff U.Xn)
      (GCD369CubeHahnRegular.constantCoeff U.Yn)
      (GCD369CubeHahnRegular.constantCoeff U.Zn) S.u S.v → False := by
  dsimp only
  intro load
  let U := S.transverseFactorOfBounds s hs
    ((WithTop.coe_le_coe.mpr hbefore.le).trans T.normal_orderTop_lower.1)
    ((WithTop.coe_le_coe.mpr hbefore.le).trans T.normal_orderTop_lower.2.1)
    ((WithTop.coe_le_coe.mpr hbefore.le).trans T.normal_orderTop_lower.2.2)
  have hX : GCD369CubeHahnRegular.constantCoeff U.Xn = 0 := by
    dsimp only [U, transverseFactorOfBounds]
    rw [GCD369CubeHahnRegular.constantCoeff_shift]
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact (WithTop.coe_lt_coe.mpr hbefore).trans_le T.normal_orderTop_lower.1
  have hY : GCD369CubeHahnRegular.constantCoeff U.Yn = 0 := by
    dsimp only [U, transverseFactorOfBounds]
    rw [GCD369CubeHahnRegular.constantCoeff_shift]
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact (WithTop.coe_lt_coe.mpr hbefore).trans_le T.normal_orderTop_lower.2.1
  have hZ : GCD369CubeHahnRegular.constantCoeff U.Zn = 0 := by
    dsimp only [U, transverseFactorOfBounds]
    rw [GCD369CubeHahnRegular.constantCoeff_shift]
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    exact (WithTop.coe_lt_coe.mpr hbefore).trans_le T.normal_orderTop_lower.2.2
  apply load.noCommonRoot
    (GCD369CubeHahnRegular.constantCoeff S.normal.sextic.regularX)
    S.leadingCubicRoot
  rw [hX, hY, hZ]
  ring

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.arbitraryEarlyLoad_strict_before_transverse
