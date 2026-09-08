import InfinityRho2Assembly
import InfinityLaterHandoff

/-! # Constant-core exclusion at infinity

The complete target-normalized load fan through weight eleven feeds the
terminal later-load handoff, ruling out a polynomial source with constant
core.
-/

noncomputable section

namespace GCD369CubePolynomialSource

/-- A plane Jacobian source in the `3`--`6`--`9` cube setup cannot have
constant core. -/
theorem infinity_constantCore_empty
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (S : GCD369CubePolynomialSource k) (hsdegree : S.s.natDegree = 0) :
    False := by
  obtain ⟨T⟩ := S.targetNormalized_infinity_transverseScale_nonempty hsdegree
  obtain ⟨hc7, hc5, hc4, hc2, hc1, hrho1, hrho2⟩ :=
    S.targetNormalized_infinity_loads_through_rho2 hsdegree T
  exact S.targetNormalized_earlyLoads_empty_of_constantCore hsdegree
    hc7 hc5 hc4 hc2 hc1 hrho1 hrho2

end GCD369CubePolynomialSource

#print axioms GCD369CubePolynomialSource.infinity_constantCore_empty
