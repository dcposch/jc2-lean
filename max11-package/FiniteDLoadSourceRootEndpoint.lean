import FiniteLateDoubleSource
import FiniteSimpleSourceEndpointCoordinates
import FiniteDoubleLoadEndpointLift

/-! # The balanced active-`d` singular source branch

At `p = 3 * delta`, the literal source first selects the simple root of the
singular leading cubic.  Its exact half-scale quadratic coordinates have
zero `B` residue, so the balanced four-row `d`-load system is inconsistent.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- A nonzero weight-one `d` load cannot meet the intrinsic cubic scale
exactly on the singular finite source branch. -/
theorem TransverseScale.singular_source_inconsistent_at_active_d_of_eq
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant D0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hrho1 : F.rho1 = GCD369CubeHahnRegular.constant Rho1)
    (hrho2 : F.rho2 = GCD369CubeHahnRegular.constant Rho2)
    (hrho3 : F.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : F.rho4 = GCD369CubeHahnRegular.constant Rho4)
    (hEq : F.scale.p = 3 * T.delta) : False := by
  have hp : 3 * T.delta ≤ F.scale.p := le_of_eq hEq.symm
  obtain ⟨r0, hr0, hXne, hu, hv, hY, hZ, hx⟩ :=
    T.source_coordinate_is_simpleRoot_at_or_after_cubic F hscale
      D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4 hp
  have huc : GCD369CubeHahnRegular.constantCoeff S.cubicU =
      -3 * r0 ^ 2 := by
    rw [S.constantCoeff_cubicU, hu]
  have hvc : GCD369CubeHahnRegular.constantCoeff S.cubicV =
      2 * r0 ^ 3 := by
    rw [S.constantCoeff_cubicV, hv]
  obtain ⟨r, d, Bn, q, hr, hroot, hD, hB, hC, hBn0⟩ :=
    T.factor.simpleRoot_zeroQuadratic_coordinates_from_source
      F hscale D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
      hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
      (by simpa only [TransverseScale.factor] using hp)
      r0 (GCD369CubeHahnRegular.constantCoeff T.Xn)
      hr0 hXne huc hvc hx (by rfl) hY hZ
  exact T.factor.doubleRoot_dLoad_source_inconsistent_of_eq
    F hscale D0 C7 C5 C4 C3 C2 C1 Rho1 Rho2 Rho3 Rho4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
    r r0 (GCD369CubeHahnRegular.constantCoeff T.Xn)
    hr0 hXne hr hu hv (by rfl) hY hroot
    (by simpa only [TransverseScale.factor] using hEq)
    d Bn q hBn0 hD hB hC

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.singular_source_inconsistent_at_active_d_of_eq
