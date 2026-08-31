import FiniteC2SourceRootSplit
import FiniteSimpleSourceEndpointCoordinatesC2
import FiniteDoubleC2LoadEndpointLift

/-! # The balanced active-`c2` singular source branch

At `7 * p = 3 * delta`, the literal source still excludes the double
source root.  The remaining simple source root supplies exact quadratic
moving-root coordinates whose half-scale `B` residue vanishes, and the
balanced four-row load system is then inconsistent.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- If the weight-seven `c2` load meets the intrinsic cubic scale exactly,
the singular finite source branch is inconsistent. -/
theorem TransverseScale.singular_source_inconsistent_at_active_c2_of_eq
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (C2 C1 Rho1 Rho2 Rho3 Rho4 : k)
    (hdNormal : S.normal.d = 0)
    (hc7Normal : S.normal.c7 = 0)
    (hc5Normal : S.normal.c5 = 0)
    (hc4Normal : S.normal.c4 = 0)
    (hc3Normal : S.normal.c3 = 0)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hrho1 : F.rho1 = GCD369CubeHahnRegular.constant Rho1)
    (hrho2 : F.rho2 = GCD369CubeHahnRegular.constant Rho2)
    (hrho3 : F.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : F.rho4 = GCD369CubeHahnRegular.constant Rho4)
    (hEq : 7 * F.scale.p = 3 * T.delta) : False := by
  have hd0 : F.d = 0 := by simpa using hd
  have hc70 : F.c7 = 0 := by simpa using hc7
  have hc50 : F.c5 = 0 := by simpa using hc5
  have hc40 : F.c4 = 0 := by simpa using hc4
  have hc30 : F.c3 = 0 := by simpa using hc3
  have hp : 3 * T.delta ≤ 7 * F.scale.p := by
    exact le_of_eq hEq.symm
  obtain ⟨r0, hr0, hXne, hu, hv, hY, hZ, hx⟩ :=
    T.source_coordinate_is_simpleRoot_before_c2
      F hscale hdNormal hc7Normal hc5Normal hc4Normal hc3Normal
      hd0 hc70 hc50 hc40 hc30 hp
  have huc : GCD369CubeHahnRegular.constantCoeff S.cubicU =
      -3 * r0 ^ 2 := by
    rw [S.constantCoeff_cubicU, hu]
  have hvc : GCD369CubeHahnRegular.constantCoeff S.cubicV =
      2 * r0 ^ 3 := by
    rw [S.constantCoeff_cubicV, hv]
  obtain ⟨r, d, Bn, q, hr, hroot, hD, hB, hC, hBn0⟩ :=
    T.factor.simpleRoot_zeroQuadratic_coordinates_from_source_before_c2
      F hscale hdNormal hc7Normal hc5Normal hc4Normal hc3Normal
      hd0 hc70 hc50 hc40 hc30
      (by simpa only [TransverseScale.factor] using hp)
      r0 (GCD369CubeHahnRegular.constantCoeff T.Xn)
      hr0 hXne huc hvc hx (by rfl) hY hZ
  exact T.factor.doubleRoot_c2Load_source_inconsistent_of_eq
    F hscale C2 C1 Rho1 Rho2 Rho3 Rho4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
    r r0 (GCD369CubeHahnRegular.constantCoeff T.Xn)
    hr0 hXne hr hu hv (by rfl) hY hroot
    (by simpa only [TransverseScale.factor] using hEq)
    d Bn q hBn0 hD hB hC

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.singular_source_inconsistent_at_active_c2_of_eq
