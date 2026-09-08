import FiniteRho2SourceRootSplit
import FiniteDoubleEndpointCoordinatesRho2
import FiniteSimpleSourceEndpointResidueRho2
import FiniteDoubleRho2LoadEndpointLift

/-! # The balanced active-`rho2` singular source branch -/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- If the weight-eleven `rho2` load meets the intrinsic cubic scale exactly,
the singular finite source branch is inconsistent. -/
theorem TransverseScale.singular_source_inconsistent_at_active_rho2_of_eq
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseScale)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (R Rho3 Rho4 : k)
    (hdNormal : S.normal.d = 0)
    (hc7Normal : S.normal.c7 = 0)
    (hc5Normal : S.normal.c5 = 0)
    (hc4Normal : S.normal.c4 = 0)
    (hc3Normal : S.normal.c3 = 0)
    (hc2Normal : S.normal.c2 = 0)
    (hc1Normal : S.normal.c1 = 0)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant 0)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant 0)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant 0)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant 0)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant 0)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant 0)
    (hrho1 : F.rho1 = GCD369CubeHahnRegular.constant 0)
    (hrho2 : F.rho2 = GCD369CubeHahnRegular.constant R)
    (hrho3 : F.rho3 = GCD369CubeHahnRegular.constant Rho3)
    (hrho4 : F.rho4 = GCD369CubeHahnRegular.constant Rho4)
    (hEq : 11 * F.scale.p = 3 * T.delta) : False := by
  have hd0 : F.d = 0 := by simpa using hd
  have hc70 : F.c7 = 0 := by simpa using hc7
  have hc50 : F.c5 = 0 := by simpa using hc5
  have hc40 : F.c4 = 0 := by simpa using hc4
  have hc30 : F.c3 = 0 := by simpa using hc3
  have hc20 : F.c2 = 0 := by simpa using hc2
  have hc10 : F.c1 = 0 := by simpa using hc1
  have hr10 : F.rho1 = 0 := by simpa using hrho1
  have hp : 3 * T.delta ≤ 11 * F.scale.p := le_of_eq hEq.symm
  obtain ⟨r0, hr0, hXne, hu, hv, hY, hZ, hx⟩ :=
    T.source_coordinate_is_simpleRoot_before_rho2
      F hscale hdNormal hc7Normal hc5Normal hc4Normal hc3Normal hc2Normal
      hc1Normal hd0 hc70 hc50 hc40 hc30 hc20 hc10 hr10 hp
  have huc : GCD369CubeHahnRegular.constantCoeff S.cubicU =
      -3 * r0 ^ 2 := by
    rw [S.constantCoeff_cubicU, hu]
  have hvc : GCD369CubeHahnRegular.constantCoeff S.cubicV =
      2 * r0 ^ 3 := by
    rw [S.constantCoeff_cubicV, hv]
  have hUne : GCD369CubeHahnRegular.constantCoeff S.cubicU ≠ 0 := by
    rw [huc]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hr0)
  let r : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.movingDoubleRoot S.cubicU S.cubicV hUne
  have hr : GCD369CubeHahnRegular.constantCoeff r = r0 :=
    GCD369CubeHahnRegular.constantCoeff_movingDoubleRoot
      S.cubicU S.cubicV hUne r0 huc hvc hr0
  have hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0 :=
    GCD369CubeHahnRegular.movingDoubleRoot_relation
      S.cubicU S.cubicV hUne
  obtain ⟨d, B, q, hD, hB, hC⟩ :=
    T.factor.doubleRoot_quadratic_coordinates_at_rho2
      F hscale hd0 hc70 hc50 hc40 hc30 hc20 hc10 hr10
      (by simpa only [TransverseScale.factor] using hEq)
      r r0 (GCD369CubeHahnRegular.constantCoeff T.Xn)
      hr0 hXne hr huc (by rfl) hY hZ hroot
  have hEqNormal : 11 * S.normal.sextic.scale.p =
      3 * T.factor.delta := by
    rw [hscale]
    simpa only [TransverseScale.factor] using hEq
  have hB0 := T.factor.simpleRoot_quadratic_B_residue_zero_at_rho2
    hdNormal hc7Normal hc5Normal hc4Normal hc3Normal hc2Normal hc1Normal
    hEqNormal r0 (GCD369CubeHahnRegular.constantCoeff T.Xn) r d B q
    hr0 hXne hr hx (by rfl) hroot hD hB hC
  exact T.factor.doubleRoot_rho2Load_source_inconsistent_of_eq
    F hscale R Rho3 Rho4
    hd hc7 hc5 hc4 hc3 hc2 hc1 hrho1 hrho2 hrho3 hrho4
    r r0 (GCD369CubeHahnRegular.constantCoeff T.Xn)
    hr0 hXne hr hu hv (by rfl) hY hroot
    (by simpa only [TransverseScale.factor] using hEq)
    d B q hB0 hD hB hC

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseScale.singular_source_inconsistent_at_active_rho2_of_eq
