import FiniteDoubleZeroLoadCubicRho2

/-! # Lifted zero-load obstruction before `rho2`

The source-facing row lift supplies exact half/full quadratic coordinates.
The zero-load cubic calculation then excludes every singular transverse jet
strictly before the weight-eleven load, with no source-root case split.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

set_option maxHeartbeats 4000000

/-- Once all earlier loads vanish, a transverse double-root jet cannot lie
strictly below the `rho2` cutoff. -/
theorem TransverseFactor.doubleRoot_inconsistent_before_rho2
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (hd : F.d = 0) (hc7 : F.c7 = 0) (hc5 : F.c5 = 0)
    (hc4 : F.c4 = 0) (hc3 : F.c3 = 0) (hc2 : F.c2 = 0)
    (hc1 : F.c1 = 0) (hr1 : F.rho1 = 0)
    (hp : 3 * T.delta < 11 * F.scale.p)
    (r : GCD369CubeHahnRegular k) (r0 A0 : k)
    (hr0 : r0 ≠ 0) (hA0 : A0 ≠ 0)
    (hr : GCD369CubeHahnRegular.constantCoeff r = r0)
    (hu : GCD369CubeHahnRegular.constantCoeff S.cubicU = -3 * r0 ^ 2)
    (hX : GCD369CubeHahnRegular.constantCoeff T.Xn = A0)
    (hY : GCD369CubeHahnRegular.constantCoeff T.Yn = r0 * A0)
    (hZ : GCD369CubeHahnRegular.constantCoeff T.Zn = -2 * r0 ^ 2 * A0)
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0) : False := by
  obtain ⟨hDfull, B, hYcoord, hQfull⟩ :=
    T.doubleRoot_deviations_order_delta_from_source_before_rho2
      F hscale hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 (le_of_lt hp) r r0 A0 hr0 hA0 hr hu hX hY hZ
        hroot
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let M : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial (T.delta / 2)
      (div_nonneg T.hdelta.le (by norm_num))
  let D : GCD369CubeHahnRegular k := S.cubicU + 3 * r ^ 2
  let d : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift D T.delta hDfull
  let Ztail : GCD369CubeHahnRegular k :=
    T.Zn + 2 * r ^ 2 * T.Xn + M * r * B
  let q : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift Ztail T.delta hQfull
  have hDfact : H * d = D := by
    exact GCD369CubeHahnRegular.monomial_mul_shift
      D T.delta T.hdelta.le hDfull
  have hQfact : H * q = Ztail := by
    exact GCD369CubeHahnRegular.monomial_mul_shift
      Ztail T.delta T.hdelta.le hQfull
  have hM2 : M ^ 2 = H := by
    apply Subtype.ext
    change (HahnSeries.single (T.delta / 2) (1 : k)) ^ 2 =
      HahnSeries.single T.delta 1
    rw [pow_two, HahnSeries.single_mul_single]
    congr 1 <;> ring
  have hDcoord : S.cubicU + 3 * r ^ 2 = M ^ 2 * d := by
    rw [hM2]
    exact hDfact.symm
  have hBcoord : T.Yn - r * T.Xn = M * B := by
    simpa only [M] using (show T.Yn - r * T.Xn =
        GCD369CubeHahnRegular.monomial (T.delta / 2)
          (div_nonneg T.hdelta.le (by norm_num)) * B by
      linear_combination hYcoord)
  have hCcoord : T.Zn + 2 * r ^ 2 * T.Xn =
      M ^ 2 * q - M * r * B := by
    dsimp only [Ztail] at hQfact
    rw [hM2]
    linear_combination -hQfact
  exact T.doubleRoot_zeroLoad_balanced_cubic_inconsistent_before_rho2
    F hscale hd hc7 hc5 hc4 hc3 hc2 hc1 hr1 hp r d B q r0 A0 hr0 hA0 hr hX hY
      hroot hDcoord hBcoord hCcoord

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_inconsistent_before_rho2
