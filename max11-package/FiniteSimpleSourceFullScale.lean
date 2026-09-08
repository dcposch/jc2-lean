import FiniteSimpleSourceLateOrder

/-! # Full-scale coordinates in the late simple-root chart

The late source inequalities promote both the simple-root displacement and
the nominal half-scale normal correction to the intrinsic `delta` scale.
This file packages that promotion as literal factorizations, ready for the
tied first-load coefficient calculation.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- Once `w` starts at `delta` and `B` starts at `delta / 2`, both `w` and
the product of the half-scale monomial with `B` factor through the full
`delta` monomial. -/
theorem TransverseFactor.simpleRoot_fullScale_factorization
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (w B : GCD369CubeHahnRegular k)
    (hw : (↑T.delta : WithTop ℚ) ≤ w.1.orderTop)
    (hB : (↑(T.delta / 2) : WithTop ℚ) ≤ B.1.orderTop) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    let M := GCD369CubeHahnRegular.monomial (T.delta / 2)
      (div_nonneg T.hdelta.le (by norm_num))
    ∃ s b : GCD369CubeHahnRegular k,
      w = H * s ∧ M * B = H * b := by
  dsimp only
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let M : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial (T.delta / 2)
      (div_nonneg T.hdelta.le (by norm_num))
  let s : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift w T.delta hw
  have hM := GCD369CubeHahnRegular.monomial_orderTop_and_leadingCoeff
    (k := k) (T.delta / 2)
      (div_nonneg T.hdelta.le (by norm_num))
  have hMB0 := GCD369CubeHahnRegular.mul_orderTop_lower
    M B (T.delta / 2) (T.delta / 2)
      (by simpa only [M] using hM.1.ge) hB
  have hMB : (↑T.delta : WithTop ℚ) ≤ (M * B).1.orderTop := by
    simpa only [show T.delta / 2 + T.delta / 2 = T.delta by ring]
      using hMB0
  let b : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.shift (M * B) T.delta hMB
  refine ⟨s, b, ?_, ?_⟩
  · exact (GCD369CubeHahnRegular.monomial_mul_shift
      w T.delta T.hdelta.le hw).symm
  · exact (GCD369CubeHahnRegular.monomial_mul_shift
      (M * B) T.delta T.hdelta.le hMB).symm

/-- The half-scale simple-root normal coordinates therefore rewrite with
only full-`delta` corrections. -/
theorem TransverseFactor.simpleRoot_sourceLate_fullScale_coordinates
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r w B B2 C2 : GCD369CubeHahnRegular k)
    (hw : (↑T.delta : WithTop ℚ) ≤ w.1.orderTop)
    (hB : (↑(T.delta / 2) : WithTop ℚ) ≤ B.1.orderTop)
    (hY : T.Yn = r * T.Xn +
      GCD369CubeHahnRegular.monomial (T.delta / 2)
        (div_nonneg T.hdelta.le (by norm_num)) * B +
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * B2)
    (hZ : T.Zn = -2 * r ^ 2 * T.Xn -
      GCD369CubeHahnRegular.monomial (T.delta / 2)
        (div_nonneg T.hdelta.le (by norm_num)) * r * B +
      GCD369CubeHahnRegular.monomial T.delta T.hdelta.le * C2) :
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    ∃ s b : GCD369CubeHahnRegular k,
      w = H * s ∧
      T.Yn = r * T.Xn + H * (b + B2) ∧
      T.Zn = -2 * r ^ 2 * T.Xn + H * (-r * b + C2) := by
  dsimp only
  let H : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
  let M : GCD369CubeHahnRegular k :=
    GCD369CubeHahnRegular.monomial (T.delta / 2)
      (div_nonneg T.hdelta.le (by norm_num))
  obtain ⟨s, b, hwfact, hBfact⟩ :=
    T.simpleRoot_fullScale_factorization w B hw hB
  refine ⟨s, b, by simpa only [H] using hwfact, ?_, ?_⟩
  · rw [hY]
    simpa only [H, M] using (show
      r * T.Xn + M * B + H * B2 = r * T.Xn + H * (b + B2) by
        rw [hBfact]
        ring)
  · rw [hZ]
    simpa only [H, M] using (show
      -2 * r ^ 2 * T.Xn - M * r * B + H * C2 =
        -2 * r ^ 2 * T.Xn + H * (-r * b + C2) by
        rw [show M * r * B = r * (M * B) by ring, hBfact]
        ring)

end GCD369CubeHahnCommonValueData

#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.simpleRoot_fullScale_factorization
#print axioms
  GCD369CubeHahnCommonValueData.TransverseFactor.simpleRoot_sourceLate_fullScale_coordinates
