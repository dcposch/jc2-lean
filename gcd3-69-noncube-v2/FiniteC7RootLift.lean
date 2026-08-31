import FiniteC7Extraction

/-! # First `c7` common-root lifting identities

Once the weight-one source parameter has been killed, a weight-two `c7`
constant scaled to the square of the corresponding monomial produces the
exact arbitrary-`c7` Kuranishi packet on the three normal residues.  No
root is constructed: the recovered source coordinate already supplies it.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- Once the three normal coordinates reach half the weight-two pole scale,
the four literal scaled Faber equations produce the exact arbitrary-`c7`
Kuranishi packet on their residues. -/
theorem c7LeadingFaberRowsAt_of_bounds
    {k : Type*} [Field k] [CharZero k]
    (S : GCD369CubeHahnCommonValueData k)
    (F : GCD369CubeHahnFaberPoleData k)
    (hscale : S.normal.sextic.scale = F.scale)
    (C7 C5 C4 C3 C2 C1 R1 R2 R3 R4 : k)
    (hd : F.d = GCD369CubeHahnRegular.constant 0)
    (hc7 : F.c7 = GCD369CubeHahnRegular.constant C7)
    (hc5 : F.c5 = GCD369CubeHahnRegular.constant C5)
    (hc4 : F.c4 = GCD369CubeHahnRegular.constant C4)
    (hc3 : F.c3 = GCD369CubeHahnRegular.constant C3)
    (hc2 : F.c2 = GCD369CubeHahnRegular.constant C2)
    (hc1 : F.c1 = GCD369CubeHahnRegular.constant C1)
    (hr1 : F.rho1 = GCD369CubeHahnRegular.constant R1)
    (hr2 : F.rho2 = GCD369CubeHahnRegular.constant R2)
    (hr3 : F.rho3 = GCD369CubeHahnRegular.constant R3)
    (hr4 : F.rho4 = GCD369CubeHahnRegular.constant R4)
    (hnormal2 : (↑((2 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal2.1.orderTop)
    (hnormal1 : (↑((2 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal1.1.orderTop)
    (hnormal0 : (↑((2 * F.scale.p) / 2) : WithTop ℚ) ≤
      S.normal0.1.orderTop) :
    let T := S.transverseFactorOfBounds ((2 * F.scale.p) / 2)
      (div_pos (mul_pos (by norm_num : (0 : ℚ) < 2) F.scale.hp)
        (by norm_num))
      hnormal2 hnormal1 hnormal0
    GCD369CubeC7LeadingFaberRowsAt
      (GCD369CubeHahnRegular.constantCoeff T.Xn)
      (GCD369CubeHahnRegular.constantCoeff T.Yn)
      (GCD369CubeHahnRegular.constantCoeff T.Zn) S.u S.v C7 := by
  dsimp only
  let T := S.transverseFactorOfBounds ((2 * F.scale.p) / 2)
    (div_pos (mul_pos (by norm_num : (0 : ℚ) < 2) F.scale.hp)
      (by norm_num))
    hnormal2 hnormal1 hnormal0
  have hz := F.c7NCoeff_zero C5 C4 C3 C2 C1 R1 R2 R3 R4
    hd hc5 hc4 hc3 hc2 hc1 hr1 hr2 hr3 hr4
  rw [hc7,
    F.scale.weightedRegular_constant_eq_monomial_sq 2 (by norm_num) C7] at hz
  rcases hz with ⟨hz1, hz2, hz3, hz4⟩
  apply T.c7LeadingFaberRowsAt C7
  · have hTdelta : T.delta = (2 * F.scale.p) / 2 := rfl
    simp only [hTdelta]
    rw [hscale]
    convert hz1 using 1 <;> norm_num
  · have hTdelta : T.delta = (2 * F.scale.p) / 2 := rfl
    simp only [hTdelta]
    rw [hscale]
    convert hz2 using 1 <;> norm_num
  · have hTdelta : T.delta = (2 * F.scale.p) / 2 := rfl
    simp only [hTdelta]
    rw [hscale]
    convert hz3 using 1 <;> norm_num
  · have hTdelta : T.delta = (2 * F.scale.p) / 2 := rfl
    simp only [hTdelta]
    rw [hscale]
    convert hz4 using 1 <;> norm_num

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnCommonValueData.c7LeadingFaberRowsAt_of_bounds
