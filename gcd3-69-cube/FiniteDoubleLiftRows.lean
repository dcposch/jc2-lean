import FiniteTripleScale

/-! # Exact Hahn rows in the moving double-root chart

This is the source-independent bridge between the common-normal Faber
expansions and the second blowup.  The canonical moving-root relation rewrites
the first four zero-high numerators in the three deviation coordinates used by
the valuation induction.
-/

noncomputable section

namespace GCD369CubeHahnCommonValueData

/-- Exact first four zero-high Faber rows after passing to the canonical
moving-root deviations
`D = U + 3*r^2`, `B = Yn - r*Xn`, and `C = Zn + 2*r^2*Xn`.

No order hypothesis is used here.  Thus later coefficient extractions can be
performed uniformly at whatever common positive scale the three deviations
first occur. -/
theorem TransverseFactor.doubleRoot_zeroHigh_expansions
    {k : Type*} [Field k] [CharZero k]
    {S : GCD369CubeHahnCommonValueData k} (T : S.TransverseFactor)
    (r : GCD369CubeHahnRegular k)
    (hroot : 2 * S.cubicU * r + 3 * S.cubicV = 0) :
    let A := T.Xn
    let D := S.cubicU + 3 * r ^ 2
    let B := T.Yn - r * A
    let C := T.Zn + 2 * r ^ 2 * A
    let H := GCD369CubeHahnRegular.monomial T.delta T.hdelta.le
    (729 * GCD369CubeFaberN1
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4 =
      (-32 * (729 *
        (A ^ 2 * D - 2 * A * B * r - B ^ 2 - 2 * A * C))) * H ^ 2) ∧
    (2187 * GCD369CubeFaberN2
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4 =
      (32 * (-1458 *
        (2 * A ^ 2 * r * D - 3 * A * B * r ^ 2 -
          3 * A * C * r + 3 * A * B * D - 3 * B * C))) * H ^ 2) ∧
    (GCD369CubeFaberN3
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4 =
      (128 *
        (-2 * A ^ 2 * r ^ 2 * D + 6 * B ^ 2 * r ^ 2 +
          2 * A ^ 2 * D ^ 2 - 2 * B ^ 2 * D - 4 * A * C * D +
          3 * C ^ 2)) * H ^ 2 - (64 * A ^ 3) * H ^ 3) ∧
    (6561 * GCD369CubeFaberN4
        S.normal.sextic.scale.regular0 S.normal.sextic.scale.regular1
        S.normal.sextic.scale.regular2 S.normal.sextic.scale.regular3
        S.normal.sextic.scale.regular4 =
      (32 * (4374 * (-3 * r ^ 2 + D) *
        (A * B * r ^ 2 + 2 * B ^ 2 * r + A * C * r +
          3 * A * B * D - 3 * B * C))) * H ^ 2 -
        (314928 * (r * A + B) * A ^ 2) * H ^ 3) := by
  dsimp only
  let A : GCD369CubeHahnRegular k := T.Xn
  let D : GCD369CubeHahnRegular k := S.cubicU + 3 * r ^ 2
  let B : GCD369CubeHahnRegular k := T.Yn - r * A
  let C : GCD369CubeHahnRegular k := T.Zn + 2 * r ^ 2 * A
  let e : GCD369CubeHahnRegular k := S.cubicV - 2 * r ^ 3
  have hA : T.Xn = A := rfl
  have hY : T.Yn = r * A + B := by
    dsimp only [B]
    ring
  have hZ : T.Zn = -2 * r ^ 2 * A + C := by
    dsimp only [C]
    ring
  have hU : S.cubicU = -3 * r ^ 2 + D := by
    dsimp only [D]
    ring
  have hV : S.cubicV = 2 * r ^ 3 + e := by
    dsimp only [e]
    ring
  have hre : 3 * e + 2 * D * r = 0 := by
    dsimp only [e, D]
    linear_combination hroot
  have hrow1 := GCD369CubeDoubleBlowupRow1 A B C r D
  have hrow2 := GCD369CubeDoubleBlowupRow2 A B C r D e hre
  have hrow3 := GCD369CubeDoubleBlowupRow3 A B C r D e hre
  have hrow4 := GCD369CubeDoubleBlowupRow4 A B C r D e hre
  have h1 := T.zeroHighN1Expansion
  have h2 := T.zeroHighN2Expansion
  have h3 := T.zeroHighN3Expansion
  have h4 := T.zeroHighN4Expansion
  rw [hA, hY, hZ, hU, hrow1] at h1
  rw [hA, hY, hZ, hU, hV, hrow2] at h2
  rw [hA, hY, hZ, hU, hV, hrow3] at h3
  rw [hA, hY, hZ, hU, hV, hrow4] at h4
  exact ⟨by simpa only [A, D, B, C] using h1,
    by simpa only [A, D, B, C] using h2,
    by simpa only [A, D, B, C] using h3,
    by simpa only [A, D, B, C] using h4⟩

end GCD369CubeHahnCommonValueData

#print axioms GCD369CubeHahnCommonValueData.TransverseFactor.doubleRoot_zeroHigh_expansions
