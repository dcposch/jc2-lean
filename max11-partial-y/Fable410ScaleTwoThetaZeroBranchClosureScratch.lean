import Fable410ScaleTwoThetaSourceBridgeScratch
import Fable410ScaleTwoIotaZeroPolarBranchScratch

/-! # Closure of the theta-forced zero-`p₁` branch of the `(4,10)` face

On the nonzero first face `H = h²` and `N = 5 p₃ H³ - 2 q₉ = λ h⁹` with
`h.natDegree = 1`, the theta source bridge proved `p₁(a) = 0`
unconditionally (`thetaBridge_pOneVanishes410`), while the zero-`p₁`
polar branch of the iota bridge was opened only under the branch
hypothesis `p₁(a) = 0`.  This file combines the two: the branch
hypothesis is discharged by `θ`, so the zero-`p₁` packet holds on every
nonzero face, and the two towers are merged into the sharpest exact
residual available on the branch.  The complementary hypothesis
`λ + 4 t₂(a) = 0` is neither assumed nor needed anywhere.

First, the `θ` tower gains its own second `h`-factor, mirroring the
zero-branch refinement of `ι`: the exposed root vanishings `v₁(a) = 0`
and `Θ₂(a) = 0` promote the peel to `Θ₃ = h₀² ν₂`, `Θ₂ = h₀ μ₂`, and
cancelling `h₀` in the chain leaves the exact peeled identity
`ν₂ + μ₂ + Θ₁ + h₀ Θ₀ = c_θ h₀` with root tie
`ν₂(a) + μ₂(a) + 16777216 q₁(a) = 0`
(`nonzeroFace410_thetaZeroBranchClosurePacket`).

Second, the retained iota cofactors of the zero branch
(`ι₃ = h₀² w₂`, `ι₂ = h₀ u₂`, `w₂ + u₂ + ι₁ + h₀ ι₀ = c h₀`,
`w₂(a) + u₂(a) = 2 q₁(a) t₂(a)`) are combined with the theta tie and
the degree-`0` Keller row `p₀'(a) q₁(a) = j`.  Eliminating `q₁(a)`
between the two towers yields the `q₁`-free cross-tower tie
`8388608 (w₂(a) + u₂(a)) + t₂(a) (ν₂(a) + μ₂(a)) = 0`
(`thetaZeroBranch_crossTowerTie410`), and eliminating it against the
Keller row yields the linked pair
`p₀'(a) (ν₂(a) + μ₂(a)) + 16777216 j = 0` and
`p₀'(a) (w₂(a) + u₂(a)) = 2 j t₂(a)`: for `j ≠ 0` the three root
sums `q₁(a)`, `ν₂(a) + μ₂(a)`, `w₂(a) + u₂(a)` are each determined by
`(j, t₂(a))` up to the single unit `p₀'(a)`.

Third, for a nonzero Keller constant the closure is sharpened to
units: `p₀'(a) ≠ 0`, `q₁(a) ≠ 0`, `ν₂(a) + μ₂(a) ≠ 0`, and
`w₂(a) + u₂(a) ≠ 0` whenever `t₂(a) ≠ 0`
(`thetaZeroBranch_unitClosure410`).

Nothing here closes the face: no contradiction is derived, the
cofactors `ν₂, μ₂, w₂, u₂` are pinned only in the sums `ν₂ + μ₂` and
`w₂ + u₂` at the root, the constants `c_θ, c` remain free, and
`t₂(a), a₂₂, s₂₂, q₁(a), q₀(a), j, p₀'(a), q₀'(a)` remain free or
tied-not-determined.  The ground constants `α, β, γ, δ` are not
touched, no total-degree or twice-prime theorem is used, and the
nonzero-face Jacobian coefficient tower stays exhausted: the
degree-`0` row is the last one and it is consumed here.  The aligned
face `N = 0` is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Scalar combination lemmas -/

section ThetaZeroBranchClosureScalars410

variable {F : Type*} [Field F] [CharZero F]

/-- Eliminating `q₁` between the theta tie
`ν₂(a) + μ₂(a) + 16777216 q₁(a) = 0` and the iota tie
`w₂(a) + u₂(a) = 2 q₁(a) t₂(a)` leaves a `q₁`-free linear relation
between the two tower sums. -/
theorem thetaZeroBranch_crossTowerTie410 (nm wu q1 t2v : F)
    (htheta : nm + 16777216 * q1 = 0)
    (hiota : wu = 2 * q1 * t2v) :
    8388608 * wu + t2v * nm = 0 := by
  linear_combination (8388608 : F) * hiota + t2v * htheta

/-- For a nonzero Keller constant the evaluated closure system consists
of units: `p₀'(a)`, `q₁(a)`, and the theta sum `ν₂(a) + μ₂(a)` are all
nonzero, and the iota sum `w₂(a) + u₂(a)` is nonzero whenever
`t₂(a)` is. -/
theorem thetaZeroBranch_unitClosure410 (pd q1 nm wu t2v j : F)
    (hj : j ≠ 0) (hrow : pd * q1 = j)
    (htheta : nm + 16777216 * q1 = 0)
    (hiota : wu = 2 * q1 * t2v) :
    pd ≠ 0 ∧ q1 ≠ 0 ∧ nm ≠ 0 ∧ (t2v ≠ 0 → wu ≠ 0) := by
  obtain ⟨hpd, hq1⟩ := iotaZeroBranch_kellerUnits410 pd q1 j hj hrow
  refine ⟨hpd, hq1, ?_, ?_⟩
  · intro hnm
    rw [hnm, zero_add] at htheta
    have h16 : (16777216 : F) ≠ 0 := by norm_num
    exact hq1 ((mul_eq_zero.mp htheta).resolve_left h16)
  · intro ht2 hwu
    rw [hwu] at hiota
    exact mul_ne_zero
      (mul_ne_zero (by norm_num : (2 : F) ≠ 0) hq1) ht2 hiota.symm

end ThetaZeroBranchClosureScalars410

/-! ## Source-facing closure packet -/

section ThetaZeroBranchClosure410

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

set_option maxHeartbeats 1600000 in
/-- Sharpest exact residual on the theta-forced zero-`p₁` branch of the
nonzero `(4,10)` face, with the branch hypothesis discharged: `θ`
forces `p₁(a) = 0`, both towers carry their second `h`-factor
(`Θ₃ = h₀² ν₂`, `Θ₂ = h₀ μ₂`, `ι₃ = h₀² w₂`, `ι₂ = h₀ u₂`) with exact
peeled identities, the root ties pin `q₁(a)` twice
(`ν₂(a) + μ₂(a) + 16777216 q₁(a) = 0` and
`w₂(a) + u₂(a) = 2 q₁(a) t₂(a)`), the degree-`0` Keller row gives
`p₀'(a) q₁(a) = j`, and eliminating `q₁(a)` yields the `q₁`-free
cross-tower tie `8388608 (w₂(a) + u₂(a)) + t₂(a) (ν₂(a) + μ₂(a)) = 0`
together with the Keller-linked pair
`p₀'(a) (ν₂(a) + μ₂(a)) + 16777216 j = 0` and
`p₀'(a) (w₂(a) + u₂(a)) = 2 j t₂(a)`; for `j ≠ 0` all root sums are
units (the iota sum whenever `t₂(a) ≠ 0`).  The hypothesis
`λ + 4 t₂(a) = 0` is not assumed.  The cofactors are pinned only in
sums, `c_θ, c` remain free, and the branch is not closed. -/
theorem nonzeroFace410_thetaZeroBranchClosurePacket
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (t2 a22 s22 vis w73 q54 b42 b31 : k[X]) (a : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hp3 : p.coeff 3 = h0 ^ 3 * t2) (hp2 : p.coeff 2 = h0 ^ 2 * a22)
    (hq8 : q.coeff 8 = h0 ^ 8 * s22) (hq7 : q.coeff 7 = h0 ^ 6 * vis)
    (hq6 : q.coeff 6 = h0 ^ 5 * w73) (hq5 : q.coeff 5 = h0 ^ 4 * q54)
    (hq4 : q.coeff 4 = h0 ^ 2 * b42) (hq3 : q.coeff 3 = h0 * b31)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hT : (64 : k) * vis.eval a - (160 : k) * (p.coeff 1).eval a = 0)
    (hU : (8 : k) * w73.eval a =
      (p.coeff 1).eval a * ((30 : k) * t2.eval a - (9 : k) * lambda))
    (hW : (8 : k) * b42.eval a = (15 : k) * ((p.coeff 1).eval a) ^ 2)
    (hV : (32 : k) * q54.eval a +
        (40 : k) * (p.coeff 1).eval a * a22.eval a -
        (64 : k) * (p.coeff 1).eval a * s22.eval a -
        (27 : k) * (p.coeff 1).eval a * lambda * t2.eval a +
        (90 : k) * (p.coeff 1).eval a * (t2.eval a) ^ 2 =
      0)
    (hX : (64 : k) * b31.eval a =
      (15 : k) * ((p.coeff 1).eval a) ^ 2 *
        ((4 : k) * t2.eval a - (3 : k) * lambda))
    (hY : (256 : k) * (q.coeff 2).eval a =
      ((p.coeff 1).eval a) ^ 2 *
        ((256 : k) * s22.eval a - (400 : k) * a22.eval a +
          (243 : k) * lambda * t2.eval a -
          (540 : k) * (t2.eval a) ^ 2)) :
    ∃ (ctheta c : k) (nu2 mu2 w2 u2 : k[X]),
      (p.coeff 1).eval a = 0 ∧
      localClearedThetaResidual410 h0 t2 a22 s22 vis w73 q54
          (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1)
          lambda =
        Polynomial.C ctheta * h0 ^ 3 ∧
      thetaPolarThreeNumerator410 vis (p.coeff 1) b42 =
        h0 ^ 2 * nu2 ∧
      thetaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 (p.coeff 1)
          b42 b31 (q.coeff 2) lambda =
        h0 * mu2 ∧
      nu2 + mu2 +
          thetaPolarOneNumerator410 t2 a22 s22 vis w73 q54 (p.coeff 1)
            (p.coeff 0) (q.coeff 1) lambda +
          h0 * thetaRegularNumerator410 t2 a22 s22 (p.coeff 0)
            lambda =
        Polynomial.C ctheta * h0 ∧
      localClearedIotaResidual410 h0 t2 a22 s22 vis w73 q54
          (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1)
          (q.coeff 0) lambda =
        Polynomial.C c * h0 ^ 3 ∧
      iotaPolarThreeNumerator410 t2 vis w73 (p.coeff 1) b42 b31
          lambda =
        h0 ^ 2 * w2 ∧
      iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 (p.coeff 1)
          (p.coeff 0) b42 b31 (q.coeff 2) lambda =
        h0 * u2 ∧
      w2 + u2 +
          iotaPolarOneNumerator410 t2 a22 s22 vis w73 q54 (p.coeff 1)
            (p.coeff 0) (q.coeff 1) lambda +
          h0 * iotaRegularNumerator410 t2 a22 s22 (p.coeff 0)
            (q.coeff 0) lambda =
        Polynomial.C c * h0 ∧
      nu2.eval a + mu2.eval a +
          (16777216 : k) * (q.coeff 1).eval a =
        0 ∧
      w2.eval a + u2.eval a =
        (2 : k) * (q.coeff 1).eval a * t2.eval a ∧
      ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a = j ∧
      (8388608 : k) * (w2.eval a + u2.eval a) +
          t2.eval a * (nu2.eval a + mu2.eval a) =
        0 ∧
      ((p.coeff 0).derivative).eval a *
            (nu2.eval a + mu2.eval a) +
          (16777216 : k) * j =
        0 ∧
      ((p.coeff 0).derivative).eval a * (w2.eval a + u2.eval a) =
        (2 : k) * j * t2.eval a ∧
      (j ≠ 0 →
        ((p.coeff 0).derivative).eval a ≠ 0 ∧
          (q.coeff 1).eval a ≠ 0 ∧
          nu2.eval a + mu2.eval a ≠ 0 ∧
          (t2.eval a ≠ 0 → w2.eval a + u2.eval a ≠ 0)) := by
  have hh0 : h0 ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hdegree
    exact zero_ne_one hdegree
  obtain ⟨ctheta, _, v1, v2, v3, _, _, _, hpowT, htw1, htw2, htw3,
      htwc, _, _, _, _, _, ha1, _, _, _, _, _, _, hv10, _, hv2tie, _,
      _, _, _, hcombo, _⟩ :=
    nonzeroFace410_thetaSourceBridgePacket p q H h0 j lambda t2 a22
      s22 vis w73 q54 b42 b31 a hp hq hh0 hH hp4 hq10 hN hD hp3 hp2
      hq8 hq7 hq6 hq5 hq4 hq3 hroot hT hU hW hV hX hY
  obtain ⟨c, w2, u2, hzw2, hzu2, hzexact, hzsum, hzrow, hzfinal⟩ :=
    nonzeroFace410_iotaZeroPolarBranchPacket p q H h0 j lambda t2 a22
      s22 vis w73 q54 b42 b31 a hp hq hH hp4 hq10 hN hD hp3 hp2 hq8
      hq7 hq6 hq5 hq4 hq3 hdegree hroot ha1 hT hU hW hV hX hY
  have hTh2a :
      (thetaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 (p.coeff 1)
          b42 b31 (q.coeff 2) lambda).eval a = 0 := by
    have he := congrArg (fun r : k[X] => r.eval a) htw2
    simp only [eval_add, eval_mul, hroot, zero_mul] at he
    linear_combination he - hv10
  obtain ⟨nu2, hnu⟩ := linearPolynomial_dvd_of_eval_eq_zero_410 h0 v1
    a hdegree hroot hv10
  obtain ⟨mu2, hmu⟩ := linearPolynomial_dvd_of_eval_eq_zero_410 h0
    (thetaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 (p.coeff 1) b42
      b31 (q.coeff 2) lambda) a hdegree hroot hTh2a
  have hTheta3 :
      thetaPolarThreeNumerator410 vis (p.coeff 1) b42 =
        h0 ^ 2 * nu2 := by
    rw [htw1, hnu]
    ring
  have hv2eq : nu2 + mu2 = v2 := by
    have hcancel : h0 * (nu2 + mu2) = h0 * v2 := by
      linear_combination htw2 - hnu - hmu
    exact mul_left_cancel₀ hh0 hcancel
  have hv2eval : nu2.eval a + mu2.eval a = v2.eval a := by
    have he := congrArg (fun r : k[X] => r.eval a) hv2eq
    simpa only [eval_add] using he
  have hpeelT :
      nu2 + mu2 +
          thetaPolarOneNumerator410 t2 a22 s22 vis w73 q54 (p.coeff 1)
            (p.coeff 0) (q.coeff 1) lambda +
          h0 * thetaRegularNumerator410 t2 a22 s22 (p.coeff 0)
            lambda =
        Polynomial.C ctheta * h0 := by
    linear_combination hv2eq + htw3 + h0 * htwc
  have hnmtie :
      nu2.eval a + mu2.eval a +
          (16777216 : k) * (q.coeff 1).eval a =
        0 := by
    linear_combination hv2eval + hv2tie
  have hpowIz :
      localClearedIotaResidual410 h0 t2 a22 s22 vis w73 q54
          (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1)
          (q.coeff 0) lambda =
        Polynomial.C c * h0 ^ 3 := by
    simp only [localClearedIotaResidual410]
    linear_combination hzw2 + h0 * hzu2 + h0 ^ 2 * hzexact
  have hcross := thetaZeroBranch_crossTowerTie410
    (nu2.eval a + mu2.eval a) (w2.eval a + u2.eval a)
    ((q.coeff 1).eval a) (t2.eval a) hnmtie hzsum
  have hkellerTheta :
      ((p.coeff 0).derivative).eval a *
            (nu2.eval a + mu2.eval a) +
          (16777216 : k) * j =
        0 := by
    linear_combination hcombo +
      ((p.coeff 0).derivative).eval a * hv2eval
  have hunits : j ≠ 0 →
      ((p.coeff 0).derivative).eval a ≠ 0 ∧
        (q.coeff 1).eval a ≠ 0 ∧
        nu2.eval a + mu2.eval a ≠ 0 ∧
        (t2.eval a ≠ 0 → w2.eval a + u2.eval a ≠ 0) := fun hj =>
    thetaZeroBranch_unitClosure410 (((p.coeff 0).derivative).eval a)
      ((q.coeff 1).eval a) (nu2.eval a + mu2.eval a)
      (w2.eval a + u2.eval a) (t2.eval a) j hj hzrow hnmtie hzsum
  exact ⟨ctheta, c, nu2, mu2, w2, u2, ha1, hpowT, hTheta3, hmu,
    hpeelT, hpowIz, hzw2, hzu2, hzexact, hnmtie, hzsum, hzrow, hcross,
    hkellerTheta, hzfinal, hunits⟩

end ThetaZeroBranchClosure410

#print axioms thetaZeroBranch_crossTowerTie410
#print axioms thetaZeroBranch_unitClosure410
#print axioms nonzeroFace410_thetaZeroBranchClosurePacket

end Max11DegreeRoutes
