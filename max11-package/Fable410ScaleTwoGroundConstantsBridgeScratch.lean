import Fable410ScaleTwoThetaSourceBridgeScratch

/-! # Ground constants bridge for the normalized `(4,10)` nonzero source

The theta source bridge exhausted the Keller row tower on the nonzero
`(4,10)` face and pinned `p₁(a) = 0`, `q₁(a)` (twice), and the terminal
cofactors.  The ground first integrals `α, β, γ, δ` (rows `11`–`8`)
were still uncleared against any jet.  Among them `α = P - (5/2) A`
(row `11`, `alphaResidual410`) is the lowest and most constrained: on
the thirteenth-face jet both of its letters are `h`-free
(`A = (8 a₂₂ - 3 t₂²)/8`, `P = (18 λ t₂ + 16 s₂₂ - 45 t₂²)/16`), so its
exact literal-source clearing has weight ZERO — the unique `h`-free
ground integral, while `β, γ, δ` all carry order-`-1` letters.

First, the clearing: `8 α = 8 s₂₂ - 20 a₂₂ - 15 t₂² + 9 λ t₂` exactly
(`alphaDefect_eq_cleared410`); the `h`-adic peel is trivial because the
cleared defect already sits at order `0`.

Second, the literal-source trace: the degree-`11` Jacobian row makes
`α` a differential constant, so the cleared numerator is GLOBALLY a
scalar (`nonzeroFace410_alphaResidualPowerRelation`):
`8 s₂₂ - 20 a₂₂ - 15 t₂² + 9 λ t₂ = C c_α` as polynomials — the first
global pin of a thirteenth-face jet letter by a ground constant in this
lane.  The letter `s₂₂` is solved exactly
(`alphaGroundPin_solveSTwo410`), not merely evaluated at the root.

Third, the combination with the theta/iota/Keller packet: both regular
blocks are linear in `s₂₂`, so the pin eliminates `s₂₂` from them in
factored form (`thetaRegular_alphaEliminated410`,
`iotaRegular_alphaEliminated410` with explicit cofactors
`thetaRegularSTwoCofactor410`, `iotaRegularSTwoCofactor410`), giving
global ground-constant-loaded forms of the two terminal cofactor ties
`8 v₃ + 8 Θ₀|_{s₂₂=0} + (C c_α + 20 a₂₂ + 15 t₂² - 9 λ t₂) S_θ =
8 C c_θ` and its `ι` analogue, together with their root evaluations.
These are the sharpest ground-constant-loaded residuals: they link the
three constants `c_α, c_θ, c` through `t₂, a₂₂, p₀, q₀` only.

Nothing here closes the face or a branch: `c_α` is free, so the pin
eliminates no configuration; `t₂(a), a₂₂(a), q₁(a), q₀(a), c_α, c_θ,
c, j, p₀'(a), q₀'(a)` remain free or tied-not-determined; the ground
constants `β, γ, δ` stay uncleared; the raw regular ties of the theta
packet are recoverable from the ground-loaded ones and the `s₂₂` pin.
No total-degree or twice-prime theorem is used, and the aligned face
`N = 0` is not touched.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Weight-zero clearing of `α` on the thirteenth-face jet -/

section AlphaGroundClearing410

variable {F : Type*} [Field F] [CharZero F]

set_option linter.unusedSectionVars false

/-- Cleared numerator of `8 α` on the thirteenth-face jet.  It is
`h`-free: `α` is the unique ground first integral whose clearing has
weight zero. -/
def alphaGroundNumerator410 (t2 a22 s22 : F[X]) (lambda : F) : F[X] :=
  (8 : F[X]) * s22 - (20 : F[X]) * a22 - (15 : F[X]) * t2 ^ 2 +
    (9 : F[X]) * Polynomial.C lambda * t2

/-- Exact weight-zero clearing of the second-face residual `α` on the
thirteenth-face jet substitutions: no power of `h` survives. -/
theorem alphaDefect_eq_cleared410
    (h t2 a22 s22 b9 lambda : F) (hh : h ≠ 0)
    (hN : 5 * (h ^ 3 * t2) * h ^ 6 - 2 * b9 = lambda * h ^ 9) :
    (8 : F) *
        alphaResidual410
          (depressedA410 h (quarticDepressionR410 h (h ^ 3 * t2))
            (h ^ 3 * t2) (h ^ 2 * a22))
          (depressedP410 h (quarticDepressionR410 h (h ^ 3 * t2)) b9
            (h ^ 8 * s22)) =
      8 * s22 - 20 * a22 - 15 * t2 ^ 2 + 9 * lambda * t2 := by
  simp only [alphaResidual410]
  rw [depressedA410_eq_cleared h (h ^ 3 * t2) (h ^ 2 * a22) hh,
    depressedP410_eq_cleared_ninthPower h (h ^ 3 * t2) b9 (h ^ 8 * s22)
      lambda hh hN]
  field_simp
  ring

/-- The ground pin solves the jet letter `s₂₂` globally, as a
polynomial identity, up to the ground constant `c_α`. -/
theorem alphaGroundPin_solveSTwo410 (t2 a22 s22 : F[X])
    (lambda calpha : F)
    (hpin : alphaGroundNumerator410 t2 a22 s22 lambda =
      Polynomial.C calpha) :
    (8 : F[X]) * s22 =
      Polynomial.C calpha + (20 : F[X]) * a22 + (15 : F[X]) * t2 ^ 2 -
        (9 : F[X]) * Polynomial.C lambda * t2 := by
  have h := hpin
  simp only [alphaGroundNumerator410] at h
  linear_combination h

/-- Root evaluation of the ground pin. -/
theorem alphaGroundPin_rootEval410 (t2 a22 s22 : F[X])
    (lambda calpha a : F)
    (hpin : alphaGroundNumerator410 t2 a22 s22 lambda =
      Polynomial.C calpha) :
    (8 : F) * s22.eval a =
      calpha + (20 : F) * a22.eval a + (15 : F) * (t2.eval a) ^ 2 -
        (9 : F) * lambda * t2.eval a := by
  have h := congrArg (fun r : F[X] => r.eval a) hpin
  simp only [alphaGroundNumerator410, eval_add, eval_sub, eval_mul,
    eval_pow, eval_ofNat, eval_C] at h
  linear_combination h

/-- `s₂₂`-cofactor of the theta regular block: the theta regular
numerator is linear in `s₂₂` with this coefficient. -/
def thetaRegularSTwoCofactor410 (t2 a22 a0 : F[X]) : F[X] :=
  -(94371840 : F[X]) * a0 * a22 * t2 +
    (51118080 : F[X]) * a0 * t2 ^ 3 +
    (51118080 : F[X]) * a22 ^ 3 * t2 -
    (108625920 : F[X]) * a22 ^ 2 * t2 ^ 3 +
    (57028608 : F[X]) * a22 * t2 ^ 5 -
    (8486400 : F[X]) * t2 ^ 7

/-- `s₂₂`-cofactor of the iota regular block: the iota regular
numerator is linear in `s₂₂` with this coefficient. -/
def iotaRegularSTwoCofactor410 (t2 a22 a0 : F[X]) : F[X] :=
  (8 : F[X]) * a0 ^ 2 - (16 : F[X]) * a0 * a22 ^ 2 +
    (48 : F[X]) * a0 * a22 * t2 ^ 2 - (16 : F[X]) * a0 * t2 ^ 4 +
    (4 : F[X]) * a22 ^ 4 - (32 : F[X]) * a22 ^ 3 * t2 ^ 2 +
    (40 : F[X]) * a22 ^ 2 * t2 ^ 4 - (16 : F[X]) * a22 * t2 ^ 6 +
    (2 : F[X]) * t2 ^ 8

set_option maxHeartbeats 1600000 in
/-- Factored elimination of `s₂₂` from the theta regular block by the
ground pin: the block is linear in `s₂₂`, so the pinned solved form
enters exactly once, multiplied by the explicit cofactor. -/
theorem thetaRegular_alphaEliminated410 (t2 a22 s22 a0 : F[X])
    (lambda calpha : F)
    (hpin : alphaGroundNumerator410 t2 a22 s22 lambda =
      Polynomial.C calpha) :
    (8 : F[X]) * thetaRegularNumerator410 t2 a22 s22 a0 lambda =
      (8 : F[X]) * thetaRegularNumerator410 t2 a22 0 a0 lambda +
        (Polynomial.C calpha + (20 : F[X]) * a22 +
            (15 : F[X]) * t2 ^ 2 -
            (9 : F[X]) * Polynomial.C lambda * t2) *
          thetaRegularSTwoCofactor410 t2 a22 a0 := by
  have h := hpin
  simp only [alphaGroundNumerator410] at h
  simp only [thetaRegularNumerator410, thetaRegularSTwoCofactor410]
  linear_combination
    (-(94371840 : F[X]) * a0 * a22 * t2 +
      (51118080 : F[X]) * a0 * t2 ^ 3 +
      (51118080 : F[X]) * a22 ^ 3 * t2 -
      (108625920 : F[X]) * a22 ^ 2 * t2 ^ 3 +
      (57028608 : F[X]) * a22 * t2 ^ 5 -
      (8486400 : F[X]) * t2 ^ 7) * h

set_option maxHeartbeats 1600000 in
/-- Factored elimination of `s₂₂` from the iota regular block by the
ground pin. -/
theorem iotaRegular_alphaEliminated410 (t2 a22 s22 a0 b0 : F[X])
    (lambda calpha : F)
    (hpin : alphaGroundNumerator410 t2 a22 s22 lambda =
      Polynomial.C calpha) :
    (8 : F[X]) * iotaRegularNumerator410 t2 a22 s22 a0 b0 lambda =
      (8 : F[X]) * iotaRegularNumerator410 t2 a22 0 a0 b0 lambda +
        (Polynomial.C calpha + (20 : F[X]) * a22 +
            (15 : F[X]) * t2 ^ 2 -
            (9 : F[X]) * Polynomial.C lambda * t2) *
          iotaRegularSTwoCofactor410 t2 a22 a0 := by
  have h := hpin
  simp only [alphaGroundNumerator410] at h
  simp only [iotaRegularNumerator410, iotaRegularSTwoCofactor410]
  linear_combination
    ((8 : F[X]) * a0 ^ 2 - (16 : F[X]) * a0 * a22 ^ 2 +
      (48 : F[X]) * a0 * a22 * t2 ^ 2 - (16 : F[X]) * a0 * t2 ^ 4 +
      (4 : F[X]) * a22 ^ 4 - (32 : F[X]) * a22 ^ 3 * t2 ^ 2 +
      (40 : F[X]) * a22 ^ 2 * t2 ^ 4 - (16 : F[X]) * a22 * t2 ^ 6 +
      (2 : F[X]) * t2 ^ 8) * h

end AlphaGroundClearing410

/-! ## Source-facing ground power relation -/

section NonzeroGroundConstantsBridge410

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

set_option maxHeartbeats 80000000 in
/-- The second-face residual `α` on a square-core ninth-power source is
a differential constant of the degree-`11` Jacobian row, and on the
thirteenth-face jet its weight-zero cleared defect is GLOBALLY a
scalar: `8 s₂₂ - 20 a₂₂ - 15 t₂² + 9 λ t₂ = C c_α` as polynomials. -/
theorem nonzeroFace410_alphaResidualPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (t2 a22 s22 : k[X])
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp4 : p.coeff 4 = H ^ 2) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (hp3 : p.coeff 3 = h0 ^ 3 * t2) (hp2 : p.coeff 2 = h0 ^ 2 * a22)
    (hq8 : q.coeff 8 = h0 ^ 8 * s22) :
    ∃ calpha : k,
      alphaGroundNumerator410 t2 a22 s22 lambda =
        Polynomial.C calpha := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let a1 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 1)
  let a0 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 0)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
  let t2R : RatFunc k := algebraMap k[X] (RatFunc k) t2
  let a22R : RatFunc k := algebraMap k[X] (RatFunc k) a22
  let s22R : RatFunc k := algebraMap k[X] (RatFunc k) s22
  have hh : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 4) = hRF ^ 4 := by
    simp only [hp4, hH, hRF, map_pow]
    ring
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = hRF ^ 10 := by
    simp only [hq10, hH, hRF, map_pow]
    ring
  have hpDep :
      affineDepress68 hRF (quarticDepressionR410 hRF a3)
          (sourceToRatFunc68 p) =
        depressedQuartic46
          (depressedA46 hRF (quarticDepressionR410 hRF a3) a3 a2)
          (depressedB46 hRF (quarticDepressionR410 hRF a3) a3 a2 a1)
          (depressedC46 hRF (quarticDepressionR410 hRF a3) a3 a2 a1
            a0) := by
    change affineDepress46 hRF (quarticDepressionR410 hRF a3)
        (sourceToRatFunc46 p) = _
    exact affineDepress_sourceQuartic46 p hRF
      (quarticDepressionR410 hRF a3) hp hh hpTop
      (by simp [a3, quarticDepressionR410])
  have hNrat : 5 * a3 * hRF ^ 6 - 2 * b9 = RatFunc.C lambda * hRF ^ 9 := by
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hN
    have hH3 : algebraMap k[X] (RatFunc k) (H ^ 3) = hRF ^ 6 := by
      simp only [hH, hRF, map_pow]
      ring
    have hh9 : algebraMap k[X] (RatFunc k) (h0 ^ 9) = hRF ^ 9 := by
      simp only [hRF, map_pow]
    have hleft : algebraMap k[X] (RatFunc k)
        ((5 : k[X]) * p.coeff 3 * H ^ 3 - (2 : k[X]) * q.coeff 9) =
        5 * a3 * hRF ^ 6 - 2 * b9 := by
      simp only [map_sub, map_mul, map_ofNat, a3, b9, hH3]
    have hright : algebraMap k[X] (RatFunc k)
        (Polynomial.C lambda * h0 ^ 9) =
        RatFunc.C lambda * hRF ^ 9 := by
      simp only [map_mul, RatFunc.algebraMap_C, hh9]
    exact hleft.symm.trans (hmapped.trans hright)
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j hRF (quarticDepressionR410 hRF a3) hh hD
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (quarticDepressionR410 hRF a3)
      (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (quarticDepressionR410 hRF a3)
      (sourceToRatFunc68 q)
  have hf3 : f.coeff 3 = 0 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedQuartic46_three]
  have hf4 : f.coeff 4 = 1 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedQuartic46_four]
  have hf_high : ∀ n, 4 < n → f.coeff n = 0 := by
    intro n hn
    dsimp only [f]
    rw [hpDep, coeff_depressedQuartic46_of_gt_four _ _ _ hn]
  have hg_high_src : ∀ n, 10 < n → (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = hRF ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) hRF
      (quarticDepressionR410 hRF a3) hh hgTop hg_high_src
  have hg8' :
      g.coeff 8 =
        depressedP410 hRF (quarticDepressionR410 hRF a3) b9 b8 := by
    dsimp only [g]
    rw [hg8]
    simp [depressedP410, depressedP810, quarticDepressionR410,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8]
  have hg9L :
      g.coeff 9 =
        depressedL410 hRF (quarticDepressionR410 hRF a3) b9 := by
    dsimp only [g]
    rw [hg9]
    simp [depressedL410, depressedL810, quarticDepressionR410,
      sourceToRatFunc68, sourceToRatFunc46, b9]
  have hLval :
      depressedL410 hRF (quarticDepressionR410 hRF a3) b9 =
        RatFunc.C (-lambda / 2) := by
    have hL := depressedL410_eq_of_ninthPower hRF a3 b9
      (RatFunc.C lambda) hh (by simpa using hNrat)
    simpa [map_neg, map_div₀, map_ofNat] using hL
  have hg9' : g.coeff 9 = RatFunc.C (-lambda / 2) := by
    rw [hg9L, hLval]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hg9']
    have hx := ratFuncDerivation46_polynomial (C (-lambda / 2) : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hrow11 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 2) -
        (4 : RatFunc k) * ratFuncDerivation68 (g.coeff 8) = 0 := by
    have hrow :=
      differentialJacobian_coeff_11_monicQuarticDecic
        ratFuncDerivation68 f g hf_high hf4 hf3 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 11) hbracket
    simpa [f, g, Polynomial.coeff_C, show (11 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hf2 : f.coeff 2 =
      depressedA410 hRF (quarticDepressionR410 hRF a3) a3 a2 := by
    dsimp only [f, depressedA410, a3, a2]
    rw [hpDep, coeff_depressedQuartic46_two]
  have halpha0 :
      ratFuncDerivation68 (alphaResidual410 (f.coeff 2) (g.coeff 8)) =
        0 :=
    alphaResidual410_deriv_zero ratFuncDerivation68 (f.coeff 2)
      (g.coeff 8) hrow11
  obtain ⟨c0, hc0⟩ :
      ∃ c0 : k,
        alphaResidual410 (f.coeff 2) (g.coeff 8) =
          algebraMap k (RatFunc k) c0 := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      halpha0
  have hp3R : a3 = hRF ^ 3 * t2R := by
    dsimp only [a3, hRF, t2R]
    rw [hp3, map_mul, map_pow]
  have hp2R : a2 = hRF ^ 2 * a22R := by
    dsimp only [a2, hRF, a22R]
    rw [hp2, map_mul, map_pow]
  have hq8R : b8 = hRF ^ 8 * s22R := by
    dsimp only [b8, hRF, s22R]
    rw [hq8, map_mul, map_pow]
  have hNratSub :
      5 * (hRF ^ 3 * t2R) * hRF ^ 6 - 2 * b9 =
        RatFunc.C lambda * hRF ^ 9 := by
    rw [← hp3R]
    exact hNrat
  have hF := alphaDefect_eq_cleared410 hRF t2R a22R s22R b9
    (RatFunc.C lambda) hh hNratSub
  have hf2' : f.coeff 2 =
      depressedA410 hRF (quarticDepressionR410 hRF (hRF ^ 3 * t2R))
        (hRF ^ 3 * t2R) (hRF ^ 2 * a22R) := by
    rw [← hp3R, ← hp2R]
    exact hf2
  have hg8'' : g.coeff 8 =
      depressedP410 hRF (quarticDepressionR410 hRF (hRF ^ 3 * t2R)) b9
        (hRF ^ 8 * s22R) := by
    rw [← hp3R, ← hq8R]
    exact hg8'
  have hclear :
      algebraMap k[X] (RatFunc k)
          (alphaGroundNumerator410 t2 a22 s22 lambda) =
        (8 : RatFunc k) *
          alphaResidual410 (f.coeff 2) (g.coeff 8) := by
    rw [hf2', hg8'', hF]
    simp only [alphaGroundNumerator410, map_add, map_sub, map_mul,
      map_pow, map_ofNat, RatFunc.algebraMap_C, t2R, a22R, s22R]
  have htarget :
      algebraMap k[X] (RatFunc k)
          (alphaGroundNumerator410 t2 a22 s22 lambda) =
        algebraMap k[X] (RatFunc k) (Polynomial.C (8 * c0)) := by
    rw [hclear, hc0]
    simp [map_mul, RatFunc.algebraMap_C, map_ofNat]
  refine ⟨8 * c0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget

/-! ## Ground-constants bridge packet -/

set_option maxHeartbeats 4000000 in
/-- Sharpest exact successor packet of the ground-constants bridge on
the nonzero `(4,10)` face: the global weight-zero pin of the row-`11`
ground constant `c_α` solving the jet letter `s₂₂` exactly, both power
relations with their full `h`-adic peels, the unconditional collapse
`p₁(a) = 0`, the vanishing of every thirteenth-face jet letter at the
root, the double pinning of `q₁`, the ground-constant-loaded forms of
the two terminal cofactor ties — globally and at the root — with `s₂₂`
eliminated through the explicit factored cofactors, the degree-`0`
Keller row, its combination with the `θ` cofactor, and the exact
combinations on the branch `λ + 4 t₂(a) = 0`.  Nothing here closes the
face or a branch: `c_α` is free, so the pin eliminates no
configuration; `t₂(a), a₂₂, q₁(a), q₀(a), c_α, c_θ, c, j, p₀'(a),
q₀'(a)` remain free or tied-not-determined, and the ground constants
`β, γ, δ` stay uncleared. -/
theorem nonzeroFace410_groundConstantsBridgePacket
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (t2 a22 s22 vis w73 q54 b42 b31 : k[X]) (a : k)
    (hp : p.natDegree = 4) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
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
    (hroot : h0.eval a = 0)
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
    ∃ (calpha ctheta c : k) (v1 v2 v3 w1 w2 w3 : k[X]),
      alphaGroundNumerator410 t2 a22 s22 lambda =
        Polynomial.C calpha ∧
      (8 : k[X]) * s22 =
        Polynomial.C calpha + (20 : k[X]) * a22 +
          (15 : k[X]) * t2 ^ 2 -
          (9 : k[X]) * Polynomial.C lambda * t2 ∧
      localClearedThetaResidual410 h0 t2 a22 s22 vis w73 q54
          (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1)
          lambda =
        Polynomial.C ctheta * h0 ^ 3 ∧
      thetaPolarThreeNumerator410 vis (p.coeff 1) b42 = h0 * v1 ∧
      v1 + thetaPolarTwoNumerator410 t2 a22 s22 vis w73 q54
          (p.coeff 1) b42 b31 (q.coeff 2) lambda =
        h0 * v2 ∧
      v2 + thetaPolarOneNumerator410 t2 a22 s22 vis w73 q54
          (p.coeff 1) (p.coeff 0) (q.coeff 1) lambda =
        h0 * v3 ∧
      v3 + thetaRegularNumerator410 t2 a22 s22 (p.coeff 0) lambda =
        Polynomial.C ctheta ∧
      localClearedIotaResidual410 h0 t2 a22 s22 vis w73 q54
          (p.coeff 1) (p.coeff 0) b42 b31 (q.coeff 2) (q.coeff 1)
          (q.coeff 0) lambda =
        Polynomial.C c * h0 ^ 3 ∧
      iotaPolarThreeNumerator410 t2 vis w73 (p.coeff 1) b42 b31
          lambda =
        h0 * w1 ∧
      w1 + iotaPolarTwoNumerator410 t2 a22 s22 vis w73 q54 (p.coeff 1)
          (p.coeff 0) b42 b31 (q.coeff 2) lambda =
        h0 * w2 ∧
      w2 + iotaPolarOneNumerator410 t2 a22 s22 vis w73 q54 (p.coeff 1)
          (p.coeff 0) (q.coeff 1) lambda =
        h0 * w3 ∧
      w3 + iotaRegularNumerator410 t2 a22 s22 (p.coeff 0) (q.coeff 0)
          lambda =
        Polynomial.C c ∧
      (8 : k[X]) * v3 +
          (8 : k[X]) *
            thetaRegularNumerator410 t2 a22 0 (p.coeff 0) lambda +
          (Polynomial.C calpha + (20 : k[X]) * a22 +
              (15 : k[X]) * t2 ^ 2 -
              (9 : k[X]) * Polynomial.C lambda * t2) *
            thetaRegularSTwoCofactor410 t2 a22 (p.coeff 0) =
        (8 : k[X]) * Polynomial.C ctheta ∧
      (8 : k[X]) * w3 +
          (8 : k[X]) *
            iotaRegularNumerator410 t2 a22 0 (p.coeff 0) (q.coeff 0)
              lambda +
          (Polynomial.C calpha + (20 : k[X]) * a22 +
              (15 : k[X]) * t2 ^ 2 -
              (9 : k[X]) * Polynomial.C lambda * t2) *
            iotaRegularSTwoCofactor410 t2 a22 (p.coeff 0) =
        (8 : k[X]) * Polynomial.C c ∧
      (p.coeff 1).eval a = 0 ∧
      vis.eval a = 0 ∧
      w73.eval a = 0 ∧
      q54.eval a = 0 ∧
      b42.eval a = 0 ∧
      b31.eval a = 0 ∧
      (q.coeff 2).eval a = 0 ∧
      v1.eval a = 0 ∧
      w1.eval a = 0 ∧
      v2.eval a + (16777216 : k) * (q.coeff 1).eval a = 0 ∧
      w2.eval a = (2 : k) * (q.coeff 1).eval a * t2.eval a ∧
      (8 : k) * s22.eval a =
        calpha + (20 : k) * a22.eval a + (15 : k) * (t2.eval a) ^ 2 -
          (9 : k) * lambda * t2.eval a ∧
      (8 : k) * v3.eval a +
          (8 : k) *
            (thetaRegularNumerator410 t2 a22 0 (p.coeff 0)
                lambda).eval a +
          (calpha + (20 : k) * a22.eval a +
              (15 : k) * (t2.eval a) ^ 2 -
              (9 : k) * lambda * t2.eval a) *
            (thetaRegularSTwoCofactor410 t2 a22 (p.coeff 0)).eval a =
        (8 : k) * ctheta ∧
      (8 : k) * w3.eval a +
          (8 : k) *
            (iotaRegularNumerator410 t2 a22 0 (p.coeff 0) (q.coeff 0)
                lambda).eval a +
          (calpha + (20 : k) * a22.eval a +
              (15 : k) * (t2.eval a) ^ 2 -
              (9 : k) * lambda * t2.eval a) *
            (iotaRegularSTwoCofactor410 t2 a22 (p.coeff 0)).eval a =
        (8 : k) * c ∧
      ((p.coeff 0).derivative).eval a * (q.coeff 1).eval a = j ∧
      ((p.coeff 0).derivative).eval a * v2.eval a +
          (16777216 : k) * j =
        0 ∧
      (lambda + (4 : k) * t2.eval a = 0 →
        (2 : k) * w2.eval a + lambda * (q.coeff 1).eval a = 0 ∧
          (33554432 : k) * w2.eval a = lambda * v2.eval a ∧
          (2 : k) * ((p.coeff 0).derivative).eval a * w2.eval a +
              lambda * j =
            0) := by
  obtain ⟨ctheta, c, v1, v2, v3, w1, w2, w3, hpowT, htw1, htw2, htw3,
    htwc, hpowI, hiw1, hiw2, hiw3, hiwc, ha1, hvis0, hw730, hq540,
    hb420, hb310, hb20, hv10, hw10, hv2tie, hw2tie, _, _, hkelP,
    hcombo, hbr⟩ :=
    nonzeroFace410_thetaSourceBridgePacket p q H h0 j lambda t2 a22
      s22 vis w73 q54 b42 b31 a hp hq hh0 hH hp4 hq10 hN hD hp3 hp2
      hq8 hq7 hq6 hq5 hq4 hq3 hroot hT hU hW hV hX hY
  obtain ⟨calpha, hpin⟩ := nonzeroFace410_alphaResidualPowerRelation
    p q H h0 j lambda t2 a22 s22 hp hq hh0 hH hp4 hq10 hN hD hp3 hp2
    hq8
  have hsolve := alphaGroundPin_solveSTwo410 t2 a22 s22 lambda calpha
    hpin
  have hrootS := alphaGroundPin_rootEval410 t2 a22 s22 lambda calpha a
    hpin
  have hTelim := thetaRegular_alphaEliminated410 t2 a22 s22
    (p.coeff 0) lambda calpha hpin
  have hIelim := iotaRegular_alphaEliminated410 t2 a22 s22
    (p.coeff 0) (q.coeff 0) lambda calpha hpin
  have hTglobal :
      (8 : k[X]) * v3 +
          (8 : k[X]) *
            thetaRegularNumerator410 t2 a22 0 (p.coeff 0) lambda +
          (Polynomial.C calpha + (20 : k[X]) * a22 +
              (15 : k[X]) * t2 ^ 2 -
              (9 : k[X]) * Polynomial.C lambda * t2) *
            thetaRegularSTwoCofactor410 t2 a22 (p.coeff 0) =
        (8 : k[X]) * Polynomial.C ctheta := by
    linear_combination (8 : k[X]) * htwc - hTelim
  have hIglobal :
      (8 : k[X]) * w3 +
          (8 : k[X]) *
            iotaRegularNumerator410 t2 a22 0 (p.coeff 0) (q.coeff 0)
              lambda +
          (Polynomial.C calpha + (20 : k[X]) * a22 +
              (15 : k[X]) * t2 ^ 2 -
              (9 : k[X]) * Polynomial.C lambda * t2) *
            iotaRegularSTwoCofactor410 t2 a22 (p.coeff 0) =
        (8 : k[X]) * Polynomial.C c := by
    linear_combination (8 : k[X]) * hiwc - hIelim
  have hTroot :
      (8 : k) * v3.eval a +
          (8 : k) *
            (thetaRegularNumerator410 t2 a22 0 (p.coeff 0)
                lambda).eval a +
          (calpha + (20 : k) * a22.eval a +
              (15 : k) * (t2.eval a) ^ 2 -
              (9 : k) * lambda * t2.eval a) *
            (thetaRegularSTwoCofactor410 t2 a22 (p.coeff 0)).eval a =
        (8 : k) * ctheta := by
    have h := congrArg (fun r : k[X] => r.eval a) hTglobal
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_ofNat,
      eval_C] at h
    linear_combination h
  have hIroot :
      (8 : k) * w3.eval a +
          (8 : k) *
            (iotaRegularNumerator410 t2 a22 0 (p.coeff 0) (q.coeff 0)
                lambda).eval a +
          (calpha + (20 : k) * a22.eval a +
              (15 : k) * (t2.eval a) ^ 2 -
              (9 : k) * lambda * t2.eval a) *
            (iotaRegularSTwoCofactor410 t2 a22 (p.coeff 0)).eval a =
        (8 : k) * c := by
    have h := congrArg (fun r : k[X] => r.eval a) hIglobal
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_ofNat,
      eval_C] at h
    linear_combination h
  exact ⟨calpha, ctheta, c, v1, v2, v3, w1, w2, w3, hpin, hsolve,
    hpowT, htw1, htw2, htw3, htwc, hpowI, hiw1, hiw2, hiw3, hiwc,
    hTglobal, hIglobal, ha1, hvis0, hw730, hq540, hb420, hb310, hb20,
    hv10, hw10, hv2tie, hw2tie, hrootS, hTroot, hIroot, hkelP, hcombo,
    hbr⟩

end NonzeroGroundConstantsBridge410

#print axioms alphaDefect_eq_cleared410
#print axioms alphaGroundPin_solveSTwo410
#print axioms alphaGroundPin_rootEval410
#print axioms thetaRegular_alphaEliminated410
#print axioms iotaRegular_alphaEliminated410
#print axioms nonzeroFace410_alphaResidualPowerRelation
#print axioms nonzeroFace410_groundConstantsBridgePacket

end Max11DegreeRoutes
