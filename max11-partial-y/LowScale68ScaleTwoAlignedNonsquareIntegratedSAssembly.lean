import LowScale68ScaleTwoAlignedNonsquareIntegratedSNext

/-! # Source assembly for the integrated-R cubic-core packet -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

section IntegratedRSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

local notation "F68" => AdjoinRoot (alignedQuadraticPolynomial46 H)

local instance integratedRSourceCharZero68 : CharZero F68 :=
  charZero_of_injective_ringHom (algebraMap (RatFunc k) F68).injective

/-- Exact base-polynomial clearing of integrated `R`, mechanically extracted
from the source depression identity. -/
theorem NonsquareAlignedSourceCurveData68.integratedR_degreeEight_q4_shape
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    {g r t s u : k[X]}
    (hg : p.coeff 5 = H * g) (hr : g = H * r)
    (ht : p.coeff 4 = H * t)
    (hq7 : q.coeff 7 = C (4 / 3 : k) * g * H ^ 2)
    (hq6 : q.coeff 6 = H ^ 2 * s) (hq5 : q.coeff 5 = H * u) :
    q.coeff 4 + C (5 / 12 : k) * s * r ^ 2 -
        C (5 / 6 : k) * u * r - C (35 / 216 : k) * r ^ 4 =
      C (4 / 3 : k) *
          (H * p.coeff 2 - C (1 / 2 : k) * p.coeff 3 * r +
            C (1 / 6 : k) * t * r ^ 2 - C (5 / 144 : k) * r ^ 4) +
        C (2 / 9 : k) * (t - C (5 / 12 : k) * r ^ 2) ^ 2 +
        C S.alpha * H * (t - C (5 / 12 : k) * r ^ 2) +
        C S.gamma * H ^ 2 := by
  let h : F68 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  let a5 : F68 := quadraticCoefficientMap46 H (p.coeff 5)
  let a4 : F68 := quadraticCoefficientMap46 H (p.coeff 4)
  let a3 : F68 := quadraticCoefficientMap46 H (p.coeff 3)
  let a2 : F68 := quadraticCoefficientMap46 H (p.coeff 2)
  let b7 : F68 := quadraticCoefficientMap46 H (q.coeff 7)
  let b6 : F68 := quadraticCoefficientMap46 H (q.coeff 6)
  let b5 : F68 := quadraticCoefficientMap46 H (q.coeff 5)
  let b4 : F68 := quadraticCoefficientMap46 H (q.coeff 4)
  let rF : F68 := quadraticCoefficientMap46 H r
  let tF : F68 := quadraticCoefficientMap46 H t
  let sF : F68 := quadraticCoefficientMap46 H s
  let uF : F68 := quadraticCoefficientMap46 H u
  have hroot : h ^ 2 = quadraticCoefficientMap46 H H :=
    alignedQuadraticRoot_sq46 H
  have hh : h ≠ 0 := S.scale_ne_zero
  have hphi : Function.Injective (quadraticCoefficientMap46 H) :=
    (algebraMap (RatFunc k) F68).injective.comp
      (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  have hcoeffC (c : k) : quadraticCoefficientMap46 H (C c) =
      algebraMap k F68 c := by
    rw [quadraticCoefficientMap46_eq_algebraMap]
    simpa using (IsScalarTower.algebraMap_apply k k[X] F68 c).symm
  have h43 : algebraMap k F68 (4 / 3 : k) = (4 / 3 : F68) := by
    rw [map_div₀, map_ofNat, map_ofNat]
  have h512 : algebraMap k F68 (5 / 12 : k) = (5 / 12 : F68) := by
    rw [map_div₀, map_ofNat, map_ofNat]
  have h56 : algebraMap k F68 (5 / 6 : k) = (5 / 6 : F68) := by
    rw [map_div₀, map_ofNat, map_ofNat]
  have h35216 : algebraMap k F68 (35 / 216 : k) = (35 / 216 : F68) := by
    rw [map_div₀, map_ofNat, map_ofNat]
  have h12 : algebraMap k F68 (1 / 2 : k) = (1 / 2 : F68) := by
    rw [map_div₀, map_one, map_ofNat]
  have h16 : algebraMap k F68 (1 / 6 : k) = (1 / 6 : F68) := by
    rw [map_div₀, map_one, map_ofNat]
  have h5144 : algebraMap k F68 (5 / 144 : k) = (5 / 144 : F68) := by
    rw [map_div₀, map_ofNat, map_ofNat]
  have h29 : algebraMap k F68 (2 / 9 : k) = (2 / 9 : F68) := by
    rw [map_div₀, map_ofNat, map_ofNat]
  have hpTop : quadraticCoefficientMap46 H (p.coeff 6) = h ^ 6 := by
    rw [hp6, map_pow, ← hroot]
    ring
  have hqTop : quadraticCoefficientMap46 H (q.coeff 8) = h ^ 8 := by
    rw [hq8, map_pow, ← hroot]
    ring
  have hpRaw := sourceToQuadratic68_eq_rawSextic H p h hp hpTop
  have hsextic := S.sextic_eq
  rw [hpRaw] at hsextic
  have hcoeff5 := congrArg (fun f : F68[X] => f.coeff 5) hsextic
  have hcenter : S.r = sexticDepressionR68 h a5 := by
    apply r_eq_sexticDepression_of_coeff_five h S.r a5 a4 a3 a2
      (quadraticCoefficientMap46 H (p.coeff 1))
      (quadraticCoefficientMap46 H (p.coeff 0)) hh
    simpa only [depressedSextic68_coeff_five] using hcoeff5
  have hpDep := affineDepress_rawSextic68 h S.r a5 a4 a3 a2
    (quadraticCoefficientMap46 H (p.coeff 1))
    (quadraticCoefficientMap46 H (p.coeff 0)) hh hcenter
  have hA : depressedA68 h S.r a5 a4 = S.A := by
    have hc := congrArg (fun f : F68[X] => f.coeff 4)
      (hpDep.symm.trans hsextic)
    simpa [depressedSextic68] using hc
  have hC : depressedC68 h S.r a5 a4 a3 a2 = S.C0 := by
    have hc := congrArg (fun f : F68[X] => f.coeff 2)
      (hpDep.symm.trans hsextic)
    simpa [depressedSextic68] using hc
  have hqRaw := sourceToQuadratic68_eq_rawOctic H q h hq hqTop
  have hoctic := S.octic_eq
  rw [hqRaw] at hoctic
  have hqDep := affineDepress_rawOctic68 h S.r b7 b6 b5 b4
    (quadraticCoefficientMap46 H (q.coeff 3))
    (quadraticCoefficientMap46 H (q.coeff 2))
    (quadraticCoefficientMap46 H (q.coeff 1))
    (quadraticCoefficientMap46 H (q.coeff 0)) hh
  have hR : depressedR68 h S.r b7 b6 b5 b4 =
      integratedR68 0 S.A S.B S.C0 (algebraMap k F68 S.alpha)
        (algebraMap k F68 S.gamma) := by
    have hc := congrArg (fun f : F68[X] => f.coeff 4)
      (hqDep.symm.trans hoctic)
    simpa [depressedOctic68] using hc
  have ha5 : a5 = h ^ 4 * rF := by
    dsimp only [a5, rF]
    rw [hg, hr, map_mul, map_mul, ← hroot]
    ring
  have ha4 : a4 = h ^ 2 * tF := by
    dsimp only [a4, tF]
    rw [ht, map_mul, ← hroot]
  have hb7 : b7 = (4 / 3 : F68) * h ^ 6 * rF := by
    dsimp only [b7, rF]
    rw [hq7, hr]
    simp only [map_mul, map_pow, hcoeffC, h43]
    rw [← hroot]
    ring
  have hb6 : b6 = h ^ 4 * sF := by
    dsimp only [b6, sF]
    rw [hq6, map_mul, map_pow, ← hroot]
    ring
  have hb5 : b5 = h ^ 2 * uF := by
    dsimp only [b5, uF]
    rw [hq5, map_mul, ← hroot]
  have hcenter' : S.r = rF / (6 * h) := by
    rw [hcenter, sexticDepressionR68, ha5]
    field_simp [hh]
  have hR' : depressedR68 h S.r b7 b6 b5 b4 =
      integratedR68 0 (depressedA68 h S.r a5 a4)
        (depressedB68 h S.r a5 a4 a3)
        (depressedC68 h S.r a5 a4 a3 a2)
        (algebraMap k F68 S.alpha) (algebraMap k F68 S.gamma) := by
    rw [hA, hC]
    simpa only [integratedR68, zero_mul, mul_zero, add_zero] using hR
  rw [ha5, ha4, hb7, hb6, hb5] at hR'
  have hshape := integratedR_degreeEight_b4_shape_68 h S.r rF tF a3 a2
    sF uF b4 (algebraMap k F68 S.alpha) (algebraMap k F68 S.gamma)
    hh hcenter' hR'
  apply hphi
  dsimp only [a2, a3, b4, rF, tF, sF, uF] at hshape ⊢
  simp only [map_add, map_sub, map_mul, map_pow, hcoeffC, h43, h512, h56,
    h35216, h12, h16, h5144, h29]
  rw [← hroot]
  convert hshape using 1 <;> ring

end IntegratedRSource68

section CubicCoreSourcePacket68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- The integrated-Q/R identities and the next two literal Keller rows,
assembled over the original source, force the cubic core at every root of
the nonsquare quadratic. -/
theorem NonsquareAlignedSourceCurveData68.integratedRSNext_cubicCorePacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) :
    ∃ (kappa : k) (g r t s u : k[X]),
      p.coeff 5 = H * g ∧ g = H * r ∧ p.coeff 4 = H * t ∧
      q.coeff 6 = H ^ 2 * s ∧ q.coeff 5 = H * u ∧
      u = C (4 / 3 : k) * p.coeff 3 + s * r -
        C (8 / 9 : k) * t * r - C (22 / 81 : k) * r ^ 3 ∧
      (∀ a : k, H.eval a = 0 →
        (3 : k) * t.eval a = (r.eval a) ^ 2 ∧
        (27 : k) * (p.coeff 3).eval a = (r.eval a) ^ 3) := by
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2 := NonsquarePolynomial46.not_sq
  obtain ⟨kappa, g, r, t, hg, hr, ht, hq7, hq6sq, hshape,
      _hiffsrc, _hiffA, _hroots⟩ :=
    S.degreeEightResidualPacket (H := H) hdeg hp hq hp6 hq8 haligned hjac
  obtain ⟨s, hs⟩ := hq6sq
  let u : k[X] := C (4 / 3 : k) * p.coeff 3 + s * r -
    C (8 / 9 : k) * t * r - C (22 / 81 : k) * r ^ 3
  have hq5 : q.coeff 5 = H * u := by
    dsimp only [u]
    exact S.integratedQ_degreeNine_q5_shape (H := H) hp hq hp6 hq8 hg hr
      ht hq7 hs
  have hq4shape := S.integratedR_degreeEight_q4_shape (H := H) hp hq hp6
    hq8 hg hr ht hq7 hs hq5
  have hp5shape : p.coeff 5 = H ^ 2 * r := by
    rw [hg, hr]
    ring
  have hq7shape : q.coeff 7 = C (4 / 3 : k) * H ^ 3 * r := by
    rw [hq7, hr]
    ring
  have hsecondPoly : (9 : k[X]) * s =
      (2 : k[X]) * r ^ 2 + (12 : k[X]) * t + C kappa * H := by
    have hcancel : H ^ 2 * ((9 : k[X]) * s - (7 : k[X]) * r ^ 2) =
        H ^ 2 * ((12 : k[X]) * t - (5 : k[X]) * r ^ 2 +
          C kappa * H) := by
      calc
        H ^ 2 * ((9 : k[X]) * s - (7 : k[X]) * r ^ 2) =
            (9 : k[X]) * q.coeff 6 - (7 : k[X]) * g ^ 2 := by
          rw [hs, hr]
          ring
        _ = H ^ 2 * ((12 : k[X]) * t - (5 : k[X]) * r ^ 2 +
            C kappa * H) := hshape
    have hinner := mul_left_cancel₀ (pow_ne_zero 2 hH) hcancel
    linear_combination hinner
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  refine ⟨kappa, g, r, t, s, u, hg, hr, ht, hs, hq5, rfl, ?_⟩
  intro a ha
  have hsecondRoot : (9 : k) * s.eval a =
      2 * (r.eval a) ^ 2 + 12 * t.eval a := by
    have he := congrArg (fun f : k[X] => f.eval a) hsecondPoly
    simpa [eval_add, eval_mul, eval_pow, eval_C, ha] using he
  have hQRoot : u.eval a =
      (4 / 3 : k) * (p.coeff 3).eval a + s.eval a * r.eval a -
        (8 / 9 : k) * t.eval a * r.eval a -
        (22 / 81 : k) * (r.eval a) ^ 3 := by
    dsimp only [u]
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C]
  have hRRoot : (q.coeff 4).eval a +
        (5 / 12 : k) * s.eval a * (r.eval a) ^ 2 -
        (5 / 6 : k) * u.eval a * r.eval a -
        (35 / 216 : k) * (r.eval a) ^ 4 =
      (4 / 3 : k) * (-(1 / 2 : k) * (p.coeff 3).eval a * r.eval a +
          (1 / 6 : k) * t.eval a * (r.eval a) ^ 2 -
          (5 / 144 : k) * (r.eval a) ^ 4) +
        (2 / 9 : k) *
          (t.eval a - (5 / 12 : k) * (r.eval a) ^ 2) ^ 2 := by
    have he := congrArg (fun f : k[X] => f.eval a) hq4shape
    simpa [eval_add, eval_sub, eval_mul, eval_pow, eval_C, ha] using he
  have hrow8 := fifthCoefficientJacobianRow_divided_eval_root_68 hp hq
    hjac hp6 hq8 hp5shape ht hq7shape hs hq5 rfl ha (hsimple a ha)
  have hrow7 := sixthCoefficientJacobianRow_eval_root_68 hp hq hjac hp6 hq8
    hp5shape ht hq7shape hs hq5 rfl ha (hsimple a ha)
  exact integratedR_nextRow_cubicCore_68 (r.eval a) (t.eval a)
    ((p.coeff 3).eval a) (s.eval a) (u.eval a) ((q.coeff 4).eval a)
    hsecondRoot hQRoot hRRoot hrow8 hrow7

end CubicCoreSourcePacket68

end Max11DegreeRoutes
