import LowScale68ScaleTwoAlignedNonsquareDegreeEight

/-! # Cleared integrated-Q relation in the aligned nonsquare lane -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

section IntegratedQAlgebra68

variable {F : Type*} [Field F] [CharZero F]

/-- The field-level clearing behind the degree-nine quotient box. -/
theorem integratedQ_degreeNine_b5_shape_68
    (h center r t v s b5 : F) (hh : h ≠ 0)
    (hcenter : center = r / (6 * h))
    (hQ : depressedQ68 h center ((4 / 3 : F) * h ^ 6 * r)
        (h ^ 4 * s) b5 =
      (4 / 3 : F) *
        depressedB68 h center (h ^ 4 * r) (h ^ 2 * t) v) :
    b5 = h ^ 2 *
      ((4 / 3 : F) * v + s * r - (8 / 9 : F) * t * r -
        (22 / 81 : F) * r ^ 3) := by
  subst center
  simp only [depressedQ68, depressedB68] at hQ
  field_simp [hh] at hQ
  have hQ0 :
      (648 : F) * b5 + (176 : F) * h ^ 2 * r ^ 3 +
        (576 : F) * h ^ 2 * r * t - (648 : F) * h ^ 2 * r * s -
        (864 : F) * h ^ 2 * v = 0 := by
    calc
      (648 : F) * b5 + (176 : F) * h ^ 2 * r ^ 3 +
          (576 : F) * h ^ 2 * r * t - (648 : F) * h ^ 2 * r * s -
          (864 : F) * h ^ 2 * v =
          (r * h ^ 2 *
              (r ^ 2 * (-(56 * 3) + 6 * 21 * 4) - 6 ^ 3 * 3 * s) +
            6 ^ 3 * 3 * b5) -
            h ^ 2 * 4 *
              (r * (r ^ 2 * (-20 + 6 * 10) - 6 ^ 2 * 4 * t) +
                6 ^ 3 * v) := by ring
      _ = 0 := sub_eq_zero.mpr hQ
  linear_combination (1 / 648 : F) * hQ0

end IntegratedQAlgebra68

section IntegratedQSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

local notation "F68" => AdjoinRoot (alignedQuadraticPolynomial46 H)

local instance integratedQSourceCharZero68 : CharZero F68 :=
  charZero_of_injective_ringHom (algebraMap (RatFunc k) F68).injective

/-- The exact polynomial quotient supplied by integrated `Q=(4/3)B` after
the degree-nine divisibilities. -/
theorem NonsquareAlignedSourceCurveData68.integratedQ_degreeNine_q5_shape
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    {g r t s : k[X]}
    (hg : p.coeff 5 = H * g) (hr : g = H * r)
    (ht : p.coeff 4 = H * t)
    (hq7 : q.coeff 7 = C (4 / 3 : k) * g * H ^ 2)
    (hq6 : q.coeff 6 = H ^ 2 * s) :
    q.coeff 5 = H *
      (C (4 / 3 : k) * p.coeff 3 + s * r -
        C (8 / 9 : k) * t * r - C (22 / 81 : k) * r ^ 3) := by
  let h : F68 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  let a5 : F68 := quadraticCoefficientMap46 H (p.coeff 5)
  let a4 : F68 := quadraticCoefficientMap46 H (p.coeff 4)
  let a3 : F68 := quadraticCoefficientMap46 H (p.coeff 3)
  let b7 : F68 := quadraticCoefficientMap46 H (q.coeff 7)
  let b6 : F68 := quadraticCoefficientMap46 H (q.coeff 6)
  let b5 : F68 := quadraticCoefficientMap46 H (q.coeff 5)
  let rF : F68 := quadraticCoefficientMap46 H r
  let tF : F68 := quadraticCoefficientMap46 H t
  let sF : F68 := quadraticCoefficientMap46 H s
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
  have h89 : algebraMap k F68 (8 / 9 : k) = (8 / 9 : F68) := by
    rw [map_div₀, map_ofNat, map_ofNat]
  have h2281 : algebraMap k F68 (22 / 81 : k) = (22 / 81 : F68) := by
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
    apply r_eq_sexticDepression_of_coeff_five h S.r a5 a4 a3
      (quadraticCoefficientMap46 H (p.coeff 2))
      (quadraticCoefficientMap46 H (p.coeff 1))
      (quadraticCoefficientMap46 H (p.coeff 0)) hh
    simpa only [depressedSextic68_coeff_five] using hcoeff5
  have hpDep := affineDepress_rawSextic68 h S.r a5 a4 a3
    (quadraticCoefficientMap46 H (p.coeff 2))
    (quadraticCoefficientMap46 H (p.coeff 1))
    (quadraticCoefficientMap46 H (p.coeff 0)) hh hcenter
  have hB : depressedB68 h S.r a5 a4 a3 = S.B := by
    have hsame := hpDep.symm.trans hsextic
    have hc := congrArg (fun f : F68[X] => f.coeff 3) hsame
    simpa [depressedSextic68] using hc
  have hqRaw := sourceToQuadratic68_eq_rawOctic H q h hq hqTop
  have hoctic := S.octic_eq
  rw [hqRaw] at hoctic
  have hqDep := affineDepress_rawOctic68 h S.r b7 b6 b5
    (quadraticCoefficientMap46 H (q.coeff 4))
    (quadraticCoefficientMap46 H (q.coeff 3))
    (quadraticCoefficientMap46 H (q.coeff 2))
    (quadraticCoefficientMap46 H (q.coeff 1))
    (quadraticCoefficientMap46 H (q.coeff 0)) hh
  have hQ : depressedQ68 h S.r b7 b6 b5 =
      integratedQ68 0 S.A S.B 0 := by
    have hsame := hqDep.symm.trans hoctic
    have hc := congrArg (fun f : F68[X] => f.coeff 5) hsame
    simpa [depressedOctic68] using hc
  have hQB : depressedQ68 h S.r b7 b6 b5 =
      (4 / 3 : F68) * depressedB68 h S.r a5 a4 a3 := by
    rw [hQ, hB]
    simp only [integratedQ68, zero_mul, mul_zero, add_zero]
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
  have hcenter' : S.r = rF / (6 * h) := by
    rw [hcenter, sexticDepressionR68, ha5]
    field_simp [hh]
  rw [ha5, ha4, hb7, hb6] at hQB
  have hb5shape := integratedQ_degreeNine_b5_shape_68 h S.r rF tF a3 sF
    b5 hh hcenter' hQB
  apply hphi
  calc
    quadraticCoefficientMap46 H (q.coeff 5) = b5 := rfl
    _ = h ^ 2 *
        ((4 / 3 : F68) * a3 + sF * rF - (8 / 9 : F68) * tF * rF -
          (22 / 81 : F68) * rF ^ 3) := hb5shape
    _ = quadraticCoefficientMap46 H
        (H * (C (4 / 3 : k) * p.coeff 3 + s * r -
          C (8 / 9 : k) * t * r - C (22 / 81 : k) * r ^ 3)) := by
      dsimp only [a3, rF, tF, sF]
      simp only [map_mul, map_add, map_sub, map_pow, hcoeffC, h43, h89,
        h2281]
      rw [← hroot]

/-- Integrated `Q` therefore makes the raw degree-eight root split
automatic: `H` divides `q₅`. -/
theorem NonsquareAlignedSourceCurveData68.integratedQ_degreeNine_dvd_q5
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    {g r t s : k[X]}
    (hg : p.coeff 5 = H * g) (hr : g = H * r)
    (ht : p.coeff 4 = H * t)
    (hq7 : q.coeff 7 = C (4 / 3 : k) * g * H ^ 2)
    (hq6 : q.coeff 6 = H ^ 2 * s) :
    H ∣ q.coeff 5 := by
  refine ⟨C (4 / 3 : k) * p.coeff 3 + s * r -
    C (8 / 9 : k) * t * r - C (22 / 81 : k) * r ^ 3, ?_⟩
  exact S.integratedQ_degreeNine_q5_shape (H := H) hp hq hp6 hq8 hg hr
    ht hq7 hq6

end IntegratedQSource68

section IntegratedQPacket68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- The strongest source packet after clearing integrated `Q`.  The target
residual remains explicit rather than being asserted. -/
theorem NonsquareAlignedSourceCurveData68.degreeEightIntegratedQPacket
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
      ((9 : k[X]) * q.coeff 6 - (7 : k[X]) * g ^ 2 =
        H ^ 2 * ((12 : k[X]) * t - (5 : k[X]) * r ^ 2 + C kappa * H)) ∧
      (H ^ 5 ∣ evenClearedA68 H (p.coeff 5) (p.coeff 4) ↔
        H ∣ (12 : k[X]) * t - (5 : k[X]) * r ^ 2) := by
  obtain ⟨kappa, g, r, t, hg, hr, ht, hq7, hq6sq, hshape,
      _hiffsrc, hiffA, _hroots⟩ :=
    S.degreeEightResidualPacket (H := H) hdeg hp hq hp6 hq8 haligned hjac
  obtain ⟨s, hs⟩ := hq6sq
  let u : k[X] := C (4 / 3 : k) * p.coeff 3 + s * r -
    C (8 / 9 : k) * t * r - C (22 / 81 : k) * r ^ 3
  have hq5 : q.coeff 5 = H * u := by
    dsimp only [u]
    exact S.integratedQ_degreeNine_q5_shape (H := H) hp hq hp6 hq8 hg hr
      ht hq7 hs
  exact ⟨kappa, g, r, t, s, u, hg, hr, ht, hs, hq5, rfl, hshape, hiffA⟩

end IntegratedQPacket68

end Max11DegreeRoutes
