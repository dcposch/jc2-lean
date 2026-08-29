import LowScale68ScaleTwoAlignedNonsquareDegreeFive

/-! # Cubic-core source order and obstruction below degree five -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

section DegreeFiveSecondFreshCoordinate68

variable {k : Type*} [Field k] [CharZero k]

/-- Even after `q₂(a)` has been fixed externally, degree five can solve for
the fresh `p₁(a)` coordinate whenever `u(a) ≠ 0`.  Thus a second-order
integrated-`T` input must control the *coupled* `(q₂,p₁)` combination; a
condition on `q₂` alone is not enough to descend `r`. -/
theorem degreeFive_cubicCore_p1_solvable_68
    (d r q2 u p3 p3' q3 q3' p2 p2' w w' : k)
    (hd : d ≠ 0) (hu : u ≠ 0) :
    ∃ p1 : k,
      d * ((2 : k) * (r ^ 2 / 3) * q2 - p1 * u) +
        3 * (p3' * q3 - p3 * q3') + 4 * p2' * w - 2 * p2 * w' = 0 := by
  have hdu : d * u ≠ 0 := mul_ne_zero hd hu
  refine ⟨(d * ((2 : k) * (r ^ 2 / 3) * q2) +
      3 * (p3' * q3 - p3 * q3') + 4 * p2' * w - 2 * p2 * w') /
        (d * u), ?_⟩
  field_simp [hdu]
  ring

end DegreeFiveSecondFreshCoordinate68

section CubicCorePolynomialOrder68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- The source-facing cubic core gives the first genuinely new global order
gain below the raw lower rows: the numerator of depressed `B` acquires a
factor of `H`.  It also identifies the original target residual exactly with
the still-open descent `H ∣ r`. -/
theorem NonsquareAlignedSourceCurveData68.cubicCorePolynomialOrderPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) :
    ∃ (g r t : k[X]),
      p.coeff 5 = H * g ∧ g = H * r ∧ p.coeff 4 = H * t ∧
      H ∣ (p.coeff 3 - C (2 / 3 : k) * t * r +
        C (5 / 27 : k) * r ^ 3) ∧
      (H ∣ ((12 : k[X]) * t - (5 : k[X]) * r ^ 2) ↔ H ∣ r) := by
  obtain ⟨_kappa, g, r, t, s, u, hg, hr, ht, _hs, _hu, _hushape,
      hcore⟩ :=
    S.integratedRSNext_cubicCorePacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2 := NonsquarePolynomial46.not_sq
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hBdvd : H ∣ (p.coeff 3 - C (2 / 3 : k) * t * r +
      C (5 / 27 : k) * r ^ 3) := by
    apply dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
    intro a ha
    obtain ⟨htRoot, hvRoot⟩ := hcore a ha
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_C]
    have ht0 : (3 : k) * t.eval a - (r.eval a) ^ 2 = 0 :=
      sub_eq_zero.mpr htRoot
    have hv0 : (27 : k) * (p.coeff 3).eval a - (r.eval a) ^ 3 = 0 :=
      sub_eq_zero.mpr hvRoot
    linear_combination (1 / 27 : k) * hv0 -
      (2 / 9 : k) * r.eval a * ht0
  have hresIff : H ∣ ((12 : k[X]) * t - (5 : k[X]) * r ^ 2) ↔
      H ∣ r := by
    constructor
    · intro hres
      apply dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
      intro a ha
      have hres0 : (12 : k) * t.eval a - 5 * (r.eval a) ^ 2 = 0 := by
        obtain ⟨z, hz⟩ := hres
        have he := congrArg (fun f : k[X] => f.eval a) hz
        simpa [eval_sub, eval_mul, eval_pow, eval_C, ha] using he
      have htRoot := (hcore a ha).1
      have ht0 : (3 : k) * t.eval a - (r.eval a) ^ 2 = 0 :=
        sub_eq_zero.mpr htRoot
      have hrsq : (r.eval a) ^ 2 = 0 := by
        linear_combination -hres0 + 4 * ht0
      exact sq_eq_zero_iff.mp hrsq
    · intro hrdvd
      obtain ⟨r1, hr1⟩ := hrdvd
      have hrsq : H ∣ r ^ 2 := by
        refine ⟨H * r1 ^ 2, ?_⟩
        rw [hr1]
        ring
      have hthree : H ∣ (3 : k[X]) * t - r ^ 2 := by
        apply dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
        intro a ha
        have htRoot := (hcore a ha).1
        simpa [eval_sub, eval_mul, eval_pow, eval_C] using
          sub_eq_zero.mpr htRoot
      have h3t : H ∣ (3 : k[X]) * t := by
        simpa only [sub_add_cancel] using dvd_add hthree hrsq
      have h3unit : IsUnit (3 : k[X]) := by
        rw [← C_ofNat_poly]
        exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by norm_num))
      have htDvd : H ∣ t := (h3unit.dvd_mul_left).mp h3t
      exact dvd_sub (dvd_mul_of_dvd_right htDvd _)
        (dvd_mul_of_dvd_right hrsq _)
  exact ⟨g, r, t, hg, hr, ht, hBdvd, hresIff⟩

end CubicCorePolynomialOrder68

end Max11DegreeRoutes
