import Sol68ScaleTwoAlignedNonsquareAfterLowerOneMixedLocalClosureScratch

/-! # Exact split of the final coordinate-divisor allocation -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

section CoordinateSplitAlgebra68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- A split simple quadratic dividing a product either divides one factor or
its two distinct roots are allocated transversely between the factors. -/
theorem simpleQuadratic_dvd_product_coordinate_split_68
    (H r phi : k[X]) (hdeg : H.natDegree = 2)
    (hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0)
    (hdvd : H ∣ r * phi) :
    H ∣ r ∨ H ∣ phi ∨
      ∃ a b : k, a ≠ b ∧ H.eval a = 0 ∧ H.eval b = 0 ∧
        r.eval a = 0 ∧ phi.eval a ≠ 0 ∧
        r.eval b ≠ 0 ∧ phi.eval b = 0 := by
  classical
  by_cases hr : H ∣ r
  · exact Or.inl hr
  by_cases hp : H ∣ phi
  · exact Or.inr (Or.inl hp)
  right
  right
  have hra : ∃ a : k, H.eval a = 0 ∧ r.eval a ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    exact hr (dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
      (fun a ha => hnone a ha))
  have hpa : ∃ a : k, H.eval a = 0 ∧ phi.eval a ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    exact hp (dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
      (fun a ha => hnone a ha))
  obtain ⟨b, hb, hrb⟩ := hra
  obtain ⟨a, ha, hpa⟩ := hpa
  have hprodA : (r * phi).eval a = 0 :=
    eval_eq_zero_of_dvd_of_eval_eq_zero hdvd ha
  have hprodB : (r * phi).eval b = 0 :=
    eval_eq_zero_of_dvd_of_eval_eq_zero hdvd hb
  have hra0 : r.eval a = 0 := by
    simp only [eval_mul] at hprodA
    exact (mul_eq_zero.mp hprodA).resolve_right hpa
  have hpb0 : phi.eval b = 0 := by
    simp only [eval_mul] at hprodB
    exact (mul_eq_zero.mp hprodB).resolve_left hrb
  refine ⟨a, b, ?_, ha, hb, hra0, hpa, hrb, hpb0⟩
  intro hab
  subst b
  exact hrb hra0

/-- The exact first unused faces at an `r=0`, `phi≠0` root. -/
theorem terminalAfterLowerOne_rRoot_faces_68
    (H b phi w d eDot kap : k[X]) (j a : k)
    (ha : H.eval a = 0) (hphi : phi.eval a ≠ 0)
    (hI4 : b * phi + (6 : k[X]) * H * w * d = 0)
    (hrow : H * b * w * eDot - d * kap = C j * H ^ 4) :
    b.eval a = 0 ∧
      b.derivative.eval a * phi.eval a +
        6 * H.derivative.eval a * w.eval a * d.eval a = 0 ∧
      (d.eval a = 0 ∨ kap.eval a = 0) ∧
      H.derivative.eval a * b.eval a * w.eval a * eDot.eval a -
        (d.derivative.eval a * kap.eval a +
          d.eval a * kap.derivative.eval a) = 0 := by
  have hI4a := congrArg (fun P : k[X] => P.eval a) hI4
  simp only [eval_add, eval_mul, eval_C, eval_zero, ha, zero_mul] at hI4a
  have hI4a' : b.eval a * phi.eval a = 0 := by simpa using hI4a
  have hb : b.eval a = 0 :=
    (mul_eq_zero.mp hI4a').resolve_right hphi
  have hI4der := congrArg (fun P : k[X] => P.derivative.eval a) hI4
  simp only [derivative_add, derivative_mul, derivative_C, derivative_zero,
    eval_add, eval_mul, eval_C, eval_zero, ha, hb, zero_mul, mul_zero,
    zero_add, add_zero] at hI4der
  have hI4face : b.derivative.eval a * phi.eval a +
      6 * H.derivative.eval a * w.eval a * d.eval a = 0 := by
    simpa only [eval_ofNat, mul_assoc] using hI4der
  have hrowa := congrArg (fun P : k[X] => P.eval a) hrow
  simp only [eval_sub, eval_mul, eval_pow, eval_C, ha, zero_mul, zero_pow]
    at hrowa
  have hdk : d.eval a * kap.eval a = 0 := by
    have hz : -(d.eval a * kap.eval a) = 0 := by simpa using hrowa
    exact neg_eq_zero.mp hz
  have hrowder := congrArg (fun P : k[X] => P.derivative.eval a) hrow
  simp only [derivative_sub, derivative_mul, derivative_pow, derivative_C,
    derivative_zero, eval_sub, eval_add, eval_mul, eval_pow, eval_C,
    eval_ofNat, eval_zero, ha, hb, zero_mul, mul_zero, zero_pow] at hrowder
  have hrowface : H.derivative.eval a * b.eval a * w.eval a * eDot.eval a -
      (d.derivative.eval a * kap.eval a +
        d.eval a * kap.derivative.eval a) = 0 := by
    simpa [hb] using hrowder
  exact ⟨hb, hI4face, mul_eq_zero.mp hdk, hrowface⟩

/-- The base terminal row adds its exact scalar split at a `phi=0` root to
the two already transported differentiated faces. -/
theorem terminalAfterLowerOne_phiRoot_faces_68
    (H b phi w d eDot kap : k[X]) (j a : k)
    (ha : H.eval a = 0) (hphi : phi.eval a = 0)
    (hsimple : H.derivative.eval a ≠ 0)
    (hI4 : b * phi + (6 : k[X]) * H * w * d = 0)
    (hrow : H * b * w * eDot - d * kap = C j * H ^ 4) :
    b.eval a * phi.derivative.eval a +
        6 * H.derivative.eval a * w.eval a * d.eval a = 0 ∧
      H.derivative.eval a * b.eval a * w.eval a * eDot.eval a -
        (d.derivative.eval a * kap.eval a +
          d.eval a * kap.derivative.eval a) = 0 ∧
      (d.eval a = 0 ∨ kap.eval a = 0) := by
  have hnext := terminalAfterLowerOne_phiZero_next_faces_68
    H b phi w d eDot kap j a ha hphi hsimple hI4 hrow
  have hrowa := congrArg (fun P : k[X] => P.eval a) hrow
  simp only [eval_sub, eval_mul, eval_pow, eval_C, ha, zero_mul, zero_pow]
    at hrowa
  have hdk : d.eval a * kap.eval a = 0 := by
    have hz : -(d.eval a * kap.eval a) = 0 := by simpa using hrowa
    exact neg_eq_zero.mp hz
  exact ⟨hnext.1, hnext.2.1, mul_eq_zero.mp hdk⟩

end CoordinateSplitAlgebra68

section CoordinateSplitSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Complete source-facing classification at the current API boundary.  The
normalized source carries no `x`-degree bounds on these quotient polynomials,
so the transverse two-root allocation is retained with its exact first
unused faces rather than collapsed by an invalid primality argument. -/
theorem NonsquareAlignedSourceCurveData68.terminalAfterLowerOneCoordinateSplitPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) (hj : j ≠ 0) :
    ∃ (r t X Yd phi1 k1 b2 d2 w2 : k[X]),
      p.coeff 4 = H * t ∧
      (3 : k[X]) * t - r ^ 2 = H * X ∧
      (27 : k[X]) * p.coeff 3 - r ^ 3 = H * Yd ∧
      b2 * phi1 + (6 : k[X]) * H * w2 * d2 = 0 ∧
      (let A0 := cubicANumerator68 t r
       let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
       let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
         (p.coeff 3) t r
       let eDot := terminalEDerivativeNumerator68 H E0
       H * b2 * w2 * eDot - d2 * k1 = C j * H ^ 4) ∧
      (H ∣ r ∨ H ∣ phi1 ∨
        (let A0 := cubicANumerator68 t r
         let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
         let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
           (p.coeff 3) t r
         let eDot := terminalEDerivativeNumerator68 H E0
         ∃ a b : k, a ≠ b ∧ H.eval a = 0 ∧ H.eval b = 0 ∧
           r.eval a = 0 ∧ phi1.eval a ≠ 0 ∧
           r.eval b ≠ 0 ∧ phi1.eval b = 0 ∧
           b2.eval a = 0 ∧
           b2.derivative.eval a * phi1.eval a +
             6 * H.derivative.eval a * w2.eval a * d2.eval a = 0 ∧
           (d2.eval a = 0 ∨ k1.eval a = 0) ∧
           H.derivative.eval a * b2.eval a * w2.eval a * eDot.eval a -
             (d2.derivative.eval a * k1.eval a +
               d2.eval a * k1.derivative.eval a) = 0 ∧
           b2.eval b * phi1.derivative.eval b +
             6 * H.derivative.eval b * w2.eval b * d2.eval b = 0 ∧
           H.derivative.eval b * b2.eval b * w2.eval b * eDot.eval b -
             (d2.derivative.eval b * k1.eval b +
               d2.eval b * k1.derivative.eval b) = 0 ∧
           (d2.eval b = 0 ∨ k1.eval b = 0))) := by
  obtain ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
      ht, hX, hY, hI4, hrow, hdvd, _hfaces⟩ :=
    S.terminalAfterLowerOneCoordinateDvdPacket (H := H)
      hdeg hp hq hp6 hq8 haligned hjac hj
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha => nonsquare_natDegree_two_derivative_ne_zero hdeg
      NonsquarePolynomial46.not_sq ha
  have hsplit := simpleQuadratic_dvd_product_coordinate_split_68
    H r phi1 hdeg hsimple hdvd
  let A0 := cubicANumerator68 t r
  let C0 := cubicCNumerator68 H (p.coeff 2) (p.coeff 3) t r
  let E0 := cubicENumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
    (p.coeff 3) t r
  let eDot := terminalEDerivativeNumerator68 H E0
  have hrow' : H * b2 * w2 * eDot - d2 * k1 = C j * H ^ 4 := by
    simpa only [A0, C0, E0, eDot] using hrow
  have hsplit' : H ∣ r ∨ H ∣ phi1 ∨
      ∃ a b : k, a ≠ b ∧ H.eval a = 0 ∧ H.eval b = 0 ∧
        r.eval a = 0 ∧ phi1.eval a ≠ 0 ∧
        r.eval b ≠ 0 ∧ phi1.eval b = 0 ∧
        b2.eval a = 0 ∧
        b2.derivative.eval a * phi1.eval a +
          6 * H.derivative.eval a * w2.eval a * d2.eval a = 0 ∧
        (d2.eval a = 0 ∨ k1.eval a = 0) ∧
        H.derivative.eval a * b2.eval a * w2.eval a * eDot.eval a -
          (d2.derivative.eval a * k1.eval a +
            d2.eval a * k1.derivative.eval a) = 0 ∧
        b2.eval b * phi1.derivative.eval b +
          6 * H.derivative.eval b * w2.eval b * d2.eval b = 0 ∧
        H.derivative.eval b * b2.eval b * w2.eval b * eDot.eval b -
          (d2.derivative.eval b * k1.eval b +
            d2.eval b * k1.derivative.eval b) = 0 ∧
        (d2.eval b = 0 ∨ k1.eval b = 0) := by
    rcases hsplit with hr | hp | hmixed
    · exact Or.inl hr
    · exact Or.inr (Or.inl hp)
    · right
      right
      obtain ⟨a, b, hab, ha, hb, hra, hpa, hrb, hpb⟩ := hmixed
      have hrf := terminalAfterLowerOne_rRoot_faces_68
        H b2 phi1 w2 d2 eDot k1 j a ha hpa hI4 hrow'
      have hpf := terminalAfterLowerOne_phiRoot_faces_68
        H b2 phi1 w2 d2 eDot k1 j b hb hpb (hsimple b hb) hI4 hrow'
      exact ⟨a, b, hab, ha, hb, hra, hpa, hrb, hpb,
        hrf.1, hrf.2.1, hrf.2.2.1, hrf.2.2.2,
        hpf.1, hpf.2.1, hpf.2.2⟩
  exact ⟨r, t, X, Yd, phi1, k1, b2, d2, w2,
    ht, hX, hY, hI4, hrow, hsplit'⟩

end CoordinateSplitSource68

end Max11DegreeRoutes
