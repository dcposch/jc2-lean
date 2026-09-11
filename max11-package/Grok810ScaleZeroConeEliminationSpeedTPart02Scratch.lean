import Grok810ScaleZeroConeEliminationSpeedTPart01Scratch

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Algebra map of the polynomial groups -/

section AlgebraMap810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 64000000 in
theorem algebraMap_rhoBetaGroupPolynomial810
    (A B C0 D0 E0 F0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (rhoBetaGroupPolynomial810 A B C0 D0 E0 F0) =
      rhoBetaGroup810
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0) := by
  simp only [rhoBetaGroupPolynomial810, rhoBetaGroup810, map_add, map_sub,
    map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 64000000 in
theorem algebraMap_rhoGammaGroupPolynomial810
    (A B C0 D0 E0 F0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (rhoGammaGroupPolynomial810 A B C0 D0 E0 F0) =
      rhoGammaGroup810
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0) := by
  simp only [rhoGammaGroupPolynomial810, rhoGammaGroup810, map_add, map_sub,
    map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 64000000 in
theorem algebraMap_rhoDeltaGroupPolynomial810
    (A B C0 D0 E0 F0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (rhoDeltaGroupPolynomial810 A B C0 D0 E0 F0) =
      rhoDeltaGroup810
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0) := by
  simp only [rhoDeltaGroupPolynomial810, rhoDeltaGroup810, map_add, map_sub,
    map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 64000000 in
theorem algebraMap_rhoEpsilonGroupPolynomial810
    (A B C0 D0 E0 F0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (rhoEpsilonGroupPolynomial810 A B C0 D0 E0 F0) =
      rhoEpsilonGroup810
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0) := by
  simp only [rhoEpsilonGroupPolynomial810, rhoEpsilonGroup810, map_add,
    map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 64000000 in
theorem algebraMap_rhoZetaGroupPolynomial810
    (A B C0 D0 E0 F0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (rhoZetaGroupPolynomial810 A B C0 D0 E0 F0) =
      rhoZetaGroup810
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0) := by
  simp only [rhoZetaGroupPolynomial810, rhoZetaGroup810, map_add, map_sub,
    map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 64000000 in
theorem algebraMap_rhoEtaGroupPolynomial810
    (A B C0 D0 E0 F0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (rhoEtaGroupPolynomial810 A B C0 D0 E0 F0) =
      rhoEtaGroup810
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0) := by
  simp only [rhoEtaGroupPolynomial810, rhoEtaGroup810, map_add, map_sub,
    map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 64000000 in
theorem algebraMap_rhoThetaGroupPolynomial810
    (A B C0 D0 E0 G0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (rhoThetaGroupPolynomial810 A B C0 D0 E0 G0) =
      rhoThetaGroup810
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) G0) := by
  simp only [rhoThetaGroupPolynomial810, rhoThetaGroup810, map_add, map_sub,
    map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 64000000 in
theorem algebraMap_rhoBaseGroupPolynomial810
    (l : k) (A B C0 D0 E0 F0 G0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (rhoBaseGroupPolynomial810 l A B C0 D0 E0 F0 G0) =
      rhoBaseGroup810 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0)
        (algebraMap k[X] (RatFunc k) G0) := by
  simp only [rhoBaseGroupPolynomial810, rhoBaseGroup810, map_add, map_sub,
    map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 64000000 in
theorem algebraMap_degreeZeroPrimitivePolynomial810
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0) =
      degreeZeroIntegratedPrimitive810 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D0)
        (algebraMap k[X] (RatFunc k) E0)
        (algebraMap k[X] (RatFunc k) F0)
        (algebraMap k[X] (RatFunc k) G0)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
        (RatFunc.C theta) := by
  simp only [degreeZeroPrimitivePolynomial810,
    degreeZeroIntegratedPrimitive810, map_add, Polynomial.smul_eq_C_mul,
    map_mul, RatFunc.algebraMap_C,
    algebraMap_rhoBaseGroupPolynomial810,
    algebraMap_rhoBetaGroupPolynomial810,
    algebraMap_rhoGammaGroupPolynomial810,
    algebraMap_rhoDeltaGroupPolynomial810,
    algebraMap_rhoEpsilonGroupPolynomial810,
    algebraMap_rhoZetaGroupPolynomial810,
    algebraMap_rhoEtaGroupPolynomial810,
    algebraMap_rhoThetaGroupPolynomial810]
set_option maxHeartbeats 64000000 in

theorem rhoResidual810_eq_integrated
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0
      beta gamma delta epsilon zeta eta theta : F)
    (hbeta : betaResidual810 L A B Q = beta)
    (hgamma : gammaResidual810 L A B C0 P R = gamma)
    (hdelta : deltaResidual810 L A B C0 D0 P Q S0 = delta)
    (hepsilon : epsilonResidual810 L A B C0 D0 E0 P Q R T0 = epsilon)
    (hzeta : zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0 = zeta)
    (heta : etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0 = eta)
    (htheta : thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0 =
      theta) :
    rhoResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 =
      degreeZeroIntegratedPrimitive810 L A B C0 D0 E0 F0 G0 beta gamma
        delta epsilon zeta eta theta := by
  simp only [rhoResidual810, degreeZeroIntegratedPrimitive810, hbeta,
    hgamma, hdelta, hepsilon, hzeta, heta, htheta]

end AlgebraMap810

/-! ## Polynomial core and ground loads -/

section PolynomialCore810

variable {k : Type*} [Field k] [CharZero k]
set_option maxHeartbeats 64000000 in

theorem octicDepressionR810_constantScale_eq_algebraMap
    (p : k[X][X]) (t : k) :
    octicDepressionR810 (RatFunc.C t)
        (algebraMap k[X] (RatFunc k) (p.coeff 7)) =
      algebraMap k[X] (RatFunc k)
        (C ((8 * t ^ 7) ⁻¹) * p.coeff 7) := by
  simp only [octicDepressionR810, map_mul, RatFunc.algebraMap_C,
    div_eq_mul_inv]
  rw [map_inv₀, map_mul, map_ofNat, map_pow]
  ring
set_option maxHeartbeats 64000000 in

theorem constantScale_monicOctic_polynomialCore810
    (p : k[X][X]) (t : k) (ht : t ≠ 0) :
    let r0 : k[X] := C ((8 * t ^ 7)⁻¹) * p.coeff 7
    let p0 : k[X][X] := p.comp ((X - C r0) * C (C t⁻¹))
    let f : (RatFunc k)[X] :=
      affineDepress68 (RatFunc.C t)
        (octicDepressionR810 (RatFunc.C t)
          (algebraMap k[X] (RatFunc k) (p.coeff 7)))
        (sourceToRatFunc68 p)
    algebraMap k[X] (RatFunc k) (p0.coeff 6) = f.coeff 6 ∧
      algebraMap k[X] (RatFunc k) (p0.coeff 5) = f.coeff 5 ∧
      algebraMap k[X] (RatFunc k) (p0.coeff 4) = f.coeff 4 ∧
      algebraMap k[X] (RatFunc k) (p0.coeff 3) = f.coeff 3 ∧
      algebraMap k[X] (RatFunc k) (p0.coeff 2) = f.coeff 2 ∧
      algebraMap k[X] (RatFunc k) (p0.coeff 1) = f.coeff 1 ∧
      algebraMap k[X] (RatFunc k) (p0.coeff 0) = f.coeff 0 := by
  intro r0 p0 f
  have hcenter :
      octicDepressionR810 (RatFunc.C t)
          (algebraMap k[X] (RatFunc k) (p.coeff 7)) =
        algebraMap k[X] (RatFunc k) r0 :=
    octicDepressionR810_constantScale_eq_algebraMap p t
  have hf_eq : f = p0.map (algebraMap k[X] (RatFunc k)) := by
    dsimp only [f, p0]
    rw [hcenter]
    exact affineDepress_source_constantScale_map68 p t r0 ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [hf_eq, Polynomial.coeff_map])
set_option maxHeartbeats 64000000 in

theorem ratFuncDerivation68_C (a : k) :
    ratFuncDerivation68 (RatFunc.C a) = 0 := by
  have hp := ratFuncDerivation46_polynomial (C a : k[X])
  simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hp
set_option maxHeartbeats 64000000 in

theorem ratFuncDerivation68_exists_C {c : RatFunc k}
    (hc : ratFuncDerivation68 c = 0) :
    ∃ a : k, c = RatFunc.C a := by
  apply GCD369RatFuncConstantsOfPolynomialDerivative
    ratFuncDerivation46_polynomial
  simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using hc

set_option maxHeartbeats 64000000 in
theorem monicOcticDecic_rhoLoads_exist_ground810
    (f g : (RatFunc k)[X]) (terminal : k)
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : ratFuncDerivation68 (g.coeff 9) = 0)
    (hjac : differentialJacobian ratFuncDerivation68 f g =
      Polynomial.C (RatFunc.C terminal)) :
    ∃ l beta gamma delta epsilon zeta eta theta : k,
      g.coeff 9 = RatFunc.C l ∧
      betaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (g.coeff 7) =
        RatFunc.C beta ∧
      gammaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (g.coeff 8) (g.coeff 6) = RatFunc.C gamma ∧
      deltaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (g.coeff 8) (g.coeff 7) (g.coeff 5) =
        RatFunc.C delta ∧
      epsilonResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (g.coeff 8) (g.coeff 7) (g.coeff 6)
          (g.coeff 4) = RatFunc.C epsilon ∧
      zetaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 3) = RatFunc.C zeta ∧
      etaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 2) =
        RatFunc.C eta ∧
      thetaResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 1) = RatFunc.C theta := by
  let d := ratFuncDerivation68 (k := k)
  have hcoeff (n : ℕ) (hn : n ≠ 0) :
      (differentialJacobian d f g).coeff n = 0 := by
    rw [hjac]
    simp [Polynomial.coeff_C, hn]
  have h15 := (differentialJacobian_coeff_15_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 15 (by norm_num))
  have h14 := (differentialJacobian_coeff_14_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 14 (by norm_num))
  have h13 := (differentialJacobian_coeff_13_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 13 (by norm_num))
  have h12 := (differentialJacobian_coeff_12_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 12 (by norm_num))
  have h11 := (differentialJacobian_coeff_11_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 11 (by norm_num))
  have h10 := (differentialJacobian_coeff_10_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 10 (by norm_num))
  have h9 := (differentialJacobian_coeff_9_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 9 (by norm_num))
  have h8 := (differentialJacobian_coeff_8_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 8 (by norm_num))
  have halpha := alphaResidual810_deriv_zero d (f.coeff 6) (g.coeff 8)
    (by linear_combination h15)
  have hbeta := betaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (g.coeff 7) hL (by linear_combination h14)
  have hgamma := gammaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (g.coeff 8) (g.coeff 6) hL halpha
    (by linear_combination h13)
  have hdelta := deltaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (g.coeff 8) (g.coeff 7)
    (g.coeff 5) hL halpha hbeta (by linear_combination h12)
  have hepsilon := epsilonResidual810_deriv_zero d (g.coeff 9)
    (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
    (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 4) hL halpha hbeta
    hgamma (by linear_combination h11)
  have hzeta := zetaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 3) hL
    halpha hbeta hgamma hdelta (by linear_combination h10)
  have heta := etaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 2) hL halpha hbeta hgamma hdelta hepsilon
    (by linear_combination h9)
  have htheta := thetaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 1) hL halpha hbeta hgamma hdelta
    hepsilon hzeta (by linear_combination h8)
  obtain ⟨l, hl⟩ := ratFuncDerivation68_exists_C hL
  obtain ⟨beta, hbetaC⟩ := ratFuncDerivation68_exists_C hbeta
  obtain ⟨gamma, hgammaC⟩ := ratFuncDerivation68_exists_C hgamma
  obtain ⟨delta, hdeltaC⟩ := ratFuncDerivation68_exists_C hdelta
  obtain ⟨epsilon, hepsilonC⟩ := ratFuncDerivation68_exists_C hepsilon
  obtain ⟨zeta, hzetaC⟩ := ratFuncDerivation68_exists_C hzeta
  obtain ⟨eta, hetaC⟩ := ratFuncDerivation68_exists_C heta
  obtain ⟨theta, hthetaC⟩ := ratFuncDerivation68_exists_C htheta
  exact ⟨l, beta, gamma, delta, epsilon, zeta, eta, theta, hl, hbetaC,
    hgammaC, hdeltaC, hepsilonC, hzetaC, hetaC, hthetaC⟩

end PolynomialCore810

/-! ## Source-facing polynomial trajectory -/

section SourcePrimitive810

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
/-- The monic constant-scale depression of a normalized scale-zero
`(8,10)` source has polynomial free-core letters, ground residual loads,
and grouped primitive of Newton degree one. -/
theorem normalized810ScaleZero_exists_primitivePolynomial
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta : k)
      (A B C0 D0 E0 F0 G0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
      localClearedFifteenthDefect810 (Polynomial.C t)
          (p.coeff 7) (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) lambda =
        Polynomial.C cleared ∧
      let hRF : RatFunc k := RatFunc.C t
      let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
      let f : (RatFunc k)[X] :=
        affineDepress68 hRF (octicDepressionR810 hRF a7)
          (sourceToRatFunc68 p)
      let g : (RatFunc k)[X] :=
        affineDepress68 hRF (octicDepressionR810 hRF a7)
          (sourceToRatFunc68 q)
      algebraMap k[X] (RatFunc k) A = f.coeff 6 ∧
        algebraMap k[X] (RatFunc k) B = f.coeff 5 ∧
        algebraMap k[X] (RatFunc k) C0 = f.coeff 4 ∧
        algebraMap k[X] (RatFunc k) D0 = f.coeff 3 ∧
        algebraMap k[X] (RatFunc k) E0 = f.coeff 2 ∧
        algebraMap k[X] (RatFunc k) F0 = f.coeff 1 ∧
        algebraMap k[X] (RatFunc k) G0 = f.coeff 0 ∧
        g.coeff 9 = RatFunc.C l ∧
        derivative
            (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
              zeta eta theta A B C0 D0 E0 F0 G0) =
          C (j / t) ∧
        (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta
            eta theta A B C0 D0 E0 F0 G0).natDegree =
          1 := by
  dsimp only
  obtain ⟨t, j, lambda, cleared, ht, hj, hHsq, hrow, hX, hN, hprim⟩ :=
    normalized810ScaleZero_exists_degreeZeroPrimitive hsource
  rcases hsource with
    ⟨_hH, _hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    obtain ⟨j0, _hj0, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
    have hrow0 :
        (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j0 :=
      degreeZeroCoefficientJacobianRow_810 hp hq hjac
    have hj0 : j0 = j :=
      Polynomial.C_injective (hrow0.symm.trans (by simpa [p, q] using hrow))
    simpa [hj0, bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  let hRF : RatFunc k := RatFunc.C t
  let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (octicDepressionR810 hRF a7)
      (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (octicDepressionR810 hRF a7)
      (sourceToRatFunc68 q)
  obtain ⟨hAmap, hBmap, hCmap, hDmap, hEmap, hFmap, hGmap⟩ :=
    constantScale_monicOctic_polynomialCore810 p t ht
  let r0 : k[X] := C ((8 * t ^ 7)⁻¹) * p.coeff 7
  let p0 : k[X][X] := p.comp ((X - C r0) * C (C t⁻¹))
  let A : k[X] := p0.coeff 6
  let B : k[X] := p0.coeff 5
  let C0p : k[X] := p0.coeff 4
  let D0 : k[X] := p0.coeff 3
  let E0 : k[X] := p0.coeff 2
  let F0 : k[X] := p0.coeff 1
  let G0 : k[X] := p0.coeff 0
  have hA : algebraMap k[X] (RatFunc k) A = f.coeff 6 := by
    simpa [A, p0, r0, f, hRF, a7] using hAmap
  have hB : algebraMap k[X] (RatFunc k) B = f.coeff 5 := by
    simpa [B, p0, r0, f, hRF, a7] using hBmap
  have hC : algebraMap k[X] (RatFunc k) C0p = f.coeff 4 := by
    simpa [C0p, p0, r0, f, hRF, a7] using hCmap
  have hD0 : algebraMap k[X] (RatFunc k) D0 = f.coeff 3 := by
    simpa [D0, p0, r0, f, hRF, a7] using hDmap
  have hE : algebraMap k[X] (RatFunc k) E0 = f.coeff 2 := by
    simpa [E0, p0, r0, f, hRF, a7] using hEmap
  have hF : algebraMap k[X] (RatFunc k) F0 = f.coeff 1 := by
    simpa [F0, p0, r0, f, hRF, a7] using hFmap
  have hG : algebraMap k[X] (RatFunc k) G0 = f.coeff 0 := by
    simpa [G0, p0, r0, f, hRF, a7] using hGmap
  have hh : hRF ≠ 0 := by
    intro hzero
    apply ht
    apply RatFunc.C_injective
    simpa only [hRF, map_zero] using hzero
  have hp8' : p.coeff 8 = H ^ 4 := by simpa [p] using hp8
  have hq10' : q.coeff 10 = H ^ 5 := by simpa [q] using hq10
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 8) = hRF ^ 8 := by
    have hpow : (C t ^ 2) ^ 4 = (C t : k[X]) ^ 8 := by
      rw [← pow_mul]
    simp only [hp8', hHsq, hpow, hRF, map_pow, RatFunc.algebraMap_C]
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = hRF ^ 10 := by
    have hpow : (C t ^ 2) ^ 5 = (C t : k[X]) ^ 10 := by
      rw [← pow_mul]
    simp only [hq10', hHsq, hpow, hRF, map_pow, RatFunc.algebraMap_C]
  have hpDep := affineDepress_sourceOctic68 p hRF
    (octicDepressionR810 hRF a7) hp hh hpTop
  have hL0 : depressedL68 hRF (octicDepressionR810 hRF a7) a7 = 0 :=
    depressedL68_eq_zero_of_octicCenter hRF a7 hh
  have hf7 : f.coeff 7 = 0 := by
    dsimp only [f]; rw [hpDep, coeff_depressedOctic68_seven, hL0]
  have hf8 : f.coeff 8 = 1 := by
    dsimp only [f]; rw [hpDep, coeff_depressedOctic68_eight]
  have hf_high : ∀ n, 8 < n → f.coeff n = 0 := by
    intro n hn
    dsimp only [f]
    rw [hpDep, coeff_depressedOctic68_of_gt_eight _ _ _ _ _ _ _ _ hn]
  have hg_high_src : ∀ n, 10 < n →
      (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = hRF ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, _hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) hRF
      (octicDepressionR810 hRF a7) hh hgTop hg_high_src
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j hRF (octicDepressionR810 hRF a7) hh hD
  have hdiv : RatFunc.C j / hRF = RatFunc.C (j / t) := by
    simp only [hRF, map_div₀]
  have hjacC : differentialJacobian ratFuncDerivation68 f g =
      Polynomial.C (RatFunc.C (j / t)) := by
    have hbr : differentialJacobian ratFuncDerivation68 f g =
        Polynomial.C (RatFunc.C j / hRF) := by
      simpa only [f, g] using hbracket
    simpa [hdiv] using hbr
  have hNrat :
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 := by
    simpa only [p, q] using hN
  have hLval :
      depressedL810 hRF (octicDepressionR810 hRF a7)
          (algebraMap k[X] (RatFunc k) (q.coeff 9)) =
        RatFunc.C (-lambda / 4) := by
    have hNmapped := congrArg (algebraMap k[X] (RatFunc k)) hNrat
    have hNrf :
        5 * a7 * hRF ^ 2 - 4 * algebraMap k[X] (RatFunc k) (q.coeff 9) =
          RatFunc.C lambda * hRF ^ 9 := by
      simpa only [hHsq, hRF, a7, map_sub, map_mul, map_pow, map_ofNat,
        RatFunc.algebraMap_C] using hNmapped
    have hL := depressedL810_eq_of_ninthPower hRF a7
      (algebraMap k[X] (RatFunc k) (q.coeff 9)) (RatFunc.C lambda) hh
      (by simpa using hNrf)
    simpa [map_neg, map_div₀, map_ofNat] using hL
  have hg9L : g.coeff 9 =
      depressedL810 hRF (octicDepressionR810 hRF a7)
        (algebraMap k[X] (RatFunc k) (q.coeff 9)) := by
    dsimp only [g]
    rw [hg9]
    simp [depressedL810, octicDepressionR810, sourceToRatFunc68,
      sourceToRatFunc46]
  have hg9const : g.coeff 9 = RatFunc.C (-lambda / 4) := by
    rw [hg9L, hLval]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hg9const]
    exact ratFuncDerivation68_C (-lambda / 4)
  obtain ⟨l, beta, gamma, delta, epsilon, zeta, eta, theta, hl, hbeta,
      hgamma, hdelta, hepsilon, hzeta, heta, htheta⟩ :=
    monicOcticDecic_rhoLoads_exist_ground810 f g (j / t) hf_high hf8 hf7
      hg_high hg10 hLconst hjacC
  have hrho :
      rhoResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) =
        degreeZeroIntegratedPrimitive810 (RatFunc.C l)
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0p)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (algebraMap k[X] (RatFunc k) F0)
          (algebraMap k[X] (RatFunc k) G0)
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
          (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
          (RatFunc.C theta) := by
    rw [← hA, ← hB, ← hC, ← hD0, ← hE, ← hF, ← hG, hl]
    exact rhoResidual810_eq_integrated (RatFunc.C l)
      (algebraMap k[X] (RatFunc k) A)
      (algebraMap k[X] (RatFunc k) B)
      (algebraMap k[X] (RatFunc k) C0p)
      (algebraMap k[X] (RatFunc k) D0)
      (algebraMap k[X] (RatFunc k) E0)
      (algebraMap k[X] (RatFunc k) F0)
      (algebraMap k[X] (RatFunc k) G0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1)
      (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
      (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
      (RatFunc.C theta)
      (by simpa [hA, hB, hl] using hbeta)
      (by simpa [hA, hB, hC, hl] using hgamma)
      (by simpa [hA, hB, hC, hD0, hl] using hdelta)
      (by simpa [hA, hB, hC, hD0, hE, hl] using hepsilon)
      (by simpa [hA, hB, hC, hD0, hE, hF, hl] using hzeta)
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl] using heta)
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl] using htheta)
  let prim : k[X] :=
    degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta eta
      theta A B C0p D0 E0 F0 G0
  have hmap :
      algebraMap k[X] (RatFunc k) prim =
        rhoResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) := by
    rw [hrho]
    exact algebraMap_degreeZeroPrimitivePolynomial810 l beta gamma delta
      epsilon zeta eta theta A B C0p D0 E0 F0 G0
  have hder :
      algebraMap k[X] (RatFunc k) (derivative prim) =
        algebraMap k[X] (RatFunc k) (C (j / t)) := by
    rw [← ratFuncDerivation46_polynomial]
    have hderiv :
        ratFuncDerivation68 (algebraMap k[X] (RatFunc k) prim) =
          RatFunc.C (j / t) := by
      rw [hmap]
      dsimp [p, q, f, g, hRF, a7]
      exact hprim
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply,
      RatFunc.algebraMap_C] using hderiv
  have hpolyder : derivative prim = C (j / t) :=
    (RatFunc.algebraMap_injective k) hder
  have hdeg : prim.natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 prim (j / t)
      (div_ne_zero hj ht) hpolyder
  refine ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
    theta, A, B, C0p, D0, E0, F0, G0, ht, hj, div_ne_zero hj ht, hHsq,
    ?_, ?_, ?_⟩
  · simpa [p, q] using hrow
  · simpa [p, q] using hX
  · exact ⟨hA, hB, hC, hD0, hE, hF, hG, hl, hpolyder, hdeg⟩

end SourcePrimitive810


end Max11DegreeRoutes
