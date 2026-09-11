import Grok810ScaleZeroConeDefectFacesSpeedTPart11Scratch

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Source-facing constant first integrals -/

section SourceDefects810

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
/-- Source-facing packet: the affine-depressed core has integrated `ξ`,
`μ`, and `ο` polynomials equal to ground constants. -/
theorem normalized810ScaleZero_defectPolynomials_eq_C
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
        cXi cMu cOm : k) (A B C0 D0 E0 F0 G0 : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon
            zeta eta theta A B C0 D0 E0 F0 G0) =
        C (j / t) ∧
      (degreeZeroPrimitivePolynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0).natDegree =
        1 ∧
      degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 =
        Polynomial.C cXi ∧
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 =
        Polynomial.C cMu ∧
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 =
        Polynomial.C cOm ∧
      (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta, eta,
      theta, A, B, C0p, D0, E0, F0, G0, ht, hj, hjdiv, hHsq, hrowSrc, _hX,
      hcore⟩ :=
    normalized810ScaleZero_exists_primitivePolynomial hsource
  obtain ⟨hA, hB, hC, hD0, hE, hF, hG, hl, hder, hdeg⟩ := hcore
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  rcases hsource with
    ⟨_hH, _hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hDjac : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    obtain ⟨j0, _hj0, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
    have hrow0 :
        (p.coeff 0).derivative * q.coeff 1 -
          p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j0 :=
      degreeZeroCoefficientJacobianRow_810 hp hq hjac
    have hj0 : j0 = j :=
      Polynomial.C_injective (hrow0.symm.trans (by simpa [p, q] using hrowSrc))
    simpa [hj0, bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  let hRF : RatFunc k := RatFunc.C t
  let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (octicDepressionR810 hRF a7)
      (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (octicDepressionR810 hRF a7)
      (sourceToRatFunc68 q)
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
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
    p q j hRF (octicDepressionR810 hRF a7) hh hDjac
  have hdiv : RatFunc.C j / hRF = RatFunc.C (j / t) := by
    simp only [hRF, map_div₀]
  have hjacC : differentialJacobian ratFuncDerivation68 f g =
      Polynomial.C (RatFunc.C (j / t)) := by
    have hbr : differentialJacobian ratFuncDerivation68 f g =
        Polynomial.C (RatFunc.C j / hRF) := by
      simpa only [f, g] using hbracket
    simpa [hdiv] using hbr
  have hcoeff (n : ℕ) (hn : n ≠ 0) :
      (differentialJacobian ratFuncDerivation68 f g).coeff n = 0 := by
    rw [hjacC]
    simp [Polynomial.coeff_C, hn]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [show g.coeff 9 = RatFunc.C l from hl]
    exact ratFuncDerivation68_C l
  have h8 := (differentialJacobian_coeff_8_monicOcticDecic
    ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans
    (hcoeff 8 (by norm_num))
  have h7 := (differentialJacobian_coeff_7_monicOcticDecic
    ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans
    (hcoeff 7 (by norm_num))
  have h6 := (differentialJacobian_coeff_6_monicOcticDecic
    ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans
    (hcoeff 6 (by norm_num))
  have h5 := (differentialJacobian_coeff_5_monicOcticDecic
    ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans
    (hcoeff 5 (by norm_num))
  have h4 := (differentialJacobian_coeff_4_monicOcticDecic
    ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans
    (hcoeff 4 (by norm_num))
  have h3 := (differentialJacobian_coeff_3_monicOcticDecic
    ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans
    (hcoeff 3 (by norm_num))
  have h2 := (differentialJacobian_coeff_2_monicOcticDecic
    ratFuncDerivation68 f g hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans
    (hcoeff 2 (by norm_num))
  obtain ⟨l', beta', gamma', delta', epsilon', zeta', eta', theta', hl',
      hbeta', hgamma', hdelta', hepsilon', hzeta', heta', htheta'⟩ :=
    monicOcticDecic_rhoLoads_exist_ground810 f g (j / t) hf_high hf8 hf7
      hg_high hg10 hLconst hjacC
  let d := ratFuncDerivation68 (k := k)
  have h15 := (differentialJacobian_coeff_15_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans (hcoeff 15 (by norm_num))
  have h14 := (differentialJacobian_coeff_14_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans (hcoeff 14 (by norm_num))
  have h13 := (differentialJacobian_coeff_13_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans (hcoeff 13 (by norm_num))
  have h12 := (differentialJacobian_coeff_12_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans (hcoeff 12 (by norm_num))
  have h11 := (differentialJacobian_coeff_11_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans (hcoeff 11 (by norm_num))
  have h10 := (differentialJacobian_coeff_10_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans (hcoeff 10 (by norm_num))
  have h9 := (differentialJacobian_coeff_9_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hLconst).symm.trans (hcoeff 9 (by norm_num))
  have halpha := alphaResidual810_deriv_zero d (f.coeff 6) (g.coeff 8)
    (by linear_combination h15)
  have hbeta0 := betaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (g.coeff 7) hLconst (by linear_combination h14)
  have hgamma0 := gammaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (g.coeff 8) (g.coeff 6) hLconst halpha
    (by linear_combination h13)
  have hdelta0 := deltaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (g.coeff 8) (g.coeff 7)
    (g.coeff 5) hLconst halpha hbeta0 (by linear_combination h12)
  have hepsilon0 := epsilonResidual810_deriv_zero d (g.coeff 9)
    (f.coeff 6) (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2)
    (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 4) hLconst halpha hbeta0
    hgamma0 (by linear_combination h11)
  have hzeta0 := zetaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 3) hLconst
    halpha hbeta0 hgamma0 hdelta0 (by linear_combination h10)
  have heta0 := etaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 2) hLconst halpha hbeta0 hgamma0 hdelta0
    hepsilon0 (by linear_combination h9)
  have htheta0 := thetaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 1) hLconst halpha hbeta0 hgamma0
    hdelta0 hepsilon0 hzeta0 (by linear_combination h8)
  have hiota0 := iotaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 0) hLconst halpha hbeta0
    hgamma0 hdelta0 hepsilon0 hzeta0 heta0 (by linear_combination h7)
  have hxi0 := xiResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hLconst
    halpha hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0 heta0 htheta0 hiota0
    (by linear_combination h8) (by linear_combination h7)
    (by linear_combination h6) (by linear_combination h5)
    (by linear_combination h3)
  have hmu0 := muResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hLconst
    halpha hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0 heta0 htheta0 hiota0
    (by linear_combination h8) (by linear_combination h7)
    (by linear_combination h5)
  have hom0 := omicronResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hLconst
    halpha hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0 heta0 htheta0 hiota0
    (by linear_combination h8) (by linear_combination h7)
    (by linear_combination h6) (by linear_combination h5)
    (by linear_combination h4) (by linear_combination h2)
  have hkappa0 := kappaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) hLconst halpha hbeta0
    hgamma0 hdelta0 hepsilon0 hzeta0 heta0 htheta0
    (by linear_combination h8) (by linear_combination h6)
  have hnu0 := nuResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hLconst
    halpha hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0 heta0 htheta0 hiota0
    (by linear_combination h8) (by linear_combination h7)
    (by linear_combination h6) (by linear_combination h4)
  have hxi_res :
      xiResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) =
        degreeZeroXiIntegrated810 (RatFunc.C l')
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0p)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (algebraMap k[X] (RatFunc k) F0)
          (algebraMap k[X] (RatFunc k) G0)
          (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
          (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
          (RatFunc.C theta') := by
    rw [← hA, ← hB, ← hC, ← hD0, ← hE, ← hF, ← hG, hl']
    exact xiResidual810_eq_integrated (RatFunc.C l')
      (algebraMap k[X] (RatFunc k) A)
      (algebraMap k[X] (RatFunc k) B)
      (algebraMap k[X] (RatFunc k) C0p)
      (algebraMap k[X] (RatFunc k) D0)
      (algebraMap k[X] (RatFunc k) E0)
      (algebraMap k[X] (RatFunc k) F0)
      (algebraMap k[X] (RatFunc k) G0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1)
      (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
      (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
      (RatFunc.C theta')
      (by simpa [hA, hB, hl'] using hbeta')
      (by simpa [hA, hB, hC, hl'] using hgamma')
      (by simpa [hA, hB, hC, hD0, hl'] using hdelta')
      (by simpa [hA, hB, hC, hD0, hE, hl'] using hepsilon')
      (by simpa [hA, hB, hC, hD0, hE, hF, hl'] using hzeta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using heta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using htheta')
  have hmu_res :
      muResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) =
        degreeZeroMuIntegrated810 (RatFunc.C l')
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0p)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (algebraMap k[X] (RatFunc k) F0)
          (algebraMap k[X] (RatFunc k) G0)
          (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
          (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
          (RatFunc.C theta') := by
    rw [← hA, ← hB, ← hC, ← hD0, ← hE, ← hF, ← hG, hl']
    exact muResidual810_eq_integrated (RatFunc.C l')
      (algebraMap k[X] (RatFunc k) A)
      (algebraMap k[X] (RatFunc k) B)
      (algebraMap k[X] (RatFunc k) C0p)
      (algebraMap k[X] (RatFunc k) D0)
      (algebraMap k[X] (RatFunc k) E0)
      (algebraMap k[X] (RatFunc k) F0)
      (algebraMap k[X] (RatFunc k) G0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1)
      (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
      (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
      (RatFunc.C theta')
      (by simpa [hA, hB, hl'] using hbeta')
      (by simpa [hA, hB, hC, hl'] using hgamma')
      (by simpa [hA, hB, hC, hD0, hl'] using hdelta')
      (by simpa [hA, hB, hC, hD0, hE, hl'] using hepsilon')
      (by simpa [hA, hB, hC, hD0, hE, hF, hl'] using hzeta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using heta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using htheta')
  have hom_res :
      omicronResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) =
        degreeZeroOmicronIntegrated810 (RatFunc.C l')
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0p)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (algebraMap k[X] (RatFunc k) F0)
          (algebraMap k[X] (RatFunc k) G0)
          (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
          (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
          (RatFunc.C theta') := by
    rw [← hA, ← hB, ← hC, ← hD0, ← hE, ← hF, ← hG, hl']
    exact omicronResidual810_eq_integrated (RatFunc.C l')
      (algebraMap k[X] (RatFunc k) A)
      (algebraMap k[X] (RatFunc k) B)
      (algebraMap k[X] (RatFunc k) C0p)
      (algebraMap k[X] (RatFunc k) D0)
      (algebraMap k[X] (RatFunc k) E0)
      (algebraMap k[X] (RatFunc k) F0)
      (algebraMap k[X] (RatFunc k) G0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1)
      (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
      (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
      (RatFunc.C theta')
      (by simpa [hA, hB, hl'] using hbeta')
      (by simpa [hA, hB, hC, hl'] using hgamma')
      (by simpa [hA, hB, hC, hD0, hl'] using hdelta')
      (by simpa [hA, hB, hC, hD0, hE, hl'] using hepsilon')
      (by simpa [hA, hB, hC, hD0, hE, hF, hl'] using hzeta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using heta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using htheta')
  have hxi_map :
      algebraMap k[X] (RatFunc k)
          (degreeZeroXiPolynomial810 l' beta' gamma' delta' epsilon' zeta'
            eta' theta' A B C0p D0 E0 F0 G0) =
        xiResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) := by
    rw [hxi_res]
    exact algebraMap_degreeZeroXiPolynomial810 l' beta' gamma' delta'
      epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0
  have hmu_map :
      algebraMap k[X] (RatFunc k)
          (degreeZeroMuPolynomial810 l' beta' gamma' delta' epsilon' zeta'
            eta' theta' A B C0p D0 E0 F0 G0) =
        muResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) := by
    rw [hmu_res]
    exact algebraMap_degreeZeroMuPolynomial810 l' beta' gamma' delta'
      epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0
  have hom_map :
      algebraMap k[X] (RatFunc k)
          (degreeZeroOmicronPolynomial810 l' beta' gamma' delta' epsilon'
            zeta' eta' theta' A B C0p D0 E0 F0 G0) =
        omicronResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) := by
    rw [hom_res]
    exact algebraMap_degreeZeroOmicronPolynomial810 l' beta' gamma' delta'
      epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0
  have hxi_deriv :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroXiPolynomial810 l' beta' gamma' delta' epsilon'
              zeta' eta' theta' A B C0p D0 E0 F0 G0)) =
        0 := by
    rw [hxi_map]
    simpa [d, ratFuncDerivation68, ratFuncDerivation46_apply] using hxi0
  have hmu_deriv :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroMuPolynomial810 l' beta' gamma' delta' epsilon'
              zeta' eta' theta' A B C0p D0 E0 F0 G0)) =
        0 := by
    rw [hmu_map]
    simpa [d, ratFuncDerivation68, ratFuncDerivation46_apply] using hmu0
  have hom_deriv :
      ratFuncDerivation46
          (algebraMap k[X] (RatFunc k)
            (degreeZeroOmicronPolynomial810 l' beta' gamma' delta'
              epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0)) =
        0 := by
    rw [hom_map]
    simpa [d, ratFuncDerivation68, ratFuncDerivation46_apply] using hom0
  obtain ⟨cXi, hcXi⟩ :=
    degreeZeroXiPolynomial810_eq_C_of_ratFuncDeriv l' beta' gamma' delta'
      epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0 hxi_deriv
  obtain ⟨cMu, hcMu⟩ :=
    degreeZeroMuPolynomial810_eq_C_of_ratFuncDeriv l' beta' gamma' delta'
      epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0 hmu_deriv
  obtain ⟨cOm, hcOm⟩ :=
    degreeZeroOmicronPolynomial810_eq_C_of_ratFuncDeriv l' beta' gamma'
      delta' epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0 hom_deriv
  have hrho :
      rhoResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) =
        degreeZeroIntegratedPrimitive810 (RatFunc.C l')
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0p)
          (algebraMap k[X] (RatFunc k) D0)
          (algebraMap k[X] (RatFunc k) E0)
          (algebraMap k[X] (RatFunc k) F0)
          (algebraMap k[X] (RatFunc k) G0)
          (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
          (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
          (RatFunc.C theta') := by
    rw [← hA, ← hB, ← hC, ← hD0, ← hE, ← hF, ← hG, hl']
    exact rhoResidual810_eq_integrated (RatFunc.C l')
      (algebraMap k[X] (RatFunc k) A)
      (algebraMap k[X] (RatFunc k) B)
      (algebraMap k[X] (RatFunc k) C0p)
      (algebraMap k[X] (RatFunc k) D0)
      (algebraMap k[X] (RatFunc k) E0)
      (algebraMap k[X] (RatFunc k) F0)
      (algebraMap k[X] (RatFunc k) G0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1)
      (RatFunc.C beta') (RatFunc.C gamma') (RatFunc.C delta')
      (RatFunc.C epsilon') (RatFunc.C zeta') (RatFunc.C eta')
      (RatFunc.C theta')
      (by simpa [hA, hB, hl'] using hbeta')
      (by simpa [hA, hB, hC, hl'] using hgamma')
      (by simpa [hA, hB, hC, hD0, hl'] using hdelta')
      (by simpa [hA, hB, hC, hD0, hE, hl'] using hepsilon')
      (by simpa [hA, hB, hC, hD0, hE, hF, hl'] using hzeta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using heta')
      (by simpa [hA, hB, hC, hD0, hE, hF, hG, hl'] using htheta')
  let prim : k[X] :=
    degreeZeroPrimitivePolynomial810 l' beta' gamma' delta' epsilon' zeta'
      eta' theta' A B C0p D0 E0 F0 G0
  have hmap_prim :
      algebraMap k[X] (RatFunc k) prim =
        rhoResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5) (f.coeff 4)
          (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8)
          (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1) := by
    rw [hrho]
    exact algebraMap_degreeZeroPrimitivePolynomial810 l' beta' gamma'
      delta' epsilon' zeta' eta' theta' A B C0p D0 E0 F0 G0
  have hder_prim :
      algebraMap k[X] (RatFunc k) (derivative prim) =
        algebraMap k[X] (RatFunc k) (C (j / t)) := by
    rw [← ratFuncDerivation46_polynomial]
    have hderiv' :
        ratFuncDerivation68 (algebraMap k[X] (RatFunc k) prim) =
          RatFunc.C (j / t) := by
      rw [hmap_prim]
      have hd_rho :
          d (rhoResidual810 (g.coeff 9) (f.coeff 6) (f.coeff 5)
              (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
              (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6)
              (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
              (g.coeff 1)) =
            g.coeff 1 * d (f.coeff 0) - f.coeff 1 * d (g.coeff 0) :=
        rhoResidual810_deriv_eq_row d (g.coeff 9) (f.coeff 6) (f.coeff 5)
          (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
          (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
          (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hLconst halpha
          hbeta0 hgamma0 hdelta0 hepsilon0 hzeta0 heta0 htheta0 hiota0
          hkappa0 hmu0 hnu0 hxi0 hom0
      have hrow0 :
          g.coeff 1 * d (f.coeff 0) - f.coeff 1 * d (g.coeff 0) =
            RatFunc.C (j / t) :=
        degreeZeroRow_eq_constant_of_monic_differentialJacobian d f g
          (RatFunc.C (j / t)) hf_high hf8 hf7 hg_high hg10 hLconst hjacC
      have := hd_rho.trans hrow0
      simpa [d] using this
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply,
      RatFunc.algebraMap_C] using hderiv'
  have hpolyder : derivative prim = C (j / t) :=
    (RatFunc.algebraMap_injective k) hder_prim
  have hdeg' : prim.natDegree = 1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 prim (j / t)
      (div_ne_zero hj ht) hpolyder
  exact ⟨t, j, lambda, cleared, l', beta', gamma', delta', epsilon', zeta',
    eta', theta', cXi, cMu, cOm, A, B, C0p, D0, E0, F0, G0, ht, hj, hjdiv,
    hHsq, hpolyder, hdeg', hcXi,
    degreeZeroXiPolynomial810_natDegree_eq_zero_of_eq_C hcXi, hcMu,
    degreeZeroMuPolynomial810_natDegree_eq_zero_of_eq_C hcMu, hcOm,
    degreeZeroOmicronPolynomial810_natDegree_eq_zero_of_eq_C hcOm⟩

end SourceDefects810




end Max11DegreeRoutes
