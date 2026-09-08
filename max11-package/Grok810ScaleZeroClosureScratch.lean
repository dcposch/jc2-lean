import Grok810ScaleZeroConeRatioTiesScratch

/-! # Scale-zero unique-`G₀` Jacobian closure for normalized `(8,10)`, `H = 0`

Continuation of `Grok810ScaleZeroConeRatioTiesScratch` on the constant core
`H = (C t)²`.  That file reduced `normalized810ScaleZero_impossible` to
`normalized810ScaleZero_coneRatioTiesResidual`, whose named leftover is
unique-`G₀` of Newton degree one with `l = 0` and the other six letters
of degree zero (`UniqueHighG0DegOneCone810`).

CAS job `derive_810_scale_zero_cone_ratio_ties.py` (flag
`CAS810_JAC1_ONLY=1`) substitutes that chamber into the unused degree-one
Jacobian coefficient
`2 V G' + W F' - F W' - 2 E X'`
of `differentialJacobian_coeff_1_monicOcticDecic`.  After triangular
solution of `η, θ, ι`:

* `V = (5/4) G₀ + const`,
* `W` is independent of `G₀` once `l = 0`,
* `F` and `E` are constants,
* `X` is affine in `G₀`,

so the row is `G₀' · ((5/2) G₀ + const)`.  The leading coefficient in
the time variable is `(5/2) (G₀')² ≠ 0`.  Constancy of the Jacobian
coefficient therefore forces `d G₀ = 0`, contradicting `deg G₀ = 1`.

No total-degree or twice-prime theorem is used.  No `sorry`, no new
axioms, no finite-root shortcut.  The theorems
`normalized810ScaleZero_impossible` and
`planeKeller810ScaleZeroExclusion_closed` are not claimed: mixed cones
in which some of `A, B, C₀, D₀, E₀, F₀` is nonconstant remain after the
parent unique weighted `ξ`/`μ`/`ο` faces and the `A`-ratio faces.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Ground rationals and degree-zero letters -/

section ConstDeriv810

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]
variable (d : Derivation k F F)

private theorem d_frac (m n : ℕ) : d ((m : F) / (n : F)) = 0 := by
  have hm : d (m : F) = 0 := d.map_natCast m
  have hn : d (n : F) = 0 := d.map_natCast n
  rw [div_eq_mul_inv]
  simp [Derivation.leibniz, Derivation.leibniz_inv, hm, hn]

private theorem d_five_four : d (5 / 4 : F) = 0 := by
  convert d_frac d 5 4 using 2
  norm_num

private theorem d_nine_eight : d (9 / 8 : F) = 0 := by
  convert d_frac d 9 8 using 2
  norm_num

private theorem d_five_thirtytwo : d (5 / 32 : F) = 0 := by
  convert d_frac d 5 32 using 2
  norm_num

private theorem d_five_sixteen : d (5 / 16 : F) = 0 := by
  convert d_frac d 5 16 using 2
  norm_num

private theorem d_seven_eight : d (7 / 8 : F) = 0 := by
  convert d_frac d 7 8 using 2
  norm_num

private theorem d_three_four : d (3 / 4 : F) = 0 := by
  convert d_frac d 3 4 using 2
  norm_num

private theorem d_five_eight : d (5 / 8 : F) = 0 := by
  convert d_frac d 5 8 using 2
  norm_num

private theorem d_nine_one_two_eight : d (9 / 128 : F) = 0 := by
  convert d_frac d 9 128 using 2
  norm_num

private theorem d_five_one_two_eight : d (5 / 128 : F) = 0 := by
  convert d_frac d 5 128 using 2
  norm_num

private theorem d_seven_one_two_eight : d (7 / 128 : F) = 0 := by
  convert d_frac d 7 128 using 2
  norm_num

private theorem d_one_five_one_two_eight : d (15 / 128 : F) = 0 := by
  convert d_frac d 15 128 using 2
  norm_num

private theorem d_two_one_one_zero_two_four : d (21 / 1024 : F) = 0 := by
  convert d_frac d 21 1024 using 2
  norm_num

private theorem d_nine_sixtyfour : d (9 / 64 : F) = 0 := by
  convert d_frac d 9 64 using 2
  norm_num

private theorem d_one_five_sixteen : d (15 / 16 : F) = 0 := by
  convert d_frac d 15 16 using 2
  norm_num

end ConstDeriv810

section DegreeZeroMap810

variable {k : Type*} [Field k] [CharZero k]

theorem eq_C_of_natDegree_eq_zero810 {p : k[X]} (h : p.natDegree = 0) :
    p = C (p.coeff 0) :=
  eq_C_of_natDegree_le_zero h.le

theorem ratFuncDerivation68_algebraMap_of_natDegree_eq_zero
    {p : k[X]} (h : p.natDegree = 0) :
    ratFuncDerivation68 (algebraMap k[X] (RatFunc k) p) = 0 := by
  rw [eq_C_of_natDegree_eq_zero810 h, RatFunc.algebraMap_C]
  exact ratFuncDerivation68_C (p.coeff 0)

theorem ratFuncDerivation68_algebraMap_ne_zero_of_natDegree_eq_one
    {p : k[X]} (h : p.natDegree = 1) :
    ratFuncDerivation68 (algebraMap k[X] (RatFunc k) p) ≠ 0 := by
  have hder : p.derivative ≠ 0 := by
    intro hz
    have hpC : p = C (p.coeff 0) := eq_C_of_derivative_eq_zero hz
    have h0 : p.natDegree = 0 := by
      rw [hpC, natDegree_C]
    exact (Nat.succ_ne_zero 0).symm (h0.symm.trans h)
  intro hmap
  have hder_map :
      algebraMap k[X] (RatFunc k) p.derivative = 0 := by
    rw [← ratFuncDerivation46_polynomial]
    simpa [ratFuncDerivation68] using hmap
  apply hder
  apply RatFunc.algebraMap_injective k
  simpa using hder_map

end DegreeZeroMap810

/-! ## Triangular coordinates of a constant octic core -/

section ConstantCoreDeriv810

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]
variable (d : Derivation k F F)

theorem dP_eq_zero_of_dA_dalpha
    (A P : F) (hA : d A = 0)
    (halpha : d (alphaResidual810 A P) = 0) :
    d P = 0 := by
  have : d P - (5 / 4 : F) * d A = 0 := by
    simpa [alphaResidual810, map_sub, Derivation.leibniz, d_five_four d,
      zero_mul, add_zero] using halpha
  simpa [hA] using this

theorem dQ_eq_zero_of_constant_AB
    (L A B Q : F) (hL : d L = 0) (hA : d A = 0) (hB : d B = 0)
    (hbeta : d (betaResidual810 L A B Q) = 0) :
    d Q = 0 := by
  have :
      d Q - (5 / 4 : F) * d B - (9 / 8 : F) * L * d A = 0 := by
    simpa [betaResidual810, map_sub, Derivation.leibniz, d_five_four d,
      d_nine_eight d, hL, zero_mul, add_zero, mul_zero] using hbeta
  simpa [hA, hB] using this

set_option maxHeartbeats 4000000 in
theorem dR_eq_zero_of_constant_ABC
    (L A B C0 P R : F)
    (hL : d L = 0) (hA : d A = 0) (hB : d B = 0) (hC : d C0 = 0)
    (hP : d P = 0)
    (hgamma : d (gammaResidual810 L A B C0 P R) = 0) :
    d R = 0 := by
  have hsq : d (A ^ 2) = 0 := by
    simp [pow_two, Derivation.leibniz, hA]
  have halpha0 : d (alphaResidual810 A P) = 0 := by
    simp [alphaResidual810, map_sub, Derivation.leibniz, d_five_four d,
      hA, hP, zero_mul, add_zero]
  have :
      d R - ((5 / 4 : F) * d C0 + (5 / 32 : F) * d (A ^ 2) +
        (9 / 8 : F) * L * d B +
        d (alphaResidual810 A P) * A + alphaResidual810 A P * d A) = 0 := by
    simpa [gammaResidual810, map_sub, map_add, Derivation.leibniz,
      d_five_four d, d_five_thirtytwo d, d_nine_eight d, hL, hA, hB, hC,
      hP, hsq, halpha0, zero_mul, add_zero, mul_zero] using hgamma
  simpa [hA, hB, hC, hsq, halpha0] using this

set_option maxHeartbeats 8000000 in
theorem dS_eq_zero_of_constant_ABCD
    (L A B C0 D0 P Q S0 : F)
    (hL : d L = 0) (hA : d A = 0) (hB : d B = 0) (hC : d C0 = 0)
    (hD : d D0 = 0) (hP : d P = 0) (hQ : d Q = 0)
    (hdelta : d (deltaResidual810 L A B C0 D0 P Q S0) = 0) :
    d S0 = 0 := by
  have hsq : d (A ^ 2) = 0 := by
    simp [pow_two, Derivation.leibniz, hA]
  have halpha0 : d (alphaResidual810 A P) = 0 := by
    simp [alphaResidual810, map_sub, Derivation.leibniz, d_five_four d,
      hA, hP, zero_mul, add_zero]
  have hbeta0 : d (betaResidual810 L A B Q) = 0 := by
    simp [betaResidual810, map_sub, Derivation.leibniz, d_five_four d,
      d_nine_eight d, hL, hA, hB, hQ, zero_mul, add_zero, mul_zero]
  simpa [deltaResidual810, map_sub, map_add, map_mul, map_pow,
    Derivation.leibniz, d_five_four d, d_nine_eight d, d_seven_eight d,
    d_five_sixteen d, d_nine_one_two_eight d, hL, hA, hB, hC, hD, hP, hQ,
    hsq, halpha0, hbeta0, zero_mul, add_zero, mul_zero] using hdelta

set_option maxHeartbeats 8000000 in
theorem dT_eq_zero_of_constant_ABCDE
    (L A B C0 D0 E0 P Q R T0 : F)
    (hL : d L = 0) (hA : d A = 0) (hB : d B = 0) (hC : d C0 = 0)
    (hD : d D0 = 0) (hE : d E0 = 0)
    (hP : d P = 0) (hQ : d Q = 0) (hR : d R = 0)
    (hepsilon : d (epsilonResidual810 L A B C0 D0 E0 P Q R T0) = 0) :
    d T0 = 0 := by
  have hsqA : d (A ^ 2) = 0 := by
    simp [pow_two, Derivation.leibniz, hA]
  have hsqB : d (B ^ 2) = 0 := by
    simp [pow_two, Derivation.leibniz, hB]
  have hcub : d (A ^ 3) = 0 := by
    have : A ^ 3 = A ^ 2 * A := by ring
    simp [this, Derivation.leibniz, hsqA, hA]
  have halpha0 : d (alphaResidual810 A P) = 0 := by
    simp [alphaResidual810, map_sub, Derivation.leibniz, d_five_four d,
      hA, hP, zero_mul, add_zero]
  have hbeta0 : d (betaResidual810 L A B Q) = 0 := by
    simp [betaResidual810, map_sub, Derivation.leibniz, d_five_four d,
      d_nine_eight d, hL, hA, hB, hQ, zero_mul, add_zero, mul_zero]
  have hgamma0 : d (gammaResidual810 L A B C0 P R) = 0 := by
    simp [gammaResidual810, map_sub, map_add, Derivation.leibniz,
      d_five_four d, d_five_thirtytwo d, d_nine_eight d, hL, hA, hB, hC,
      hP, hR, hsqA, halpha0, zero_mul, add_zero, mul_zero]
  simpa [epsilonResidual810, map_sub, map_add, map_mul, map_pow,
    Derivation.leibniz, d_five_four d, d_five_thirtytwo d, d_five_sixteen d,
    d_five_one_two_eight d, d_nine_eight d, d_nine_sixtyfour d,
    d_seven_eight d, d_three_four d, hL, hA, hB, hC, hD, hE, hP, hQ, hR,
    hsqA, hsqB, hcub, halpha0, hbeta0, hgamma0, zero_mul, add_zero,
    mul_zero] using hepsilon

set_option maxHeartbeats 8000000 in
theorem dU_eq_zero_of_constant_ABCDEF
    (L A B C0 D0 E0 F0 P Q R S0 U0 : F)
    (hL : d L = 0) (hA : d A = 0) (hB : d B = 0) (hC : d C0 = 0)
    (hD : d D0 = 0) (hE : d E0 = 0) (hF : d F0 = 0)
    (hP : d P = 0) (hQ : d Q = 0) (hR : d R = 0) (hS : d S0 = 0)
    (hzeta : d (zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0) = 0) :
    d U0 = 0 := by
  have hsqA : d (A ^ 2) = 0 := by
    simp [pow_two, Derivation.leibniz, hA]
  have hsqB : d (B ^ 2) = 0 := by
    simp [pow_two, Derivation.leibniz, hB]
  have hcub : d (A ^ 3) = 0 := by
    have : A ^ 3 = A ^ 2 * A := by ring
    simp [this, Derivation.leibniz, hsqA, hA]
  have halpha0 : d (alphaResidual810 A P) = 0 := by
    simp [alphaResidual810, map_sub, Derivation.leibniz, d_five_four d,
      hA, hP, zero_mul, add_zero]
  have hbeta0 : d (betaResidual810 L A B Q) = 0 := by
    simp [betaResidual810, map_sub, Derivation.leibniz, d_five_four d,
      d_nine_eight d, hL, hA, hB, hQ, zero_mul, add_zero, mul_zero]
  have hgamma0 : d (gammaResidual810 L A B C0 P R) = 0 := by
    simp [gammaResidual810, map_sub, map_add, Derivation.leibniz,
      d_five_four d, d_five_thirtytwo d, d_nine_eight d, hL, hA, hB, hC,
      hP, hR, hsqA, halpha0, zero_mul, add_zero, mul_zero]
  have hdelta0 : d (deltaResidual810 L A B C0 D0 P Q S0) = 0 := by
    simp [deltaResidual810, map_sub, map_add, map_mul, map_pow,
      Derivation.leibniz, d_five_four d, d_nine_eight d, d_seven_eight d,
      d_five_sixteen d, d_nine_one_two_eight d, hL, hA, hB, hC, hD, hP, hQ,
      hS, hsqA, halpha0, hbeta0, zero_mul, add_zero, mul_zero]
  simpa [zetaResidual810, map_sub, map_add, map_mul, map_pow,
    Derivation.leibniz, d_five_four d, d_nine_eight d, d_seven_eight d,
    d_three_four d, d_five_eight d, d_five_sixteen d, d_seven_one_two_eight d,
    d_one_five_one_two_eight d, d_two_one_one_zero_two_four d,
    d_nine_sixtyfour d, d_nine_one_two_eight d, hL, hA, hB, hC, hD, hE, hF,
    hP, hQ, hR, hS, hsqA, hsqB, hcub, halpha0, hbeta0, hgamma0, hdelta0,
    zero_mul, add_zero, mul_zero] using hzeta

end ConstantCoreDeriv810

/-! ## Degree-one Jacobian on unique-`G₀` with `l = 0` -/

section UniqueG0Jac1_810

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

set_option maxHeartbeats 80000000 in
/-- The unique-`G₀` degree-one chamber with `l = 0` is empty: the
degree-one Jacobian coefficient is a nonzero multiple of `d G₀`. -/
theorem uniqueHighG0DegOne_impossible_of_l_zero
    (d : Derivation k F F) (f g : F[X]) (c : F)
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) (hL0 : g.coeff 9 = 0)
    (hjac : differentialJacobian d f g = Polynomial.C c)
    (hA : d (f.coeff 6) = 0) (hB : d (f.coeff 5) = 0)
    (hC : d (f.coeff 4) = 0) (hD : d (f.coeff 3) = 0)
    (hE : d (f.coeff 2) = 0) (hF : d (f.coeff 1) = 0)
    (hG : d (f.coeff 0) ≠ 0) :
    False := by
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
  have h7 := (differentialJacobian_coeff_7_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 7 (by norm_num))
  have h1 := (differentialJacobian_coeff_1_monicOcticDecic d f g
    hf_high hf8 hf7 hg_high hg10 hL).symm.trans (hcoeff 1 (by norm_num))
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
  have hiota := iotaResidual810_deriv_zero d (g.coeff 9) (f.coeff 6)
    (f.coeff 5) (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1)
    (f.coeff 0) (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5)
    (g.coeff 4) (g.coeff 3) (g.coeff 2) (g.coeff 0) hL halpha hbeta
    hgamma hdelta hepsilon hzeta heta (by linear_combination h7)
  have hP : d (g.coeff 8) = 0 :=
    dP_eq_zero_of_dA_dalpha d (f.coeff 6) (g.coeff 8) hA halpha
  have hQ : d (g.coeff 7) = 0 :=
    dQ_eq_zero_of_constant_AB d (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (g.coeff 7) hL hA hB hbeta
  have hR : d (g.coeff 6) = 0 :=
    dR_eq_zero_of_constant_ABC d (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (g.coeff 8) (g.coeff 6) hL hA hB hC hP hgamma
  have hS : d (g.coeff 5) = 0 :=
    dS_eq_zero_of_constant_ABCD d (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (f.coeff 3) (g.coeff 8) (g.coeff 7) (g.coeff 5) hL hA hB
      hC hD hP hQ hdelta
  have hT : d (g.coeff 4) = 0 :=
    dT_eq_zero_of_constant_ABCDE d (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (g.coeff 8) (g.coeff 7)
      (g.coeff 6) (g.coeff 4) hL hA hB hC hD hE hP hQ hR hepsilon
  have hU : d (g.coeff 3) = 0 :=
    dU_eq_zero_of_constant_ABCDEF d (g.coeff 9) (f.coeff 6) (f.coeff 5)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (g.coeff 8)
      (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 3) hL hA hB hC hD hE hF
      hP hQ hR hS hzeta
  have h9z :
      (10 : F) * d (f.coeff 0) - (8 : F) * d (g.coeff 2) = 0 := by
    simpa [hA, hB, hC, hD, hE, hF, hP, hQ, hR, hS, hT] using h9
  have hV : d (g.coeff 2) = (5 / 4 : F) * d (f.coeff 0) := by
    linear_combination -(1 / 8 : F) * h9z
  have h8z : (8 : F) * d (g.coeff 1) = 0 := by
    have hraw :
        (9 : F) * g.coeff 9 * d (f.coeff 0) - (8 : F) * d (g.coeff 1) =
          0 := by
      simpa [hA, hB, hC, hD, hE, hF, hP, hQ, hR, hS, hT, hU] using h8
    simpa [hL0] using hraw
  have hW : d (g.coeff 1) = 0 :=
    (mul_eq_zero.mp h8z).resolve_left (by norm_num)
  have h1z :
      (2 : F) * g.coeff 2 * d (f.coeff 0) -
          (2 : F) * f.coeff 2 * d (g.coeff 0) = 0 := by
    simpa [hF, hW] using h1
  have h7z :
      (8 : F) * g.coeff 8 * d (f.coeff 0) -
          (6 : F) * f.coeff 6 * d (g.coeff 2) -
          (8 : F) * d (g.coeff 0) = 0 := by
    simpa [hA, hB, hC, hD, hE, hF, hQ, hR, hS, hT, hU] using h7
  have hX :
      d (g.coeff 0) =
        (g.coeff 8 - (15 / 16 : F) * f.coeff 6) * d (f.coeff 0) := by
    have h7s :
        (8 : F) * g.coeff 8 * d (f.coeff 0) -
            (6 : F) * f.coeff 6 * ((5 / 4 : F) * d (f.coeff 0)) -
            (8 : F) * d (g.coeff 0) = 0 := by
      simpa [hV] using h7z
    have hscale :
        d (g.coeff 0) -
            (g.coeff 8 - (15 / 16 : F) * f.coeff 6) * d (f.coeff 0) =
          0 := by
      linear_combination -(1 / 8 : F) * h7s
    exact eq_of_sub_eq_zero hscale
  have hVE :
      g.coeff 2 * d (f.coeff 0) =
        f.coeff 2 *
          ((g.coeff 8 - (15 / 16 : F) * f.coeff 6) * d (f.coeff 0)) := by
    simpa [hX] using (by linear_combination (1 / 2 : F) * h1z :
      g.coeff 2 * d (f.coeff 0) = f.coeff 2 * d (g.coeff 0))
  have hVeq :
      g.coeff 2 =
        f.coeff 2 * (g.coeff 8 - (15 / 16 : F) * f.coeff 6) := by
    have hmul :
        (g.coeff 2 -
            f.coeff 2 * (g.coeff 8 - (15 / 16 : F) * f.coeff 6)) *
          d (f.coeff 0) = 0 := by
      linear_combination hVE
    exact eq_of_sub_eq_zero ((mul_eq_zero.mp hmul).resolve_right hG)
  have hdV : d (g.coeff 2) = 0 := by
    have h2 : d (2 : F) = 0 := d.map_natCast 2
    simp [hVeq, Derivation.leibniz, hE, hP, hA, d_one_five_sixteen d, h2,
      zero_mul, add_zero, mul_zero]
  have : (5 / 4 : F) * d (f.coeff 0) = 0 := by
    simpa [hdV] using hV
  have h54ne : (5 / 4 : F) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  exact hG (eq_zero_of_ne_zero_of_mul_left_eq_zero h54ne this)

end UniqueG0Jac1_810

/-! ## Source-facing instantiation -/

section SourceChamber810

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 80000000 in
/-- Source letters of a unique-`G₀` degree-one chamber with `l = 0` make
the degree-one Jacobian coefficient a nonzero multiple of `d G₀`. -/
theorem uniqueHighG0DegOne_source_impossible_of_l_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (A B C0 D0 E0 F0 G0 : k[X])
    (hcone : UniqueHighG0DegOneCone810 A B C0 D0 E0 F0 G0)
    (hmaps :
      ∃ t l : k,
        t ≠ 0 ∧ l = 0 ∧ H = (Polynomial.C t) ^ 2 ∧
          let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
          let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
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
            g.coeff 9 = RatFunc.C l) :
    False := by
  rcases hcone with ⟨hGdeg, hA0, hB0, hC0, hD0, hE0, hF0⟩
  obtain ⟨t, l, ht, hl0, hHsq, hmaps'⟩ := hmaps
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  let hRF : RatFunc k := RatFunc.C t
  let a7 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 7)
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (octicDepressionR810 hRF a7) (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (octicDepressionR810 hRF a7) (sourceToRatFunc68 q)
  rcases hmaps' with ⟨hAmap, hBmap, hCmap, hDmap, hEmap, hFmap, hGmap, hl⟩
  rcases hsource with
    ⟨_hH, _hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
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
  have hL0dep : depressedL68 hRF (octicDepressionR810 hRF a7) a7 = 0 :=
    depressedL68_eq_zero_of_octicCenter hRF a7 hh
  have hf7 : f.coeff 7 = 0 := by
    dsimp only [f]; rw [hpDep, coeff_depressedOctic68_seven, hL0dep]
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
  obtain ⟨j0, _hj0, hjac0⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hDjac : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j0) := by
    simpa [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac0
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j0 hRF (octicDepressionR810 hRF a7) hh hDjac
  have hdiv : RatFunc.C j0 / hRF = RatFunc.C (j0 / t) := by
    simp only [hRF, map_div₀]
  have hjacC : differentialJacobian ratFuncDerivation68 f g =
      Polynomial.C (RatFunc.C (j0 / t)) := by
    have hbr : differentialJacobian ratFuncDerivation68 f g =
        Polynomial.C (RatFunc.C j0 / hRF) := by
      simpa only [f, g] using hbracket
    simpa [hdiv] using hbr
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hl, hl0]
    simpa using ratFuncDerivation68_C (0 : k)
  have hL0g : g.coeff 9 = 0 := by
    rw [hl, hl0]
    simp
  have hdA : ratFuncDerivation68 (f.coeff 6) = 0 := by
    rw [← hAmap]
    exact ratFuncDerivation68_algebraMap_of_natDegree_eq_zero hA0
  have hdB : ratFuncDerivation68 (f.coeff 5) = 0 := by
    rw [← hBmap]
    exact ratFuncDerivation68_algebraMap_of_natDegree_eq_zero hB0
  have hdC : ratFuncDerivation68 (f.coeff 4) = 0 := by
    rw [← hCmap]
    exact ratFuncDerivation68_algebraMap_of_natDegree_eq_zero hC0
  have hdD : ratFuncDerivation68 (f.coeff 3) = 0 := by
    rw [← hDmap]
    exact ratFuncDerivation68_algebraMap_of_natDegree_eq_zero hD0
  have hdE : ratFuncDerivation68 (f.coeff 2) = 0 := by
    rw [← hEmap]
    exact ratFuncDerivation68_algebraMap_of_natDegree_eq_zero hE0
  have hdF : ratFuncDerivation68 (f.coeff 1) = 0 := by
    rw [← hFmap]
    exact ratFuncDerivation68_algebraMap_of_natDegree_eq_zero hF0
  have hdG : ratFuncDerivation68 (f.coeff 0) ≠ 0 := by
    rw [← hGmap]
    exact ratFuncDerivation68_algebraMap_ne_zero_of_natDegree_eq_one hGdeg
  exact uniqueHighG0DegOne_impossible_of_l_zero
    ratFuncDerivation68 f g (RatFunc.C (j0 / t)) hf_high hf8 hf7 hg_high
    hg10 hLconst hL0g hjacC hdA hdB hdC hdD hdE hdF hdG

end SourceChamber810

/-! ## Residual after unique-`G₀` of degree one -/

section ClosureResidual810

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- The extracted monic-depression core of a scale-zero source cannot
be unique-`G₀` of Newton degree one with `l = 0`. -/
theorem uniqueHighG0DegOne_existsPrimitive_false
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ¬ ∃ (A B C0 D0 E0 F0 G0 : k[X]) (l : k),
        UniqueHighG0DegOneCone810 A B C0 D0 E0 F0 G0 ∧
          l = 0 ∧
            ∃ (t j lambda cleared beta gamma delta epsilon zeta eta
                theta : k),
              t ≠ 0 ∧ H = (Polynomial.C t) ^ 2 ∧
                let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
                let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
                let hRF : RatFunc k := RatFunc.C t
                let a7 : RatFunc k :=
                  algebraMap k[X] (RatFunc k) (p.coeff 7)
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
                  g.coeff 9 = RatFunc.C l := by
  rintro ⟨A, B, C0, D0, E0, F0, G0, l, hcone, hl0, t, j, lambda, cleared,
      beta, gamma, delta, epsilon, zeta, eta, theta, ht, hHsq, hmaps⟩
  exact uniqueHighG0DegOne_source_impossible_of_l_zero hsource A B C0 D0
    E0 F0 G0 hcone ⟨t, l, ht, hl0, hHsq, hmaps⟩

/-- Remaining cones after the unique-`G₀` degree-one chamber is killed
by the degree-one Jacobian coefficient.  Mixed chambers in which some of
`A, B, C₀, D₀, E₀, F₀` is nonconstant, after the parent unique weighted
`ξ`/`μ`/`ο` faces and the `A`-ratio faces, are not claimed empty. -/
theorem normalized810ScaleZero_coneClosureResidual
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
        Polynomial.C (j / t) ∧
      (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0).natDegree =
        0 ∧
      ¬ ARatioLeadsXiCone810 A B C0 D0 E0 F0 G0 ∧
      (UniqueHighG0DegOneCone810 A B C0 D0 E0 F0 G0 → l = 0) :=
  normalized810ScaleZero_coneRatioTiesResidual hsource

theorem normalized810ScaleZero_impossible_of_closureResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hres :
      (∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
          cXi cMu cOm : k) (A B C0 D0 E0 F0 G0 : k[X]),
        t ≠ 0 ∧ j ≠ 0 ∧ j / t ≠ 0 ∧ H = (Polynomial.C t) ^ 2 ∧
          derivative
              (degreeZeroPrimitivePolynomial810 l beta gamma delta
                epsilon zeta eta theta A B C0 D0 E0 F0 G0) =
            Polynomial.C (j / t) ∧
          (degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta
              theta A B C0 D0 E0 F0 G0).natDegree =
            0 ∧
          (degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta
              theta A B C0 D0 E0 F0 G0).natDegree =
            0 ∧
          (degreeZeroOmicronPolynomial810 l beta gamma delta epsilon zeta
              eta theta A B C0 D0 E0 F0 G0).natDegree =
            0 ∧
          ¬ ARatioLeadsXiCone810 A B C0 D0 E0 F0 G0 ∧
          (UniqueHighG0DegOneCone810 A B C0 D0 E0 F0 G0 → l = 0)) →
        False) :
    False :=
  hres (normalized810ScaleZero_coneClosureResidual hsource)

end ClosureResidual810

#print axioms eq_C_of_natDegree_eq_zero810
#print axioms ratFuncDerivation68_algebraMap_of_natDegree_eq_zero
#print axioms ratFuncDerivation68_algebraMap_ne_zero_of_natDegree_eq_one
#print axioms uniqueHighG0DegOne_impossible_of_l_zero
#print axioms uniqueHighG0DegOne_source_impossible_of_l_zero
#print axioms uniqueHighG0DegOne_existsPrimitive_false
#print axioms normalized810ScaleZero_coneClosureResidual
#print axioms normalized810ScaleZero_impossible_of_closureResidual

end Max11DegreeRoutes
