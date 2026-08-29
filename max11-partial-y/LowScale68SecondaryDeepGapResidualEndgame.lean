import LowScale68SecondaryDeepGapResidualOneForms
import LowScale68SecondaryResidualRowTwoSystem
import LowScale68SecondaryResidualRowTwoFaces
import LowScale68SecondaryResidualRowTwoBalanced
import LowScale68SecondaryResidualBalancedSelector
import LowScale68SecondaryResidualRowOneFaces
import LowScale68SecondaryResidualRowOneSystem
import LowScale68SecondaryResidualBalancedEndgame
import LowScale68SecondaryResidualLoadZeroEndgame

/-! # Residual row-two/row-one endgame on the first-deep chamber `n < g < 3n/2`

The selector `maximalExpandedIntegratedPolynomialLowerSystem_deepGapResidualSelect68`
packs residual I4/I3 on `n < 2g ∧ 2g < 3n`.  This module restricts to the
open first-deep interval `n < g` (so automatically `n < 2g`) and extracts
the residual one-forms on every selected face.

Load-above I4 forces `beta = 0`.  After the additional row-one
`alpha`/`c`/`gamma` cancellations, row-one sits below `12n-3g-1` on the
whole `2g < 3n` window.  Row-zero and row-two drop below their residual
cubic indices once `beta = 0`.  The double window therefore closes,
including the fibre `b = d = e = 0`, `c ≠ 0`.  Middle load-above likewise
closes.  The remaining window is middle `g + h ≤ 3n`, whose unique
heaviest unresolved coefficient is `(5/72) beta a^3` at `6n`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section DeepGapResidualEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Chamber arithmetic -/

theorem firstDeep_gap_gt_radius
    (n g : ℕ) (hchamber : n < g ∧ 2 * g < 3 * n) :
    n < g :=
  hchamber.1

theorem firstDeep_two_mul_gap_lt_three
    (n g : ℕ) (hchamber : n < g ∧ 2 * g < 3 * n) :
    2 * g < 3 * n :=
  hchamber.2

theorem firstDeep_gap_lt_two_radius
    (n g : ℕ) (hn : 0 < n) (hchamber : n < g ∧ 2 * g < 3 * n) :
    g < 2 * n :=
  deepGap_gap_lt_two_radius n g hn hchamber.2

theorem firstDeep_not_eq_radius
    (n g : ℕ) (hchamber : n < g ∧ 2 * g < 3 * n) :
    g ≠ n :=
  ne_of_gt hchamber.1

theorem firstDeep_not_eq_four_radius
    (n g : ℕ) (hchamber : n < g ∧ 2 * g < 3 * n) :
    g ≠ 4 * n := by
  omega

theorem firstDeep_index_pos
    (n g : ℕ) (hn : 0 < n) (hchamber : n < g ∧ 2 * g < 3 * n)
    {w : ℕ} (hw : 1 < w) :
    0 < w * n - g :=
  deepGap_index_pos n g hn hchamber.2 hw

theorem firstDeep_natDegree_mul_derivative_lt68
    (p q : k[X]) (u v : ℕ)
    (hu : p.natDegree ≤ u) (hv : 1 < v) (hq : q.natDegree < v) :
    (p * derivative q).natDegree < u + v - 1 := by
  have hq' : q.natDegree ≤ v - 1 := Nat.le_sub_one_of_lt hq
  have hd : (derivative q).natDegree ≤ v - 2 := by
    have h := natDegree_derivative_le q
    omega
  have hmul := natDegree_mul_le_of_le hu hd
  omega

theorem firstDeep_natDegree_derivative_mul_lt68
    (p q : k[X]) (u v : ℕ)
    (hu0 : 0 < u) (hu : p.natDegree ≤ u) (hq : q.natDegree < v) :
    (derivative p * q).natDegree < u + v - 1 := by
  have hd : (derivative p).natDegree ≤ u - 1 :=
    (natDegree_derivative_le p).trans (by omega)
  have hq' : q.natDegree ≤ v - 1 := Nat.le_sub_one_of_lt hq
  have hmul := natDegree_mul_le_of_le hd hq'
  omega

/-! ## Residual `Q` after `beta = 0` -/

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantFourPolynomial68_degree_lt_cubicFace_of_firstDeep_beta
    (gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantFourPolynomial68
      0 0 gamma delta epsilon zeta A B c D e).natDegree <
        9 * n - 3 * g := by
  simp only [secondaryLoadInvariantFourPolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

set_option maxHeartbeats 2000000 in
theorem secondaryLoadInvariantThreePolynomial68_degree_lt_cubicFace_of_firstDeep
    (beta gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g : ℕ) (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (secondaryLoadInvariantThreePolynomial68
      0 beta gamma delta epsilon zeta A B c D e).natDegree <
        10 * n - 3 * g := by
  simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

/-! ## Extra row-one cancellations below `12n-3g-1` -/

def cubicLoadVAlphaLowPolynomial68
    (beta gamma delta epsilon eta : k)
    (A B c D : k[X]) : k[X] :=
  (-5 / 36 * beta : k) • (A * B) + (5 / 6 * beta : k) • D +
    (2 / 3 * gamma : k) • c + (1 / 2 * delta : k) • B +
    (1 / 3 * epsilon : k) • A + C eta

theorem cubicLoadVAlphaRestPolynomial68_eq_Er_gamma_low
    (alpha beta gamma delta epsilon eta : k)
    (A B c D e : k[X]) :
    cubicLoadVAlphaRestPolynomial68 alpha beta gamma delta epsilon eta
        A B c D e =
      alpha • ((1 / 3 : k) • (A * c) + e) +
        (1 / 9 * gamma : k) • A ^ 2 +
        cubicLoadVAlphaLowPolynomial68 beta gamma delta epsilon eta
          A B c D := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadVAlphaRestPolynomial68, cubicLoadVAlphaLowPolynomial68,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_zero,
    RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowOneAlphaErCore_eq_zero (alpha : k) (A Er : k[X]) :
    (2 : k) • (cubicLoadTAlphaCorePolynomial68 alpha A * derivative Er) -
      (2 : k) • (((1 / 3 : k) • A ^ 2) * derivative (alpha • Er)) = 0 := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadTAlphaCorePolynomial68, Polynomial.smul_eq_C_mul,
    derivative_smul, derivative_mul, derivative_C, map_add, map_sub, map_mul,
    map_pow, map_zero, RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 4000000 in
theorem cubicLoadRowOneAlphaCCore_eq_zero (alpha : k) (A c : k[X]) :
    (2 : k) • ((alpha • c) *
        derivative ((1 / 27 : k) • A ^ 3)) -
      (2 : k) • (c * derivative (cubicLoadVAlphaCorePolynomial68 alpha A)) =
        0 := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadVAlphaCorePolynomial68, derivative_smul, derivative_mul,
    derivative_pow, derivative_C, Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_zero, RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 4000000 in
theorem cubicLoadRowOneGammaACore_eq_zero (gamma : k) (A : k[X]) :
    (2 : k) • (((2 / 3 * gamma : k) • A) *
        derivative ((1 / 27 : k) • A ^ 3)) -
      (2 : k) • (((1 / 3 : k) • A ^ 2) *
        derivative ((1 / 9 * gamma : k) • A ^ 2)) = 0 := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [derivative_smul, derivative_mul, derivative_pow, derivative_C,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_zero,
    RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_natCast, map_one]
  ring

/-- Residual row-one load after removing the three identically vanishing
`10n-g-1` pairs. -/
def cubicLoadRowOneDeepGapRestPolynomial68
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) : k[X] :=
  let Tc := cubicLoadTAlphaCorePolynomial68 alpha A
  let Ur := cubicLoadUAlphaRestPolynomial68 beta gamma delta zeta A B c
  let Vr := cubicLoadVAlphaRestPolynomial68 alpha beta gamma delta epsilon
    eta A B c D e
  let Vlow := cubicLoadVAlphaLowPolynomial68 beta gamma delta epsilon eta
    A B c D
  let C0c := (1 / 3 : k) • A ^ 2
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := (1 / 3 : k) • (A * c) + e
  let E := Ec + Er
  Ur * derivative D +
    (2 : k) • ((alpha • c) * derivative Er) +
    (2 : k) • (((2 / 3 * gamma : k) • A) * derivative Er) +
    (2 : k) • (((5 / 6 * beta : k) • B + C epsilon) * derivative E) -
    (2 : k) • (C0c * derivative Vlow) -
    (2 : k) • (c * derivative Vr) -
    D * derivative Ur

set_option maxHeartbeats 8000000 in
theorem cubicLoadRowOneAlphaRestPolynomial68_eq_deepGapRest
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) :
    cubicLoadRowOneAlphaRestPolynomial68 alpha beta gamma delta epsilon
        zeta eta A B c D e =
      cubicLoadRowOneDeepGapRestPolynomial68 alpha beta gamma delta
          epsilon zeta eta A B c D e +
        ((2 : k) • (cubicLoadTAlphaCorePolynomial68 alpha A *
            derivative ((1 / 3 : k) • (A * c) + e)) -
          (2 : k) • (((1 / 3 : k) • A ^ 2) *
            derivative (alpha • ((1 / 3 : k) • (A * c) + e)))) +
        ((2 : k) • ((alpha • c) *
            derivative ((1 / 27 : k) • A ^ 3)) -
          (2 : k) • (c * derivative
            (cubicLoadVAlphaCorePolynomial68 alpha A))) +
        ((2 : k) • (((2 / 3 * gamma : k) • A) *
            derivative ((1 / 27 : k) • A ^ 3)) -
          (2 : k) • (((1 / 3 : k) • A ^ 2) *
            derivative ((1 / 9 * gamma : k) • A ^ 2))) := by
  have hVr := cubicLoadVAlphaRestPolynomial68_eq_Er_gamma_low
    alpha beta gamma delta epsilon eta A B c D e
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadRowOneAlphaRestPolynomial68,
    cubicLoadRowOneDeepGapRestPolynomial68, cubicLoadTAlphaRestPolynomial68,
    hVr, derivative_add, Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_zero, RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_natCast, map_one]
  ring

theorem cubicLoadRowOneAlphaRestPolynomial68_eq_deepGapRest'
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) :
    cubicLoadRowOneAlphaRestPolynomial68 alpha beta gamma delta epsilon
        zeta eta A B c D e =
      cubicLoadRowOneDeepGapRestPolynomial68 alpha beta gamma delta
        epsilon zeta eta A B c D e := by
  rw [cubicLoadRowOneAlphaRestPolynomial68_eq_deepGapRest,
    cubicLoadRowOneAlphaErCore_eq_zero,
    cubicLoadRowOneAlphaCCore_eq_zero,
    cubicLoadRowOneGammaACore_eq_zero, add_zero, add_zero, add_zero]

set_option maxHeartbeats 4000000 in
theorem cubicLoadVAlphaLowPolynomial68_degree_le
    (beta gamma delta epsilon eta : k)
    (A B c D : k[X]) (n g : ℕ)
    (hn : 0 < n) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g) :
    (cubicLoadVAlphaLowPolynomial68 beta gamma delta epsilon eta
      A B c D).natDegree ≤ 5 * n - g := by
  have hg2 : g < 2 * n := deepGap_gap_lt_two_radius n g hn hrel
  have hAB : ((-5 / 36 * beta : k) • (A * B)).natDegree ≤ 5 * n - g :=
    (natDegree_smul_le _ _).trans <|
      natDegree_mul_le.trans (by
        have := Nat.add_le_add hA hB
        omega)
  have hD' : ((5 / 6 * beta : k) • D).natDegree ≤ 5 * n - g :=
    (natDegree_smul_le _ _).trans hD
  have hc' : ((2 / 3 * gamma : k) • c).natDegree ≤ 5 * n - g :=
    (natDegree_smul_le _ _).trans (hc.trans (by omega))
  have hB' : ((1 / 2 * delta : k) • B).natDegree ≤ 5 * n - g :=
    (natDegree_smul_le _ _).trans (hB.trans (by omega))
  have hA' : ((1 / 3 * epsilon : k) • A).natDegree ≤ 5 * n - g :=
    (natDegree_smul_le _ _).trans (hA.trans (by omega))
  have hC : (C eta).natDegree ≤ 5 * n - g := by
    rw [natDegree_C]
    exact Nat.zero_le _
  simp only [cubicLoadVAlphaLowPolynomial68]
  refine (natDegree_add_le _ _).trans (max_le ?_ hC)
  refine (natDegree_add_le _ _).trans (max_le ?_ hA')
  refine (natDegree_add_le _ _).trans (max_le ?_ hB')
  refine (natDegree_add_le _ _).trans (max_le ?_ hc')
  exact (natDegree_add_le _ _).trans (max_le hAB hD')

set_option maxHeartbeats 4000000 in
theorem cubicLoadRowOneDeepGapRestPolynomial68_degree_lt_cubicFace
    (alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOneDeepGapRestPolynomial68 alpha beta gamma delta
      epsilon zeta eta A B c D e).natDegree < 12 * n - 3 * g - 1 := by
  let Tc := cubicLoadTAlphaCorePolynomial68 alpha A
  let Ur := cubicLoadUAlphaRestPolynomial68 beta gamma delta zeta A B c
  let Vr := cubicLoadVAlphaRestPolynomial68 alpha beta gamma delta epsilon
    eta A B c D e
  let Vlow := cubicLoadVAlphaLowPolynomial68 beta gamma delta epsilon eta
    A B c D
  let C0c := (1 / 3 : k) • A ^ 2
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := (1 / 3 : k) • (A * c) + e
  let E := Ec + Er
  have hg2 : g < 2 * n := deepGap_gap_lt_two_radius n g hn hrel
  have hUr : Ur.natDegree ≤ 4 * n :=
    cubicLoadUAlphaRestPolynomial68_degree_le beta gamma delta zeta
      A B c n g hA hB hc
  have hVr : Vr.natDegree ≤ 6 * n - g :=
    cubicLoadVAlphaRestPolynomial68_degree_le_of_two_mul_gap_lt_three
      alpha beta gamma delta epsilon eta A B c D e n g
      hn hrel hA hB hc hD he
  have hVlow : Vlow.natDegree ≤ 5 * n - g :=
    cubicLoadVAlphaLowPolynomial68_degree_le beta gamma delta epsilon eta
      A B c D n g hn hrel hA hB hc hD
  have hC0c : C0c.natDegree ≤ 4 * n := by
    simp only [C0c]
    compute_degree
    omega
  have hEc : Ec.natDegree ≤ 6 * n := by
    simp only [Ec]
    compute_degree
    omega
  have hEr : Er.natDegree ≤ 6 * n - g := by
    simp only [Er]
    compute_degree
    omega
  have hE : E.natDegree ≤ 6 * n :=
    (natDegree_add_le Ec Er).trans (max_le hEc (hEr.trans (by omega)))
  have hTrβ : (((5 / 6 * beta : k) • B + C epsilon)).natDegree ≤
      3 * n - g := by
    compute_degree
    omega
  have hbound (u v : ℕ) (hv : 0 < v)
      (hu : u + v - 1 < 12 * n - 3 * g - 1) :
      ∀ p q : k[X], p.natDegree ≤ u → q.natDegree ≤ v →
        (p * derivative q).natDegree < 12 * n - 3 * g - 1 :=
    fun p q hp hq =>
      deepGap_natDegree_mul_derivative_lt68 p q u v
        (12 * n - 3 * g - 1) hv hp hq hu
  have h1 : (Ur * derivative D).natDegree < 12 * n - 3 * g - 1 :=
    hbound (4 * n) (5 * n - g) (by omega) (by omega) Ur D hUr hD
  have h2 : ((alpha • c) * derivative Er).natDegree <
      12 * n - 3 * g - 1 :=
    hbound (4 * n - g) (6 * n - g) (by omega) (by omega)
      (alpha • c) Er ((natDegree_smul_le alpha c).trans hc) hEr
  have h3 : (((2 / 3 * gamma : k) • A) * derivative Er).natDegree <
      12 * n - 3 * g - 1 :=
    hbound (2 * n) (6 * n - g) (by omega) (by omega)
      ((2 / 3 * gamma : k) • A) Er
      ((natDegree_smul_le _ A).trans hA) hEr
  have h4 : (((5 / 6 * beta : k) • B + C epsilon) * derivative E).natDegree <
      12 * n - 3 * g - 1 :=
    hbound (3 * n - g) (6 * n) (by omega) (by omega)
      ((5 / 6 * beta : k) • B + C epsilon) E hTrβ hE
  have h5 : (C0c * derivative Vlow).natDegree < 12 * n - 3 * g - 1 :=
    hbound (4 * n) (5 * n - g) (by omega) (by omega) C0c Vlow hC0c hVlow
  have h6 : (c * derivative Vr).natDegree < 12 * n - 3 * g - 1 :=
    hbound (4 * n - g) (6 * n - g) (by omega) (by omega) c Vr hc hVr
  have h7 : (D * derivative Ur).natDegree < 12 * n - 3 * g - 1 :=
    hbound (5 * n - g) (4 * n) (by omega) (by omega) D Ur hD hUr
  have h2s := deepGap_natDegree_smul_lt68 (2 : k) h2
  have h3s := deepGap_natDegree_smul_lt68 (2 : k) h3
  have h4s := deepGap_natDegree_smul_lt68 (2 : k) h4
  have h5s := deepGap_natDegree_smul_lt68 (2 : k) h5
  have h6s := deepGap_natDegree_smul_lt68 (2 : k) h6
  change (Ur * derivative D +
      (2 : k) • ((alpha • c) * derivative Er) +
      (2 : k) • (((2 / 3 * gamma : k) • A) * derivative Er) +
      (2 : k) • (((5 / 6 * beta : k) • B + C epsilon) * derivative E) -
      (2 : k) • (C0c * derivative Vlow) -
      (2 : k) • (c * derivative Vr) -
      D * derivative Ur).natDegree < _
  exact deepGap_natDegree_sub_lt
    (deepGap_natDegree_sub_lt
      (deepGap_natDegree_sub_lt
        (deepGap_natDegree_add_lt
          (deepGap_natDegree_add_lt
            (deepGap_natDegree_add_lt h1 h2s) h3s) h4s) h5s) h6s) h7

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_firstDeep
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hl : l = 0) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowOnePolynomial68 l alpha beta gamma delta epsilon zeta eta
      A B c D e).natDegree < 12 * n - 3 * g - 1 := by
  rw [cubicLoadRowOnePolynomial68_eq_alphaRest l alpha beta gamma delta
    epsilon zeta eta A B c D e hl,
    cubicLoadRowOneAlphaRestPolynomial68_eq_deepGapRest']
  exact cubicLoadRowOneDeepGapRestPolynomial68_degree_lt_cubicFace
    alpha beta gamma delta epsilon zeta eta A B c D e n g
    hn hg hrel hA hB hc hD he

/-! ## Row-zero after `beta = 0` -/

set_option maxHeartbeats 4000000 in
theorem cubicLoadRowZeroAlphaDCore_eq_zero (alpha : k) (A D : k[X]) :
    cubicLoadUAlphaCorePolynomial68 alpha D *
        derivative ((1 / 27 : k) • A ^ 3) -
      D * derivative (cubicLoadVAlphaCorePolynomial68 alpha A) = 0 := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadUAlphaCorePolynomial68, cubicLoadVAlphaCorePolynomial68,
    derivative_smul, derivative_mul, derivative_pow, derivative_C,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_zero,
    RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_natCast, map_one]
  ring

def cubicLoadRowZeroDeepGapRestPolynomial68
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) : k[X] :=
  let Uc := cubicLoadUAlphaCorePolynomial68 alpha D
  let Ur := cubicLoadUAlphaRestPolynomial68 0 gamma delta zeta A B c
  let Vr := cubicLoadVAlphaRestPolynomial68 alpha 0 gamma delta epsilon
    eta A B c D e
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := (1 / 3 : k) • (A * c) + e
  let E := Ec + Er
  Ur * derivative E + Uc * derivative Er - D * derivative Vr

set_option maxHeartbeats 4000000 in
theorem cubicLoadRowZeroPolynomial68_eq_deepGapRest_of_beta
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) :
    cubicLoadRowZeroPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
        A B c D e =
      cubicLoadRowZeroDeepGapRestPolynomial68 alpha gamma delta epsilon
          zeta eta A B c D e +
        (cubicLoadUAlphaCorePolynomial68 alpha D *
            derivative ((1 / 27 : k) • A ^ 3) -
          D * derivative (cubicLoadVAlphaCorePolynomial68 alpha A)) := by
  have hU := cubicLoadUPolynomial68_eq_alphaCore_add_rest
    0 alpha 0 gamma delta zeta A B c D e rfl
  have hV := cubicLoadVPolynomial68_eq_alphaCore_add_rest
    0 alpha 0 gamma delta epsilon eta A B c D e rfl
  unfold cubicLoadRowZeroPolynomial68 cubicLoadRowZeroDeepGapRestPolynomial68
  rw [hU, hV]
  simp only [derivative_add]
  ring

theorem cubicLoadRowZeroPolynomial68_eq_deepGapRest_of_beta'
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) :
    cubicLoadRowZeroPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
        A B c D e =
      cubicLoadRowZeroDeepGapRestPolynomial68 alpha gamma delta epsilon
        zeta eta A B c D e := by
  rw [cubicLoadRowZeroPolynomial68_eq_deepGapRest_of_beta,
    cubicLoadRowZeroAlphaDCore_eq_zero, add_zero]

set_option maxHeartbeats 4000000 in
theorem cubicLoadUAlphaRestPolynomial68_degree_le_of_beta
    (gamma delta zeta : k) (A B c : k[X]) (n g : ℕ)
    (hgt : n < g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g) :
    (cubicLoadUAlphaRestPolynomial68 0 gamma delta zeta A B c).natDegree ≤
      2 * n := by
  have h0A : ((5 / 24 * (0 : k) : k) • A ^ 2).natDegree ≤ 2 * n := by
    simp [mul_zero, zero_smul, natDegree_zero]
  have h0c : ((5 / 6 * (0 : k) : k) • c).natDegree ≤ 2 * n := by
    simp [mul_zero, zero_smul, natDegree_zero]
  have hB' : ((2 / 3 * gamma : k) • B).natDegree ≤ 2 * n :=
    (natDegree_smul_le _ _).trans (hB.trans (by omega))
  have hA' : ((1 / 2 * delta : k) • A).natDegree ≤ 2 * n :=
    (natDegree_smul_le _ _).trans hA
  have hC : (C zeta).natDegree ≤ 2 * n := by
    rw [natDegree_C]
    exact Nat.zero_le _
  simp only [cubicLoadUAlphaRestPolynomial68]
  refine (natDegree_add_le _ _).trans (max_le ?_ hC)
  refine (natDegree_add_le _ _).trans (max_le ?_ hA')
  refine (natDegree_add_le _ _).trans (max_le ?_ hB')
  exact (natDegree_add_le _ _).trans (max_le h0A h0c)

set_option maxHeartbeats 4000000 in
theorem cubicLoadRowZeroDeepGapRestPolynomial68_degree_lt_double
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgt : n < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicLoadRowZeroDeepGapRestPolynomial68 alpha gamma delta epsilon
      zeta eta A B c D e).natDegree < 13 * n - 3 * g - 1 := by
  let Uc := cubicLoadUAlphaCorePolynomial68 alpha D
  let Ur := cubicLoadUAlphaRestPolynomial68 0 gamma delta zeta A B c
  let Vr := cubicLoadVAlphaRestPolynomial68 alpha 0 gamma delta epsilon
    eta A B c D e
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := (1 / 3 : k) • (A * c) + e
  let E := Ec + Er
  have hg2 : g < 2 * n := deepGap_gap_lt_two_radius n g hn hrel
  have he' : e.natDegree ≤ 6 * n - g := he.trans (by omega)
  have hUc : Uc.natDegree ≤ 5 * n - g := by
    simp only [Uc, cubicLoadUAlphaCorePolynomial68]
    exact (natDegree_smul_le alpha D).trans hD
  have hUr : Ur.natDegree ≤ 2 * n :=
    cubicLoadUAlphaRestPolynomial68_degree_le_of_beta gamma delta zeta
      A B c n g hgt hA hB hc
  have hVr : Vr.natDegree ≤ 6 * n - g :=
    cubicLoadVAlphaRestPolynomial68_degree_le_of_two_mul_gap_lt_three
      alpha 0 gamma delta epsilon eta A B c D e n g
      hn hrel hA hB hc hD he'
  have hEc : Ec.natDegree ≤ 6 * n := by
    simp only [Ec]
    compute_degree
    omega
  have hEr : Er.natDegree ≤ 6 * n - g := by
    simp only [Er]
    compute_degree
    omega
  have hE : E.natDegree ≤ 6 * n :=
    (natDegree_add_le Ec Er).trans (max_le hEc (hEr.trans (by omega)))
  have hbound (u v : ℕ) (hv : 0 < v)
      (hu : u + v - 1 < 13 * n - 3 * g - 1) :
      ∀ p q : k[X], p.natDegree ≤ u → q.natDegree ≤ v →
        (p * derivative q).natDegree < 13 * n - 3 * g - 1 :=
    fun p q hp hq =>
      deepGap_natDegree_mul_derivative_lt68 p q u v
        (13 * n - 3 * g - 1) hv hp hq hu
  have h1 : (Ur * derivative E).natDegree < 13 * n - 3 * g - 1 :=
    hbound (2 * n) (6 * n) (by omega) (by omega) Ur E hUr hE
  have h2 : (Uc * derivative Er).natDegree < 13 * n - 3 * g - 1 :=
    hbound (5 * n - g) (6 * n - g) (by omega) (by omega) Uc Er hUc hEr
  have h3 : (D * derivative Vr).natDegree < 13 * n - 3 * g - 1 :=
    hbound (5 * n - g) (6 * n - g) (by omega) (by omega) D Vr hD hVr
  change (Ur * derivative E + Uc * derivative Er -
      D * derivative Vr).natDegree < _
  exact deepGap_natDegree_sub_lt (deepGap_natDegree_add_lt h1 h2) h3

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowZeroPolynomial68_degree_lt_double_of_firstDeep_beta
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgt : n < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
      A B c D e).natDegree < 13 * n - 3 * g - 1 := by
  rw [cubicLoadRowZeroPolynomial68_eq_deepGapRest_of_beta']
  exact cubicLoadRowZeroDeepGapRestPolynomial68_degree_lt_double
    alpha gamma delta epsilon zeta eta A B c D e n g
    hn hg hgt hrel hA hB hc hD he

/-! ## Row-two alpha cores after `beta = 0` -/

def cubicLoadSAlphaCorePolynomial68 (alpha : k) (B : k[X]) : k[X] :=
  alpha • B

theorem cubicLoadSPolynomial68_eq_alphaCore_add_rest
    (l alpha beta delta : k) (A B c : k[X]) (hl : l = 0) :
    cubicLoadSPolynomial68 l alpha beta delta A B c =
      cubicLoadSAlphaCorePolynomial68 alpha B +
        ((5 / 6 * beta : k) • A + C delta) := by
  simp [cubicLoadSPolynomial68, cubicLoadSAlphaCorePolynomial68, hl,
    mul_zero, zero_smul, add_zero]
  abel

theorem cubicLoadSPolynomial68_eq_alphaCore_of_l_beta
    (alpha delta : k) (A B c : k[X]) :
    cubicLoadSPolynomial68 0 alpha 0 delta A B c =
      cubicLoadSAlphaCorePolynomial68 alpha B + C delta := by
  simp [cubicLoadSPolynomial68, cubicLoadSAlphaCorePolynomial68,
    mul_zero, zero_smul, add_zero]

set_option maxHeartbeats 4000000 in
theorem cubicLoadRowTwoAlphaC0DCore_eq_zero (alpha : k) (A D : k[X]) :
    cubicLoadUAlphaCorePolynomial68 alpha D *
        derivative ((1 / 3 : k) • A ^ 2) +
      (2 : k) • (cubicLoadTAlphaCorePolynomial68 alpha A * derivative D) -
      (2 : k) • (((1 / 3 : k) • A ^ 2) *
        derivative (cubicLoadUAlphaCorePolynomial68 alpha D)) -
      D * derivative (cubicLoadTAlphaCorePolynomial68 alpha A) = 0 := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadUAlphaCorePolynomial68, cubicLoadTAlphaCorePolynomial68,
    derivative_smul, derivative_mul, derivative_pow, derivative_C,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_zero,
    RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 4000000 in
theorem cubicLoadRowTwoAlphaBECore_eq_zero (alpha : k) (A B : k[X]) :
    (3 : k) • (cubicLoadSAlphaCorePolynomial68 alpha B *
        derivative ((1 / 27 : k) • A ^ 3)) -
      (3 : k) • (B * derivative (cubicLoadVAlphaCorePolynomial68 alpha A)) =
        0 := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadSAlphaCorePolynomial68, cubicLoadVAlphaCorePolynomial68,
    derivative_smul, derivative_mul, derivative_pow, derivative_C,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_zero,
    RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_natCast, map_one]
  ring

def cubicLoadRowTwoDeepGapRestPolynomial68
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) : k[X] :=
  let Uc := cubicLoadUAlphaCorePolynomial68 alpha D
  let Ur := cubicLoadUAlphaRestPolynomial68 0 gamma delta zeta A B c
  let Tc := cubicLoadTAlphaCorePolynomial68 alpha A
  let Tr := cubicLoadTAlphaRestPolynomial68 alpha 0 gamma epsilon A B c
  let Sc := cubicLoadSAlphaCorePolynomial68 alpha B
  let Sr := C delta
  let Vc := cubicLoadVAlphaCorePolynomial68 alpha A
  let Vr := cubicLoadVAlphaRestPolynomial68 alpha 0 gamma delta epsilon
    eta A B c D e
  let C0c := (1 / 3 : k) • A ^ 2
  let C0 := C0c + c
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := (1 / 3 : k) • (A * c) + e
  let E := Ec + Er
  let U := Uc + Ur
  Ur * derivative C0 + Uc * derivative c +
    (2 : k) • (Tr * derivative D) +
    (3 : k) • (Sr * derivative E) +
    (3 : k) • (Sc * derivative Er) -
    (3 : k) • (B * derivative Vr) -
    (2 : k) • (c * derivative U) -
    (2 : k) • (C0c * derivative Ur) -
    D * derivative Tr

set_option maxHeartbeats 8000000 in
theorem cubicLoadRowTwoPolynomial68_eq_deepGapRest_of_beta
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) :
    cubicLoadRowTwoPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
        A B c D e =
      cubicLoadRowTwoDeepGapRestPolynomial68 alpha gamma delta epsilon
          zeta eta A B c D e +
        (cubicLoadUAlphaCorePolynomial68 alpha D *
            derivative ((1 / 3 : k) • A ^ 2) +
          (2 : k) • (cubicLoadTAlphaCorePolynomial68 alpha A * derivative D) -
          (2 : k) • (((1 / 3 : k) • A ^ 2) *
            derivative (cubicLoadUAlphaCorePolynomial68 alpha D)) -
          D * derivative (cubicLoadTAlphaCorePolynomial68 alpha A)) +
        ((3 : k) • (cubicLoadSAlphaCorePolynomial68 alpha B *
            derivative ((1 / 27 : k) • A ^ 3)) -
          (3 : k) • (B * derivative
            (cubicLoadVAlphaCorePolynomial68 alpha A))) := by
  have hS := cubicLoadSPolynomial68_eq_alphaCore_of_l_beta alpha delta A B c
  have hT := cubicLoadTPolynomial68_eq_alphaCore_add_rest
    0 alpha 0 gamma epsilon A B c D rfl
  have hU := cubicLoadUPolynomial68_eq_alphaCore_add_rest
    0 alpha 0 gamma delta zeta A B c D e rfl
  have hV := cubicLoadVPolynomial68_eq_alphaCore_add_rest
    0 alpha 0 gamma delta epsilon eta A B c D e rfl
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicLoadRowTwoPolynomial68, cubicLoadRowTwoDeepGapRestPolynomial68,
    hS, hT, hU, hV, cubicLoadSAlphaCorePolynomial68, derivative_add,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_zero,
    RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_natCast, map_one]
  ring

theorem cubicLoadRowTwoPolynomial68_eq_deepGapRest_of_beta'
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) :
    cubicLoadRowTwoPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
        A B c D e =
      cubicLoadRowTwoDeepGapRestPolynomial68 alpha gamma delta epsilon
        zeta eta A B c D e := by
  rw [cubicLoadRowTwoPolynomial68_eq_deepGapRest_of_beta,
    cubicLoadRowTwoAlphaC0DCore_eq_zero, cubicLoadRowTwoAlphaBECore_eq_zero,
    add_zero, add_zero]

set_option maxHeartbeats 6000000 in
theorem cubicLoadRowTwoDeepGapRestPolynomial68_degree_lt_cubicFace
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgt : n < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowTwoDeepGapRestPolynomial68 alpha gamma delta epsilon
      zeta eta A B c D e).natDegree < 11 * n - 3 * g - 1 := by
  let Uc := cubicLoadUAlphaCorePolynomial68 alpha D
  let Ur := cubicLoadUAlphaRestPolynomial68 0 gamma delta zeta A B c
  let Tc := cubicLoadTAlphaCorePolynomial68 alpha A
  let Tr := cubicLoadTAlphaRestPolynomial68 alpha 0 gamma epsilon A B c
  let Sc := cubicLoadSAlphaCorePolynomial68 alpha B
  let Sr := (C delta : k[X])
  let Vr := cubicLoadVAlphaRestPolynomial68 alpha 0 gamma delta epsilon
    eta A B c D e
  let C0c := (1 / 3 : k) • A ^ 2
  let C0 := C0c + c
  let Ec := (1 / 27 : k) • A ^ 3
  let Er := (1 / 3 : k) • (A * c) + e
  let E := Ec + Er
  let U := Uc + Ur
  have hg2 : g < 2 * n := deepGap_gap_lt_two_radius n g hn hrel
  have hUc : Uc.natDegree ≤ 5 * n - g := by
    simp only [Uc, cubicLoadUAlphaCorePolynomial68]
    exact (natDegree_smul_le alpha D).trans hD
  have hUr : Ur.natDegree ≤ 2 * n :=
    cubicLoadUAlphaRestPolynomial68_degree_le_of_beta gamma delta zeta
      A B c n g hgt hA hB hc
  have hTr : Tr.natDegree ≤ 4 * n - g :=
    cubicLoadTAlphaRestPolynomial68_degree_le_of_two_mul_gap_lt_three
      alpha 0 gamma epsilon A B c n g hn hrel hA hB hc
  have hSc : Sc.natDegree ≤ 3 * n - g := by
    simp only [Sc, cubicLoadSAlphaCorePolynomial68]
    exact (natDegree_smul_le alpha B).trans hB
  have hSr : Sr.natDegree ≤ 0 := by
    simp [Sr, natDegree_C]
  have hVr : Vr.natDegree ≤ 6 * n - g :=
    cubicLoadVAlphaRestPolynomial68_degree_le_of_two_mul_gap_lt_three
      alpha 0 gamma delta epsilon eta A B c D e n g
      hn hrel hA hB hc hD he
  have hC0c : C0c.natDegree ≤ 4 * n := by
    simp only [C0c]
    compute_degree
    omega
  have hC0 : C0.natDegree ≤ 4 * n := by
    simp only [C0]
    compute_degree
    omega
  have hU : U.natDegree ≤ 5 * n - g :=
    (natDegree_add_le Uc Ur).trans
      (max_le hUc (hUr.trans (by omega)))
  have hEc : Ec.natDegree ≤ 6 * n := by
    simp only [Ec]
    compute_degree
    omega
  have hEr : Er.natDegree ≤ 6 * n - g := by
    simp only [Er]
    compute_degree
    omega
  have hE : E.natDegree ≤ 6 * n :=
    (natDegree_add_le Ec Er).trans (max_le hEc (hEr.trans (by omega)))
  have hbound (u v : ℕ) (hv : 0 < v)
      (hu : u + v - 1 < 11 * n - 3 * g - 1) :
      ∀ p q : k[X], p.natDegree ≤ u → q.natDegree ≤ v →
        (p * derivative q).natDegree < 11 * n - 3 * g - 1 :=
    fun p q hp hq =>
      deepGap_natDegree_mul_derivative_lt68 p q u v
        (11 * n - 3 * g - 1) hv hp hq hu
  have h1 : (Ur * derivative C0).natDegree < 11 * n - 3 * g - 1 :=
    hbound (2 * n) (4 * n) (by omega) (by omega) Ur C0 hUr hC0
  have h2 : (Uc * derivative c).natDegree < 11 * n - 3 * g - 1 :=
    hbound (5 * n - g) (4 * n - g) (by omega) (by omega) Uc c hUc hc
  have h3 : (Tr * derivative D).natDegree < 11 * n - 3 * g - 1 :=
    hbound (4 * n - g) (5 * n - g) (by omega) (by omega) Tr D hTr hD
  have h4 : (Sr * derivative E).natDegree < 11 * n - 3 * g - 1 :=
    hbound 0 (6 * n) (by omega) (by omega) Sr E hSr hE
  have h5 : (Sc * derivative Er).natDegree < 11 * n - 3 * g - 1 :=
    hbound (3 * n - g) (6 * n - g) (by omega) (by omega) Sc Er hSc hEr
  have h6 : (B * derivative Vr).natDegree < 11 * n - 3 * g - 1 :=
    hbound (3 * n - g) (6 * n - g) (by omega) (by omega) B Vr hB hVr
  have h7 : (c * derivative U).natDegree < 11 * n - 3 * g - 1 :=
    hbound (4 * n - g) (5 * n - g) (by omega) (by omega) c U hc hU
  have h8 : (C0c * derivative Ur).natDegree < 11 * n - 3 * g - 1 :=
    hbound (4 * n) (2 * n) (by omega) (by omega) C0c Ur hC0c hUr
  have h9 : (D * derivative Tr).natDegree < 11 * n - 3 * g - 1 :=
    hbound (5 * n - g) (4 * n - g) (by omega) (by omega) D Tr hD hTr
  have h3s := deepGap_natDegree_smul_lt68 (2 : k) h3
  have h4s := deepGap_natDegree_smul_lt68 (3 : k) h4
  have h5s := deepGap_natDegree_smul_lt68 (3 : k) h5
  have h6s := deepGap_natDegree_smul_lt68 (3 : k) h6
  have h7s := deepGap_natDegree_smul_lt68 (2 : k) h7
  have h8s := deepGap_natDegree_smul_lt68 (2 : k) h8
  change (Ur * derivative C0 + Uc * derivative c +
      (2 : k) • (Tr * derivative D) +
      (3 : k) • (Sr * derivative E) +
      (3 : k) • (Sc * derivative Er) -
      (3 : k) • (B * derivative Vr) -
      (2 : k) • (c * derivative U) -
      (2 : k) • (C0c * derivative Ur) -
      D * derivative Tr).natDegree < _
  exact deepGap_natDegree_sub_lt
    (deepGap_natDegree_sub_lt
      (deepGap_natDegree_sub_lt
        (deepGap_natDegree_sub_lt
          (deepGap_natDegree_add_lt
            (deepGap_natDegree_add_lt
              (deepGap_natDegree_add_lt
                (deepGap_natDegree_add_lt h1 h2) h3s) h4s) h5s) h6s) h7s) h8s) h9

set_option maxHeartbeats 2000000 in
theorem cubicLoadRowTwoPolynomial68_degree_lt_cubicFace_of_firstDeep_beta
    (alpha gamma delta epsilon zeta eta : k)
    (A B c D e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hgt : n < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - g) :
    (cubicLoadRowTwoPolynomial68 0 alpha 0 gamma delta epsilon zeta eta
      A B c D e).natDegree < 11 * n - 3 * g - 1 := by
  rw [cubicLoadRowTwoPolynomial68_eq_deepGapRest_of_beta']
  exact cubicLoadRowTwoDeepGapRestPolynomial68_degree_lt_cubicFace
    alpha gamma delta epsilon zeta eta A B c D e n g
    hn hg hgt hrel hA hB hc hD he

/-! ## Homogeneous double coefficients on `2g < 3n` -/

set_option maxHeartbeats 4000000 in
theorem secondaryResidualRowOnePolynomial68_coeff_double_of_firstDeep
    (A B c d e : k[X]) (n g : ℕ) (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) =
      (8 / 27 : k) *
        (3 * A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) * (g : k) *
            d.coeff (5 * n - 2 * g) -
          10 * A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) * (n : k) *
            d.coeff (5 * n - 2 * g) +
          2 * A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 * (n : k) *
            c.coeff (4 * n - g) -
          9 * A.coeff (2 * n) * (g : k) * c.coeff (4 * n - g) *
            e.coeff (6 * n - 2 * g) +
          30 * A.coeff (2 * n) * (n : k) * c.coeff (4 * n - g) *
            e.coeff (6 * n - 2 * g) +
          3 * (g : k) * c.coeff (4 * n - g) ^ 3 -
          12 * (n : k) * c.coeff (4 * n - g) ^ 3) := by
  have hA2deg : (A ^ 2).natDegree ≤ 4 * n := by
    compute_degree
    omega
  have hB2deg : (B ^ 2).natDegree ≤ 6 * n - 2 * g := by
    compute_degree
    omega
  have hc2deg : (c ^ 2).natDegree ≤ 8 * n - 2 * g := by
    compute_degree
    omega
  have hA2 : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_at_bound68 A (2 * n) 2 hA
    have hi : 2 * (2 * n) = 4 * n := by omega
    simpa only [hi] using h
  have hB2 : (B ^ 2).coeff (6 * n - 2 * g) =
      B.coeff (3 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 B (3 * n - g) 2 hB
    have hi : 2 * (3 * n - g) = 6 * n - 2 * g := by omega
    simpa only [hi] using h
  have hc2 : (c ^ 2).coeff (8 * n - 2 * g) =
      c.coeff (4 * n - g) ^ 2 := by
    have h := coeff_pow_at_bound68 c (4 * n - g) 2 hc
    have hi : 2 * (4 * n - g) = 8 * n - 2 * g := by omega
    simpa only [hi] using h
  have h1 := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) B d
    (4 * n) (3 * n - g) (5 * n - 2 * g) (by omega)
    hA2deg hB hd
  have hi1 : 4 * n + (3 * n - g) + (5 * n - 2 * g) - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi1, hA2] at h1
  have h2 := coeff_mul_mul_derivative_at_bounds68 (A ^ 2) d B
    (4 * n) (5 * n - 2 * g) (3 * n - g) (by omega)
    hA2deg hd hB
  have hi2 : 4 * n + (5 * n - 2 * g) + (3 * n - g) - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi2, hA2] at h2
  have h2' : (A ^ 2 * derivative B * d).coeff
      (12 * n - 3 * g - 1) =
      A.coeff (2 * n) ^ 2 * B.coeff (3 * n - g) *
        d.coeff (5 * n - 2 * g) * ((3 * n - g : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2
  have h3 := coeff_mul_mul_mul_derivative_at_bounds68 A B d A
    (2 * n) (3 * n - g) (5 * n - 2 * g) (2 * n) (by omega)
    hA hB hd hA
  have hi3 : 2 * n + (3 * n - g) + (5 * n - 2 * g) + 2 * n - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi3] at h3
  have h3' : (A * derivative A * B * d).coeff
      (12 * n - 3 * g - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) * B.coeff (3 * n - g) *
        d.coeff (5 * n - 2 * g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h3
  have h4 := coeff_mul_mul_derivative_at_bounds68 A c e
    (2 * n) (4 * n - g) (6 * n - 2 * g) (by omega) hA hc he
  have hi4 : 2 * n + (4 * n - g) + (6 * n - 2 * g) - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi4] at h4
  have h5 := coeff_mul_mul_derivative_at_bounds68 A e c
    (2 * n) (6 * n - 2 * g) (4 * n - g) (by omega) hA he hc
  have hi5 : 2 * n + (6 * n - 2 * g) + (4 * n - g) - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi5] at h5
  have h5' : (A * derivative c * e).coeff (12 * n - 3 * g - 1) =
      A.coeff (2 * n) * c.coeff (4 * n - g) *
        e.coeff (6 * n - 2 * g) * ((4 * n - g : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h5
  have h6 := coeff_mul_mul_derivative_at_bounds68 (B ^ 2) c A
    (6 * n - 2 * g) (4 * n - g) (2 * n) (by omega)
    hB2deg hc hA
  have hi6 : (6 * n - 2 * g) + (4 * n - g) + 2 * n - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi6, hB2] at h6
  have h6' : (derivative A * B ^ 2 * c).coeff
      (12 * n - 3 * g - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 *
        c.coeff (4 * n - g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h6
  have h7 := coeff_mul_derivative_at_bounds68 (c ^ 2) c
    (8 * n - 2 * g) (4 * n - g) (by omega) hc2deg hc
  have hi7 : (8 * n - 2 * g) + (4 * n - g) - 1 =
      12 * n - 3 * g - 1 := by omega
  rw [hi7, hc2] at h7
  have hlowA : (derivative A * d ^ 2).natDegree <
      12 * n - 3 * g - 1 := by compute_degree; omega
  have hlowB : (B ^ 2 * derivative e).natDegree <
      12 * n - 3 * g - 1 := by compute_degree; omega
  have hlowC : (B * c * derivative d).natDegree <
      12 * n - 3 * g - 1 := by compute_degree; omega
  have hlowD : (B * derivative c * d).natDegree <
      12 * n - 3 * g - 1 := by compute_degree; omega
  have hlowE : (derivative B * c * d).natDegree <
      12 * n - 3 * g - 1 := by compute_degree; omega
  have hlowF : (e * derivative e).natDegree <
      12 * n - 3 * g - 1 := by compute_degree; omega
  have hcast3 : (((3 * n - g : ℕ) : k)) = 3 * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 3 * n)]
    push_cast
    rfl
  have hcast4 : (((4 * n - g : ℕ) : k)) = 4 * (n : k) - (g : k) := by
    rw [Nat.cast_sub (by omega : g ≤ 4 * n)]
    push_cast
    rfl
  have hcast5 : (((5 * n - 2 * g : ℕ) : k)) =
      5 * (n : k) - 2 * (g : k) := by
    rw [Nat.cast_sub (by omega : 2 * g ≤ 5 * n)]
    push_cast
    rfl
  have hcast6 : (((6 * n - 2 * g : ℕ) : k)) =
      6 * (n : k) - 2 * (g : k) := by
    rw [Nat.cast_sub (by omega : 2 * g ≤ 6 * n)]
    push_cast
    rfl
  simp only [secondaryResidualRowOnePolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1, h2', h3', h4, h5', h6', h7,
    coeff_eq_zero_of_natDegree_lt hlowA,
    coeff_eq_zero_of_natDegree_lt hlowB,
    coeff_eq_zero_of_natDegree_lt hlowC,
    coeff_eq_zero_of_natDegree_lt hlowD,
    coeff_eq_zero_of_natDegree_lt hlowE,
    coeff_eq_zero_of_natDegree_lt hlowF, smul_eq_mul]
  rw [hcast3, hcast4, hcast5, hcast6]
  push_cast
  ring

set_option maxHeartbeats 3000000 in
theorem secondaryResidualRowZeroPolynomial68_coeff_double_of_firstDeep
    (A B c d e : k[X]) (n g : ℕ) (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff
        (13 * n - 3 * g - 1) =
      (8 / 27 : k) * (n : k) * A.coeff (2 * n) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            e.coeff (6 * n - 2 * g)) -
          A.coeff (2 * n) * c.coeff (4 * n - g) *
            d.coeff (5 * n - 2 * g) +
          B.coeff (3 * n - g) * c.coeff (4 * n - g) ^ 2) := by
  have h1 := coeff_mul_mul_mul_derivative_at_bounds68 A B e A
    (2 * n) (3 * n - g) (6 * n - 2 * g) (2 * n) (by omega)
    hA hB he hA
  have hi1 : 2 * n + (3 * n - g) + (6 * n - 2 * g) + 2 * n - 1 =
      13 * n - 3 * g - 1 := by omega
  rw [hi1] at h1
  have h1' : (A * derivative A * B * e).coeff (13 * n - 3 * g - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) * B.coeff (3 * n - g) *
        e.coeff (6 * n - 2 * g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h1
  have h2 := coeff_mul_mul_mul_derivative_at_bounds68 A c d A
    (2 * n) (4 * n - g) (5 * n - 2 * g) (2 * n) (by omega)
    hA hc hd hA
  have hi2 : 2 * n + (4 * n - g) + (5 * n - 2 * g) + 2 * n - 1 =
      13 * n - 3 * g - 1 := by omega
  rw [hi2] at h2
  have h2' : (A * derivative A * c * d).coeff (13 * n - 3 * g - 1) =
      A.coeff (2 * n) * A.coeff (2 * n) * c.coeff (4 * n - g) *
        d.coeff (5 * n - 2 * g) * ((2 * n : ℕ) : k) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h2
  have h3 := coeff_mul_mul_mul_derivative_at_bounds68 B c c A
    (3 * n - g) (4 * n - g) (4 * n - g) (2 * n) (by omega)
    hB hc hc hA
  have hi3 : (3 * n - g) + (4 * n - g) + (4 * n - g) + 2 * n - 1 =
      13 * n - 3 * g - 1 := by omega
  rw [hi3] at h3
  have h3' : (derivative A * B * c ^ 2).coeff (13 * n - 3 * g - 1) =
      A.coeff (2 * n) * B.coeff (3 * n - g) *
        c.coeff (4 * n - g) ^ 2 * ((2 * n : ℕ) : k) := by
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using h3
  have hlow1 : (A * B ^ 2 * derivative d).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow2 : (A * B * derivative B * d).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow3 : (derivative A * d * e).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow4 : (B * c * derivative e).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow5 : (B * d * derivative d).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow6 : (derivative B * d ^ 2).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  have hlow7 : (c * derivative c * d).natDegree <
      13 * n - 3 * g - 1 := by compute_degree; omega
  simp only [secondaryResidualRowZeroPolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1', h2', h3',
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow7, smul_eq_mul]
  push_cast
  ring

theorem secondaryResidualRowOnePolynomial68_coeff_doubleFibre_of_firstDeep
    (A B c d e : k[X]) (n g : ℕ) (hg : 0 < g) (hrel : 2 * g < 3 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g)
    (hb0 : B.coeff (3 * n - g) = 0)
    (hd0 : d.coeff (5 * n - 2 * g) = 0)
    (he0 : e.coeff (6 * n - 2 * g) = 0) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff
        (12 * n - 3 * g - 1) =
      (8 / 27 : k) * (3 * (g : k) - 12 * (n : k)) *
        c.coeff (4 * n - g) ^ 3 := by
  rw [secondaryResidualRowOnePolynomial68_coeff_double_of_firstDeep A B c d e
    n g hg hrel hA hB hc hd he, hb0, hd0, he0]
  ring

/-! ## Double face extraction -/

set_option maxHeartbeats 4000000 in
theorem polynomialSecondaryResidualDoubleFace68_of_firstDeep
    (alpha gamma delta epsilon zeta eta i4 i3 : k)
    (A B c d e : k[X]) (n g : ℕ)
    (hn : 0 < n) (hg : 0 < g) (hrel : 2 * g < 3 * n) (hg_gt : n < g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - 2 * g)
    (he : e.natDegree ≤ 6 * n - 2 * g)
    (ha : A.coeff (2 * n) ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68
      0 0 gamma delta epsilon zeta A B c
        ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrowOne :
      let C0 := (1 / 3 : k) • A ^ 2 + c
      let D0 := (1 / 3 : k) • (A * B) + d
      let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
      lowerRowOnePolynomial68
        (integratedTPolynomial68 0 alpha 0 gamma epsilon A B C0 D0 E0)
        (integratedUPolynomial68 0 alpha 0 gamma delta zeta A B C0 D0 E0)
        (integratedVPolynomial68 0 alpha 0 gamma delta epsilon eta
          A B C0 D0 E0) C0 D0 E0 = 0)
    (hrowZero :
      let C0 := (1 / 3 : k) • A ^ 2 + c
      let D0 := (1 / 3 : k) • (A * B) + d
      let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
      (lowerRowZeroPolynomial68
        (integratedUPolynomial68 0 alpha 0 gamma delta zeta A B C0 D0 E0)
        (integratedVPolynomial68 0 alpha 0 gamma delta epsilon eta
          A B C0 D0 E0) D0 E0).coeff (13 * n - 3 * g - 1) = 0) :
    SecondaryResidualTiedDoubleFace68 (n : k) (g : k)
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
      (e.coeff (6 * n - 2 * g)) := by
  let C0 := (1 / 3 : k) • A ^ 2 + c
  let D0 := (1 / 3 : k) • (A * B) + d
  let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  change lowerRowOnePolynomial68
    (integratedTPolynomial68 0 alpha 0 gamma epsilon A B C0 D0 E0)
    (integratedUPolynomial68 0 alpha 0 gamma delta zeta A B C0 D0 E0)
    (integratedVPolynomial68 0 alpha 0 gamma delta epsilon eta
      A B C0 D0 E0) C0 D0 E0 = 0 at hrowOne
  change (lowerRowZeroPolynomial68
    (integratedUPolynomial68 0 alpha 0 gamma delta zeta A B C0 D0 E0)
    (integratedVPolynomial68 0 alpha 0 gamma delta epsilon eta
      A B C0 D0 E0) D0 E0).coeff (13 * n - 3 * g - 1) = 0 at hrowZero
  have hD : D0.natDegree ≤ 5 * n - g := by
    simp only [D0]
    compute_degree
    omega
  have he' : e.natDegree ≤ 6 * n - g := he.trans (by omega)
  have hfour :
      -(B.coeff (3 * n - g) ^ 3) +
          9 * B.coeff (3 * n - g) * e.coeff (6 * n - 2 * g) +
          9 * c.coeff (4 * n - g) * d.coeff (5 * n - 2 * g) = 0 := by
    have hz := congrArg (fun p : k[X] => p.coeff (9 * n - 3 * g)) hi4
    rw [cubicFirstIntegralFourPolynomial68_coeff_residualDouble_of_l_beta
      gamma delta epsilon zeta A B c d e n g hg hrel
      hA hB hc hd he] at hz
    have hidx : 9 * n - 3 * g ≠ 0 := by omega
    simp only [coeff_C, if_neg hidx] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  have hthree :
      -(A.coeff (2 * n) * B.coeff (3 * n - g) *
          d.coeff (5 * n - 2 * g)) -
        B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g) +
        3 * c.coeff (4 * n - g) * e.coeff (6 * n - 2 * g) = 0 := by
    have hz := congrArg (fun p : k[X] => p.coeff (10 * n - 3 * g)) hi3
    rw [cubicFirstIntegralThreePolynomial68_coeff_residualDouble_of_deepGap
      0 gamma delta epsilon zeta A B c d e n g hg hrel
      hA hB hc hd he] at hz
    have hindex : 10 * n - 3 * g ≠ 0 := by omega
    simp only [coeff_C, if_neg hindex] at hz
    have hzero := (mul_eq_zero.mp hz).resolve_left (by norm_num)
    linear_combination hzero
  have hcoords := integratedPolynomial68_cubicCoordinates
    0 alpha 0 gamma delta epsilon zeta eta A B c D0 e
  have hone := congrArg
    (fun p : k[X] => p.coeff (12 * n - 3 * g - 1)) hrowOne
  rw [hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowOnePolynomial68_split, coeff_add,
    show cubicHomogeneousRowOnePolynomial68 A B c D0 e =
        secondaryResidualRowOnePolynomial68 A B c d e by
      simpa only [D0] using
        cubicHomogeneousRowOnePolynomial68_residualCoordinates A B c d e,
    secondaryResidualRowOnePolynomial68_coeff_double_of_firstDeep A B c d e n g
      hg hrel hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_firstDeep
        0 alpha 0 gamma delta epsilon zeta eta A B c D0 e n g
        hn hg rfl hrel hA hB hc hD he'), add_zero, coeff_zero] at hone
  have hone0 := (mul_eq_zero.mp hone).resolve_left (by norm_num)
  rw [hcoords.u_eq, hcoords.v_eq, cubicRowZeroPolynomial68_split,
    coeff_add,
    show cubicHomogeneousRowZeroPolynomial68 A B c D0 e =
        secondaryResidualRowZeroPolynomial68 A B c d e by
      simpa only [D0] using
        cubicHomogeneousRowZeroPolynomial68_residualCoordinates A B c d e,
    secondaryResidualRowZeroPolynomial68_coeff_double_of_firstDeep A B c d e n g
      hg hrel hA hB hc hd he,
    coeff_eq_zero_of_natDegree_lt
      (cubicLoadRowZeroPolynomial68_degree_lt_double_of_firstDeep_beta
        alpha gamma delta epsilon zeta eta A B c D0 e n g
        hn hg hg_gt hrel hA hB hc hD he), add_zero] at hrowZero
  have hncast : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hfactor : (8 / 27 : k) * (n : k) * A.coeff (2 * n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hncast) ha
  have hzero0 := (mul_eq_zero.mp hrowZero).resolve_left hfactor
  exact ⟨hfour, by linear_combination hthree,
    by linear_combination hzero0, by linear_combination hone0⟩

/-! ## Double fibre and tied-face contradictions -/

theorem secondaryResidualDoubleFibre68_impossible_of_firstDeep
    (n g : ℕ) (a b c d e : k) (hc : c ≠ 0)
    (hchamber : n < g ∧ 2 * g < 3 * n)
    (hb : b = 0) (hd : d = 0) (he : e = 0)
    (hface : SecondaryResidualTiedDoubleFace68
      (n : k) (g : k) a b c d e) : False := by
  have hone := hface.one
  rw [hb, hd, he] at hone
  have hcoeff : (3 * (g : k) - 12 * (n : k)) ≠ 0 := by
    intro hz
    have hcast : (3 * g : k) = (12 * n : ℕ) := by
      push_cast
      linear_combination hz
    have hnat : 3 * g = 12 * n := by exact_mod_cast hcast
    omega
  have hc3 : c ^ 3 = 0 := by
    have hprod : (3 * (g : k) - 12 * (n : k)) * c ^ 3 = 0 := by
      linear_combination hone
    exact (mul_eq_zero.mp hprod).resolve_left hcoeff
  exact (pow_ne_zero 3 hc) hc3

theorem secondaryResidualTiedDoubleFace68_impossible_of_firstDeep
    (n g : ℕ) (a b c d e : k) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hchamber : n < g ∧ 2 * g < 3 * n)
    (hface : SecondaryResidualTiedDoubleFace68
      (n : k) (g : k) a b c d e) : False := by
  have hcast := secondaryResidualTiedDoubleFace68_forces_gap_eq_four_radius
    (n : k) (g : k) a b c d e ha hb hc hface
  have hnat : g = 4 * n := by exact_mod_cast hcast
  omega

theorem secondaryResidualDoubleFace68_impossible_of_firstDeep
    (n g : ℕ) (a b c d e : k)
    (ha : a ≠ 0) (hsupport : b ≠ 0 ∨ c ≠ 0)
    (hchamber : n < g ∧ 2 * g < 3 * n)
    (hface : SecondaryResidualTiedDoubleFace68
      (n : k) (g : k) a b c d e) : False := by
  have hb : b ≠ 0 := by
    rcases hsupport with hb | hc
    · exact hb
    · intro hb0
      have hd0 : d = 0 := by
        have h := hface.four
        rw [hb0] at h
        have hcd : c * d = 0 := by linear_combination (1 / 9 : k) * h
        exact (mul_eq_zero.mp hcd).resolve_left hc
      have he0 : e = 0 := by
        have h := hface.three
        rw [hb0] at h
        have hce : c * e = 0 := by linear_combination (1 / 3 : k) * h
        exact (mul_eq_zero.mp hce).resolve_left hc
      exact secondaryResidualDoubleFibre68_impossible_of_firstDeep
        n g a b c d e hc hchamber hb0 hd0 he0 hface
  have hc : c ≠ 0 := by
    rcases hsupport with hb' | hc
    · intro hc0
      have hd0 : d = 0 := by
        have h := hface.three
        rw [hc0] at h
        have hab : a * b ≠ 0 := mul_ne_zero ha hb'
        have habd : a * b * d = 0 := by linear_combination -h
        exact (mul_eq_zero.mp habd).resolve_left hab
      have he0 : e = 0 := by
        have h := hface.zero
        rw [hc0] at h
        have hab : a * b ≠ 0 := mul_ne_zero ha hb'
        have habe : a * b * e = 0 := by linear_combination -h
        exact (mul_eq_zero.mp habe).resolve_left hab
      have h := hface.four
      rw [hc0, hd0, he0] at h
      have hb3 : b ^ 3 = 0 := by linear_combination -h
      exact (pow_ne_zero 3 hb') hb3
    · exact hc
  by_cases hd : d = 0
  · exact secondaryResidualEAtDoubleFace68_impossible b c e hb hc
      (secondaryResidualEAtDoubleFace68_of_tied
        (n : k) (g : k) a b c d e hb hc hd hface)
  by_cases he : e = 0
  · exact secondaryResidualDAtDoubleFace68_impossible a b c d hb hc
      (secondaryResidualDAtDoubleFace68_of_tied
        (n : k) (g : k) a b c d e hb hc he hface)
  exact secondaryResidualTiedDoubleFace68_impossible_of_firstDeep
    n g a b c d e ha hb hc hchamber hface

/-! ## Canonical double contradiction -/

set_option maxHeartbeats 8000000 in
theorem maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstDouble_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hchamber :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n < g ∧ 2 * g < 3 * n)
    (hdouble :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      let h := secondaryResidualGap68 n d ee
      ¬ h < 2 * g) :
    False := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  let h := secondaryResidualGap68 n d ee
  change n < g ∧ 2 * g < 3 * n at hchamber
  change ¬ h < 2 * g at hdouble
  have hsel :=
    maximalExpandedIntegratedPolynomialLowerSystem_deepGapResidualSelect68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          And.intro (by omega : n < 2 * g) hchamber.2)
  change l = 0 ∧
    (Be.coeff (3 * n - g) ≠ 0 ∨ ce.coeff (4 * n - g) ≠ 0) ∧
    d.natDegree < 5 * n - g ∧ ee.natDegree < 6 * n - g ∧
    g < h ∧
    d.natDegree ≤ 5 * n - h ∧ ee.natDegree ≤ 6 * n - h ∧
    DeepGapResidualInvariants68 n g h
      (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
      (ce.coeff (4 * n - g))
      (d.coeff (5 * n - h)) (ee.coeff (6 * n - h))
      (d.coeff (5 * n - 2 * g)) (ee.coeff (6 * n - 2 * g))
      beta at hsel
  have hl : l = 0 := hsel.1
  have hinv := hsel.2.2.2.2.2.2.2
  have hbeta := (hinv.four_double_above hdouble hchamber.1).1
  have hcore := maximalExpandedIntegratedPolynomialLowerSystem_cubicCore68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hdrop := maximalExpandedIntegratedPolynomialLowerSystem_degreeDrop68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hsecondary :=
    maximalExpandedIntegratedPolynomialLowerSystem_secondaryRadius68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  have hn : 0 < n := by simpa only [n] using hcore.1
  have hg0 : 0 < g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.1
  have ha : Ae.coeff (2 * n) ≠ 0 := by
    simpa only [n, Ae] using hcore.2.2.2.2.2
  have hA : Ae.natDegree ≤ 2 * n := by
    have hAe : Ae.natDegree = 2 * n := by
      simpa only [n, Ae, Be, Ce, De, Ee] using hdrop.1
    omega
  have hB : Be.natDegree ≤ 3 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hsecondary.2.1
  have hc : ce.natDegree ≤ 4 * n - g := by
    simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
      hsecondary.2.2.1
  have hd2 : d.natDegree ≤ 5 * n - 2 * g := by
    have hge : 2 * g ≤ h := not_lt.mp hdouble
    exact (hsel.2.2.2.2.2.1).trans (Nat.sub_le_sub_left hge (5 * n))
  have he2 : ee.natDegree ≤ 6 * n - 2 * g := by
    have hge : 2 * g ≤ h := not_lt.mp hdouble
    exact (hsel.2.2.2.2.2.2.1).trans (Nat.sub_le_sub_left hge (6 * n))
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce := by
    simpa only [ce] using cubicCDefectPolynomial68_reconstruct Ae Ce
  have hErec :
      Ee = (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee := by
    simpa only [ce, ee] using
      cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d := by
    simpa only [d] using secondaryDDefectPolynomial68_reconstruct Ae Be De
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  have hi4e : firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i4 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralFourPolynomial68_of_eq
        l beta gamma delta epsilon zeta i4 A B C0 D E hi4
  have hi3e : firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
      Ae Be Ce De Ee = C i3 := by
    simpa only [Ae, Be, Ce, De, Ee] using
      expand_firstIntegralThreePolynomial68_of_eq
        l beta gamma delta epsilon zeta i3 A B C0 D E hi3
  have hi4c := hi4e
  rw [hCrec, hErec, firstIntegralFourPolynomial68_cubicCoordinates,
    hDrec, hl, hbeta] at hi4c
  have hi3c := hi3e
  rw [hCrec, hErec, firstIntegralThreePolynomial68_cubicCoordinates,
    hDrec, hl, hbeta] at hi3c
  have h1e : lowerRowOnePolynomial68
      (integratedTPolynomial68 l alpha beta gamma epsilon Ae Be Ce De Ee)
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) Ce De Ee = 0 := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedTPolynomial68, ← expand_integratedUPolynomial68,
      ← expand_integratedVPolynomial68, lowerRowOnePolynomial68_expand,
      hsys.rowOne, map_zero, zero_mul]
  have h0e : lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee = C terminal * (60 * (X ^ 59 : k[X])) := by
    dsimp only [Ae, Be, Ce, De, Ee]
    rw [← expand_integratedUPolynomial68, ← expand_integratedVPolynomial68,
      lowerRowZeroPolynomial68_expand, hsys.rowZero, expand_C]
    norm_num
  have h0target : (lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta Ae Be Ce De Ee)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        Ae Be Ce De Ee) De Ee).coeff (13 * n - 3 * g - 1) = 0 := by
    rw [h0e]
    apply coeff_eq_zero_of_natDegree_lt
    have hdegree :
        (C terminal * (60 * (X ^ 59 : k[X]))).natDegree ≤ 59 := by
      compute_degree
    have hn10 : 10 ≤ n := by
      have hcases :
          n = 30 * A.natDegree ∨ n = 20 * B.natDegree ∨
            n = 15 * C0.natDegree ∨ n = 12 * D.natDegree ∨
              n = 10 * E.natDegree := by
        simp only [n, weightedRadius68]
        omega
      rcases hcases with hA' | hB' | hC' | hD' | hE'
      · have : 0 < A.natDegree := by omega
        omega
      · have : 0 < B.natDegree := by omega
        omega
      · have : 0 < C0.natDegree := by omega
        omega
      · have : 0 < D.natDegree := by omega
        omega
      · have : 0 < E.natDegree := by omega
        omega
    have hidx : 59 < 13 * n - 3 * g - 1 := by omega
    exact hdegree.trans_lt hidx
  have h1cubic := h1e
  rw [hCrec, hDrec, hErec, hl, hbeta] at h1cubic
  have h0cubic := h0target
  rw [hCrec, hDrec, hErec, hl, hbeta] at h0cubic
  have hface := polynomialSecondaryResidualDoubleFace68_of_firstDeep
    alpha gamma delta epsilon zeta eta i4 i3 Ae Be ce d ee n g
    hn hg0 hchamber.2 hchamber.1 hA hB hc hd2 he2 ha hi4c hi3c
    h1cubic h0cubic
  exact secondaryResidualDoubleFace68_impossible_of_firstDeep
    n g (Ae.coeff (2 * n)) (Be.coeff (3 * n - g))
    (ce.coeff (4 * n - g)) (d.coeff (5 * n - 2 * g))
    (ee.coeff (6 * n - 2 * g)) ha hsel.2.1 hchamber hface

/-! ## Mixed middle wall and remaining obstruction -/

theorem maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstMixedWall68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hchamber :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n < g ∧ 2 * g < 3 * n)
    (hmiddle :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      let h := secondaryResidualGap68 n d ee
      h < 2 * g ∧ g + h = 3 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    let d := secondaryDDefectPolynomial68 Ae Be De
    let h := secondaryResidualGap68 n d ee
    (8 / 3 : k) *
        (Be.coeff (3 * n - g) * ee.coeff (6 * n - h) +
          ce.coeff (4 * n - g) * d.coeff (5 * n - h)) +
      (5 / 72 : k) * beta * Ae.coeff (2 * n) ^ 3 = 0 := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  let h := secondaryResidualGap68 n d ee
  change n < g ∧ 2 * g < 3 * n at hchamber
  change h < 2 * g ∧ g + h = 3 * n at hmiddle
  have hsel :=
    maximalExpandedIntegratedPolynomialLowerSystem_deepGapResidualSelect68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          And.intro (by omega : n < 2 * g) hchamber.2)
  exact hsel.2.2.2.2.2.2.2.four_middle_mixed hmiddle.1 hmiddle.2

/-- On the first-deep chamber `n < g < 3n/2`, the residual double window
is impossible.  The remaining open window is residual middle `g < h < 2g`.
Its unique heaviest unresolved coefficient is the I4 load
`(5/72) beta a^3` at index `6n`: ordinary homogeneous I4 when
`g+h < 3n`, mixed exactly on `g+h = 3n`, and already forced to vanish
(hence `beta = 0`) when `3n < g+h`. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirst_obstruction68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hchamber :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n < g ∧ 2 * g < 3 * n) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    let d := secondaryDDefectPolynomial68 Ae Be De
    let h := secondaryResidualGap68 n d ee
    h < 2 * g ∧
      (g + h < 3 * n →
        Be.coeff (3 * n - g) * ee.coeff (6 * n - h) +
          ce.coeff (4 * n - g) * d.coeff (5 * n - h) = 0) ∧
      (g + h = 3 * n →
        (8 / 3 : k) *
            (Be.coeff (3 * n - g) * ee.coeff (6 * n - h) +
              ce.coeff (4 * n - g) * d.coeff (5 * n - h)) +
          (5 / 72 : k) * beta * Ae.coeff (2 * n) ^ 3 = 0) ∧
      (3 * n < g + h →
        beta = 0 ∧
          Be.coeff (3 * n - g) * ee.coeff (6 * n - h) +
            ce.coeff (4 * n - g) * d.coeff (5 * n - h) = 0) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  let h := secondaryResidualGap68 n d ee
  change n < g ∧ 2 * g < 3 * n at hchamber
  have hsel :=
    maximalExpandedIntegratedPolynomialLowerSystem_deepGapResidualSelect68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
          And.intro (by omega : n < 2 * g) hchamber.2)
  have hh : h < 2 * g := by
    by_contra hnot
    exact maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstDouble_impossible68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys (by
        simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hchamber)
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g, d, h] using hnot)
  have hinv := hsel.2.2.2.2.2.2.2
  exact ⟨hh, hinv.four_middle_below hh, hinv.four_middle_mixed hh,
    hinv.four_middle_above hh⟩

end DeepGapResidualEndgame68

#print axioms cubicLoadRowOnePolynomial68_degree_lt_cubicFace_of_firstDeep
#print axioms cubicLoadRowZeroPolynomial68_degree_lt_double_of_firstDeep_beta
#print axioms cubicLoadRowTwoPolynomial68_degree_lt_cubicFace_of_firstDeep_beta
#print axioms secondaryResidualDoubleFibre68_impossible_of_firstDeep
#print axioms polynomialSecondaryResidualDoubleFace68_of_firstDeep
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstDouble_impossible68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirstMixedWall68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirst_obstruction68

end Max11DegreeRoutes

