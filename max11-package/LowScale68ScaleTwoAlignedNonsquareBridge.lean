import LowScale68ScaleTwoAlignedFace
import LowScale46QuadraticSourceBridge

/-! # Aligned nonsquare quadratic-field source for `(6,8)`, `H = 2`

Untracked working note. No tracked file was edited.

The quadratic extension `k(x)(√H)`, its deck involution, fixed field, and
differential constants are independent of the outer pair; they are reused
from `LowScale46QuadraticField` and the generic mapping layer of
`LowScale46QuadraticSourceBridge`.  Degree-specific `(4,6)` residuals,
boundary quartics, and the last-row unit-product are not used.

This file maps a literal aligned nonsquare `(6,8)` source into that field,
proves depressed sextic/octic deck parities, forces the odd Faber constants
and the odd first integral to vanish, and packages the exact remaining
lower-row packet.
-/

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section AffineEval68

variable {F : Type*} [Field F]

theorem eval_affineDepress68_center (h r : F) (f : F[X]) :
    (affineDepress68 h r f).eval r = f.coeff 0 := by
  simpa [affineDepress68] using (coeff_zero_eq_eval_zero f).symm

end AffineEval68

section QuadraticSource68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

local notation "F68" => AdjoinRoot (alignedQuadraticPolynomial46 H)

local instance quadraticCharZero68 : CharZero F68 :=
  charZero_of_injective_ringHom (algebraMap (RatFunc k) F68).injective

/-- A mapped degree-six source with leading coefficient `h^6` is the raw
sextic used by the `(6,8)` depression. -/
theorem sourceToQuadratic68_eq_rawSextic
    (p : k[X][X]) (h : F68) (hp : p.natDegree = 6)
    (htop : quadraticCoefficientMap46 H (p.coeff 6) = h ^ 6) :
    sourceToQuadratic46 H p = rawSextic68 h
      (quadraticCoefficientMap46 H (p.coeff 5))
      (quadraticCoefficientMap46 H (p.coeff 4))
      (quadraticCoefficientMap46 H (p.coeff 3))
      (quadraticCoefficientMap46 H (p.coeff 2))
      (quadraticCoefficientMap46 H (p.coeff 1))
      (quadraticCoefficientMap46 H (p.coeff 0)) := by
  ext n
  by_cases hn : n ≤ 6
  · interval_cases n <;>
      simp [sourceToQuadratic46, rawSextic68, htop, coeff_add, coeff_C,
        coeff_C_mul, coeff_mul_X_pow', coeff_X, coeff_X_pow] <;>
      rw [← Polynomial.C_pow, coeff_C] <;> simp
  · have hn6 : 6 < n := by omega
    have hz : p.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [sourceToQuadratic46, rawSextic68, hz, coeff_add, coeff_C,
      coeff_C_mul, coeff_mul_X_pow', coeff_X, coeff_X_pow,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega,
      show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega,
      show n ≠ 6 by omega, show n - 5 ≠ 0 by omega,
      show n - 4 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
      show n - 2 ≠ 0 by omega, show 1 ≠ n by omega] <;>
      rw [← Polynomial.C_pow, coeff_C] <;>
      simp [show n - 6 ≠ 0 by omega]

/-- The analogous raw octic expansion. -/
theorem sourceToQuadratic68_eq_rawOctic
    (q : k[X][X]) (h : F68) (hq : q.natDegree = 8)
    (htop : quadraticCoefficientMap46 H (q.coeff 8) = h ^ 8) :
    sourceToQuadratic46 H q = rawOctic68 h
      (quadraticCoefficientMap46 H (q.coeff 7))
      (quadraticCoefficientMap46 H (q.coeff 6))
      (quadraticCoefficientMap46 H (q.coeff 5))
      (quadraticCoefficientMap46 H (q.coeff 4))
      (quadraticCoefficientMap46 H (q.coeff 3))
      (quadraticCoefficientMap46 H (q.coeff 2))
      (quadraticCoefficientMap46 H (q.coeff 1))
      (quadraticCoefficientMap46 H (q.coeff 0)) := by
  ext n
  by_cases hn : n ≤ 8
  · interval_cases n <;>
      simp [sourceToQuadratic46, rawOctic68, htop, coeff_add, coeff_C,
        coeff_C_mul, coeff_mul_X_pow', coeff_X, coeff_X_pow] <;>
      rw [← Polynomial.C_pow, coeff_C] <;> simp
  · have hn8 : 8 < n := by omega
    have hz : q.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [sourceToQuadratic46, rawOctic68, hz, coeff_add, coeff_C,
      coeff_C_mul, coeff_mul_X_pow', coeff_X, coeff_X_pow,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega,
      show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega,
      show n ≠ 6 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega,
      show n - 7 ≠ 0 by omega, show n - 6 ≠ 0 by omega,
      show n - 5 ≠ 0 by omega, show n - 4 ≠ 0 by omega,
      show n - 3 ≠ 0 by omega, show n - 2 ≠ 0 by omega,
      show 1 ≠ n by omega] <;>
      rw [← Polynomial.C_pow, coeff_C] <;>
      simp [show n - 8 ≠ 0 by omega]

/-- After `y=(z-r)/h`, the quadratic-field source bracket is divided by
`h`.  This is the generic affine chain rule, not a `(4,6)` identity. -/
theorem differentialJacobian_affineDepress_sourceToQuadratic68
    (p q : k[X][X]) (j : k) (h r : F68) (hh : h ≠ 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j)) :
    differentialJacobian (quadraticDerivation46 H)
        (affineDepress68 h r (sourceToQuadratic46 H p))
        (affineDepress68 h r (sourceToQuadratic46 H q)) =
      C (algebraMap k F68 j / h) := by
  simpa [affineDepress68, affineDepress46] using
    differentialJacobian_affineDepress_sourceToQuadratic46
      H p q j h r hh hD

/-- Deck equivariance of the `(6,8)` affine depression. -/
theorem sourceAffineDepress_map_deck68
    (p : k[X][X]) (h r : F68)
    (hh : alignedQuadraticDeck46 H h = -h)
    (hr : alignedQuadraticDeck46 H r = -r) :
    (affineDepress68 h r (sourceToQuadratic46 H p)).map
        (alignedQuadraticDeck46 H) =
      (affineDepress68 h r (sourceToQuadratic46 H p)).comp (-X) := by
  rw [affineDepress68, Polynomial.map_comp,
    sourceToQuadratic46_map_deck]
  rw [Polynomial.comp_assoc]
  congr 1
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, map_inv₀,
    C_comp, X_comp, sub_comp, mul_comp, neg_comp]
  change (X - C (alignedQuadraticDeck46 H r)) *
      C (alignedQuadraticDeck46 H h)⁻¹ = (-X - C r) * C h⁻¹
  rw [hh, hr]
  simp only [inv_neg, C_neg]
  ring

/-- Coefficientwise deck parities of a depressed sextic. -/
theorem depressedSextic_deckParity68 (A B C0 D E : F68)
    (hmap : (depressedSextic68 A B C0 D E).map
        (alignedQuadraticDeck46 H) =
      (depressedSextic68 A B C0 D E).comp (-X)) :
    alignedQuadraticDeck46 H A = A ∧
    alignedQuadraticDeck46 H B = -B ∧
    alignedQuadraticDeck46 H C0 = C0 ∧
    alignedQuadraticDeck46 H D = -D ∧
    alignedQuadraticDeck46 H E = E := by
  have hshape : (depressedSextic68 A B C0 D E).comp (-X) =
      depressedSextic68 A (-B) C0 (-D) E := by
    simp [depressedSextic68]
    ring
  rw [hshape] at hmap
  have h4 := congrArg (fun f : F68[X] => f.coeff 4) hmap
  have h3 := congrArg (fun f : F68[X] => f.coeff 3) hmap
  have h2 := congrArg (fun f : F68[X] => f.coeff 2) hmap
  have h1 := congrArg (fun f : F68[X] => f.coeff 1) hmap
  have h0 := congrArg (fun f : F68[X] => f.coeff 0) hmap
  norm_num [depressedSextic68, coeff_add, coeff_C, coeff_C_mul,
    coeff_mul_X_pow', coeff_X, coeff_X_pow] at h4 h3 h2 h1 h0
  exact ⟨h4, h3, h2, h1, h0⟩

/-- Alternating deck parities of a depressed octic. -/
theorem depressedOctic_deckParity68 (L P0 Q0 R0 S0 T0 U0 V0 : F68)
    (hmap : (depressedOctic68 L P0 Q0 R0 S0 T0 U0 V0).map
        (alignedQuadraticDeck46 H) =
      (depressedOctic68 L P0 Q0 R0 S0 T0 U0 V0).comp (-X)) :
    alignedQuadraticDeck46 H L = -L ∧
    alignedQuadraticDeck46 H P0 = P0 ∧
    alignedQuadraticDeck46 H Q0 = -Q0 ∧
    alignedQuadraticDeck46 H R0 = R0 ∧
    alignedQuadraticDeck46 H S0 = -S0 ∧
    alignedQuadraticDeck46 H T0 = T0 ∧
    alignedQuadraticDeck46 H U0 = -U0 ∧
    alignedQuadraticDeck46 H V0 = V0 := by
  have hshape : (depressedOctic68 L P0 Q0 R0 S0 T0 U0 V0).comp (-X) =
      depressedOctic68 (-L) P0 (-Q0) R0 (-S0) T0 (-U0) V0 := by
    simp [depressedOctic68]
    ring
  rw [hshape] at hmap
  have h7 := congrArg (fun f : F68[X] => f.coeff 7) hmap
  have h6 := congrArg (fun f : F68[X] => f.coeff 6) hmap
  have h5 := congrArg (fun f : F68[X] => f.coeff 5) hmap
  have h4 := congrArg (fun f : F68[X] => f.coeff 4) hmap
  have h3 := congrArg (fun f : F68[X] => f.coeff 3) hmap
  have h2 := congrArg (fun f : F68[X] => f.coeff 2) hmap
  have h1 := congrArg (fun f : F68[X] => f.coeff 1) hmap
  have h0 := congrArg (fun f : F68[X] => f.coeff 0) hmap
  norm_num [depressedOctic68, coeff_add, coeff_C, coeff_C_mul,
    coeff_mul_X_pow', coeff_X, coeff_X_pow] at h7 h6 h5 h4 h3 h2 h1 h0
  exact ⟨h7, h6, h5, h4, h3, h2, h1, h0⟩

/-- The seven Faber residuals, and `L` itself, descend to the ground field
of the quadratic extension. -/
theorem depressedCoefficients_integrate_over_quadratic68
    (L P0 Q0 R0 S0 T0 U0 V0 A B C0 D E terminal : F68)
    (hbracket : differentialJacobian (quadraticDerivation46 H)
        (depressedSextic68 A B C0 D E)
        (depressedOctic68 L P0 Q0 R0 S0 T0 U0 V0) = C terminal) :
    ∃ l alpha beta gamma delta epsilon zeta eta : k,
      L = algebraMap k F68 l ∧
      P0 = integratedP68 A (algebraMap k F68 alpha) ∧
      Q0 = integratedQ68 L A B (algebraMap k F68 beta) ∧
      R0 = integratedR68 L A B C0 (algebraMap k F68 alpha)
        (algebraMap k F68 gamma) ∧
      S0 = integratedS68 L A B C0 D (algebraMap k F68 alpha)
        (algebraMap k F68 beta) (algebraMap k F68 delta) ∧
      T0 = integratedT68 L A B C0 D E (algebraMap k F68 alpha)
        (algebraMap k F68 beta) (algebraMap k F68 gamma)
        (algebraMap k F68 epsilon) ∧
      U0 = integratedU68 L A B C0 D E (algebraMap k F68 alpha)
        (algebraMap k F68 beta) (algebraMap k F68 gamma)
        (algebraMap k F68 delta) (algebraMap k F68 zeta) ∧
      V0 = integratedV68 L A B C0 D E (algebraMap k F68 alpha)
        (algebraMap k F68 beta) (algebraMap k F68 gamma)
        (algebraMap k F68 delta) (algebraMap k F68 epsilon)
        (algebraMap k F68 eta) := by
  have hL := depressedL_deriv_zero68 (quadraticDerivation46 H)
    L P0 Q0 R0 S0 T0 U0 V0 A B C0 D E terminal hbracket
  rcases depressedUpperResiduals_deriv_zero68 (quadraticDerivation46 H)
      L P0 Q0 R0 S0 T0 U0 V0 A B C0 D E terminal hL hbracket with
    ⟨halpha, hbeta, hgamma, hdelta, hepsilon, hzeta, heta⟩
  have hLD : Differential.deriv L = 0 := by
    simpa only [quadraticDerivation46_apply] using hL
  have halphaD : Differential.deriv (alphaResidual68 A P0) = 0 := by
    simpa only [quadraticDerivation46_apply] using halpha
  have hbetaD : Differential.deriv (betaResidual68 L A B Q0) = 0 := by
    simpa only [quadraticDerivation46_apply] using hbeta
  have hgammaD : Differential.deriv
      (gammaResidual68 L A B C0 P0 R0) = 0 := by
    simpa only [quadraticDerivation46_apply] using hgamma
  have hdeltaD : Differential.deriv
      (deltaResidual68 L A B C0 D P0 Q0 S0) = 0 := by
    simpa only [quadraticDerivation46_apply] using hdelta
  have hepsilonD : Differential.deriv
      (epsilonResidual68 L A B C0 D E P0 Q0 R0 T0) = 0 := by
    simpa only [quadraticDerivation46_apply] using hepsilon
  have hzetaD : Differential.deriv
      (zetaResidual68 L A B C0 D E P0 Q0 R0 S0 U0) = 0 := by
    simpa only [quadraticDerivation46_apply] using hzeta
  have hetaD : Differential.deriv
      (etaResidual68 L A B C0 D E P0 Q0 R0 S0 T0 V0) = 0 := by
    simpa only [quadraticDerivation46_apply] using heta
  obtain ⟨l, hl⟩ := alignedQuadraticConstants46 H
    NonsquarePolynomial46.not_sq _ hLD
  obtain ⟨alpha, halpha'⟩ := alignedQuadraticConstants46 H
    NonsquarePolynomial46.not_sq _ halphaD
  obtain ⟨beta, hbeta'⟩ := alignedQuadraticConstants46 H
    NonsquarePolynomial46.not_sq _ hbetaD
  obtain ⟨gamma, hgamma'⟩ := alignedQuadraticConstants46 H
    NonsquarePolynomial46.not_sq _ hgammaD
  obtain ⟨delta, hdelta'⟩ := alignedQuadraticConstants46 H
    NonsquarePolynomial46.not_sq _ hdeltaD
  obtain ⟨epsilon, hepsilon'⟩ := alignedQuadraticConstants46 H
    NonsquarePolynomial46.not_sq _ hepsilonD
  obtain ⟨zeta, hzeta'⟩ := alignedQuadraticConstants46 H
    NonsquarePolynomial46.not_sq _ hzetaD
  obtain ⟨eta, heta'⟩ := alignedQuadraticConstants46 H
    NonsquarePolynomial46.not_sq _ hetaD
  have hrec := reconstructOcticCoefficients68
    L P0 Q0 R0 S0 T0 U0 V0 A B C0 D E
  dsimp only at hrec
  rw [halpha', hbeta', hgamma', hdelta', hepsilon', hzeta', heta'] at hrec
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, hl,
    hrec.1, hrec.2.1, hrec.2.2.1, hrec.2.2.2.1, hrec.2.2.2.2.1,
    hrec.2.2.2.2.2.1, hrec.2.2.2.2.2.2⟩

set_option maxHeartbeats 2000000 in
/-- With the odd Faber constants already zero, the first `z⁴` integral is
odd under the quadratic deck. -/
theorem firstIntegralFour68_alignedDeckOdd
    (A B C0 D E gamma epsilon : F68)
    (hA : alignedQuadraticDeck46 H A = A)
    (hB : alignedQuadraticDeck46 H B = -B)
    (hC : alignedQuadraticDeck46 H C0 = C0)
    (hD : alignedQuadraticDeck46 H D = -D)
    (hE : alignedQuadraticDeck46 H E = E)
    (hgamma : alignedQuadraticDeck46 H gamma = gamma)
    (hepsilon : alignedQuadraticDeck46 H epsilon = epsilon) :
    alignedQuadraticDeck46 H
        (firstIntegralFour68 0 A B C0 D E 0 gamma 0 epsilon 0) =
      - firstIntegralFour68 0 A B C0 D E 0 gamma 0 epsilon 0 := by
  simp only [firstIntegralFour68, map_add, map_sub, map_neg, map_mul,
    map_pow, map_div₀, map_ofNat, map_zero, hA, hB, hC, hD, hE,
    hgamma, hepsilon]
  ring

/-- Deck-oddness of `Q = (4/3)B + beta` forces the ground constant `beta`
to vanish. -/
theorem quadraticDeck_kills_beta68
    (A B : F68) (beta : k)
    (hB : alignedQuadraticDeck46 H B = -B)
    (hQodd : alignedQuadraticDeck46 H
        (integratedQ68 0 A B (algebraMap k F68 beta)) =
      - integratedQ68 0 A B (algebraMap k F68 beta)) :
    beta = 0 := by
  simp only [integratedQ68, map_add, map_mul, map_div₀, map_ofNat,
    map_zero, mul_zero, zero_mul, add_zero, zero_add, hB,
    alignedQuadraticDeck46_ground] at hQodd
  ring_nf at hQodd
  have h2 : (2 : F68) * algebraMap k F68 beta = 0 := by
    linear_combination hQodd
  have hbetaF : algebraMap k F68 beta = 0 :=
    (mul_eq_zero.mp h2).resolve_left (by norm_num)
  exact (algebraMap k F68).injective (by simpa using hbetaF)

/-- Deck-oddness of the aligned `S` coefficient forces `delta = 0`. -/
theorem quadraticDeck_kills_delta68
    (A B C0 D : F68) (alpha delta : k)
    (hA : alignedQuadraticDeck46 H A = A)
    (hB : alignedQuadraticDeck46 H B = -B)
    (hD : alignedQuadraticDeck46 H D = -D)
    (hSodd : alignedQuadraticDeck46 H
        (integratedS68 0 A B C0 D (algebraMap k F68 alpha) 0
          (algebraMap k F68 delta)) =
      - integratedS68 0 A B C0 D (algebraMap k F68 alpha) 0
          (algebraMap k F68 delta)) :
    delta = 0 := by
  simp only [integratedS68, map_add, map_mul, map_div₀, map_pow,
    map_ofNat, map_zero, mul_zero, zero_mul, add_zero, zero_add, hA, hB,
    hD, alignedQuadraticDeck46_ground] at hSodd
  ring_nf at hSodd
  have h2 : (2 : F68) * algebraMap k F68 delta = 0 := by
    linear_combination hSodd
  have hdeltaF : algebraMap k F68 delta = 0 :=
    (mul_eq_zero.mp h2).resolve_left (by norm_num)
  exact (algebraMap k F68).injective (by simpa using hdeltaF)

/-- Deck-oddness of the aligned `U` coefficient forces `zeta = 0`. -/
theorem quadraticDeck_kills_zeta68
    (A B C0 D E : F68) (alpha gamma zeta : k)
    (hA : alignedQuadraticDeck46 H A = A)
    (hB : alignedQuadraticDeck46 H B = -B)
    (hC : alignedQuadraticDeck46 H C0 = C0)
    (hD : alignedQuadraticDeck46 H D = -D)
    (hUodd : alignedQuadraticDeck46 H
        (integratedU68 0 A B C0 D E (algebraMap k F68 alpha) 0
          (algebraMap k F68 gamma) 0 (algebraMap k F68 zeta)) =
      - integratedU68 0 A B C0 D E (algebraMap k F68 alpha) 0
          (algebraMap k F68 gamma) 0 (algebraMap k F68 zeta)) :
    zeta = 0 := by
  simp only [integratedU68, map_add, map_sub, map_mul, map_div₀, map_pow,
    map_ofNat, map_zero, mul_zero, zero_mul, add_zero, zero_add, hA, hB,
    hC, hD, alignedQuadraticDeck46_ground] at hUodd
  ring_nf at hUodd
  have h2 : (2 : F68) * algebraMap k F68 zeta = 0 := by
    linear_combination hUodd
  have hzetaF : algebraMap k F68 zeta = 0 :=
    (mul_eq_zero.mp h2).resolve_left (by norm_num)
  exact (algebraMap k F68).injective (by simpa using hzetaF)

/-- Source-facing data for the aligned nonsquare `(6,8)` branch after deck
parity has collapsed it to `beta = delta = zeta = 0`. -/
structure NonsquareAlignedSourceCurveData68
    (p q : k[X][X]) (j : k) where
  r : F68
  A : F68
  B : F68
  C0 : F68
  D : F68
  E : F68
  alpha : k
  gamma : k
  epsilon : k
  eta : k
  scale_ne_zero : AdjoinRoot.root (alignedQuadraticPolynomial46 H) ≠ 0
  r_odd : alignedQuadraticDeck46 H r = -r
  A_even : alignedQuadraticDeck46 H A = A
  B_odd : alignedQuadraticDeck46 H B = -B
  C_even : alignedQuadraticDeck46 H C0 = C0
  D_odd : alignedQuadraticDeck46 H D = -D
  E_even : alignedQuadraticDeck46 H E = E
  sextic_eq :
    affineDepress68 (AdjoinRoot.root (alignedQuadraticPolynomial46 H)) r
        (sourceToQuadratic46 H p) = depressedSextic68 A B C0 D E
  octic_eq :
    affineDepress68 (AdjoinRoot.root (alignedQuadraticPolynomial46 H)) r
        (sourceToQuadratic46 H q) =
      depressedOctic68 0
        (integratedP68 A (algebraMap k F68 alpha))
        (integratedQ68 0 A B 0)
        (integratedR68 0 A B C0 (algebraMap k F68 alpha)
          (algebraMap k F68 gamma))
        (integratedS68 0 A B C0 D (algebraMap k F68 alpha) 0 0)
        (integratedT68 0 A B C0 D E (algebraMap k F68 alpha) 0
          (algebraMap k F68 gamma) (algebraMap k F68 epsilon))
        (integratedU68 0 A B C0 D E (algebraMap k F68 alpha) 0
          (algebraMap k F68 gamma) 0 0)
        (integratedV68 0 A B C0 D E (algebraMap k F68 alpha) 0
          (algebraMap k F68 gamma) 0 (algebraMap k F68 epsilon)
          (algebraMap k F68 eta))
  bracket_eq :
    differentialJacobian (quadraticDerivation46 H)
        (depressedSextic68 A B C0 D E)
        (depressedOctic68 0
          (integratedP68 A (algebraMap k F68 alpha))
          (integratedQ68 0 A B 0)
          (integratedR68 0 A B C0 (algebraMap k F68 alpha)
            (algebraMap k F68 gamma))
          (integratedS68 0 A B C0 D (algebraMap k F68 alpha) 0 0)
          (integratedT68 0 A B C0 D E (algebraMap k F68 alpha) 0
            (algebraMap k F68 gamma) (algebraMap k F68 epsilon))
          (integratedU68 0 A B C0 D E (algebraMap k F68 alpha) 0
            (algebraMap k F68 gamma) 0 0)
          (integratedV68 0 A B C0 D E (algebraMap k F68 alpha) 0
            (algebraMap k F68 gamma) 0 (algebraMap k F68 epsilon)
            (algebraMap k F68 eta))) =
      C (algebraMap k F68 j /
        AdjoinRoot.root (alignedQuadraticPolynomial46 H))
  centerSextic :
    (depressedSextic68 A B C0 D E).eval r =
      quadraticCoefficientMap46 H (p.coeff 0)
  centerOctic :
    (depressedOctic68 0
        (integratedP68 A (algebraMap k F68 alpha))
        (integratedQ68 0 A B 0)
        (integratedR68 0 A B C0 (algebraMap k F68 alpha)
          (algebraMap k F68 gamma))
        (integratedS68 0 A B C0 D (algebraMap k F68 alpha) 0 0)
        (integratedT68 0 A B C0 D E (algebraMap k F68 alpha) 0
          (algebraMap k F68 gamma) (algebraMap k F68 epsilon))
        (integratedU68 0 A B C0 D E (algebraMap k F68 alpha) 0
          (algebraMap k F68 gamma) 0 0)
        (integratedV68 0 A B C0 D E (algebraMap k F68 alpha) 0
          (algebraMap k F68 gamma) 0 (algebraMap k F68 epsilon)
          (algebraMap k F68 eta))).eval r =
      quadraticCoefficientMap46 H (q.coeff 0)

/-- Depressed aligned source in `k(x)(√H)` before Faber constants are
killed. -/
structure NonsquareAlignedDepressedSource68
    (p q : k[X][X]) (j : k) where
  r : F68
  A : F68
  B : F68
  C0 : F68
  D : F68
  E : F68
  P0 : F68
  Q0 : F68
  R0 : F68
  S0 : F68
  T0 : F68
  U0 : F68
  V0 : F68
  scale_ne_zero : AdjoinRoot.root (alignedQuadraticPolynomial46 H) ≠ 0
  r_odd : alignedQuadraticDeck46 H r = -r
  A_even : alignedQuadraticDeck46 H A = A
  B_odd : alignedQuadraticDeck46 H B = -B
  C_even : alignedQuadraticDeck46 H C0 = C0
  D_odd : alignedQuadraticDeck46 H D = -D
  E_even : alignedQuadraticDeck46 H E = E
  Q_odd : alignedQuadraticDeck46 H Q0 = -Q0
  S_odd : alignedQuadraticDeck46 H S0 = -S0
  U_odd : alignedQuadraticDeck46 H U0 = -U0
  sextic_eq :
    affineDepress68 (AdjoinRoot.root (alignedQuadraticPolynomial46 H)) r
        (sourceToQuadratic46 H p) = depressedSextic68 A B C0 D E
  octic_eq :
    affineDepress68 (AdjoinRoot.root (alignedQuadraticPolynomial46 H)) r
        (sourceToQuadratic46 H q) =
      depressedOctic68 0 P0 Q0 R0 S0 T0 U0 V0
  bracket_eq :
    differentialJacobian (quadraticDerivation46 H)
        (depressedSextic68 A B C0 D E)
        (depressedOctic68 0 P0 Q0 R0 S0 T0 U0 V0) =
      C (algebraMap k F68 j /
        AdjoinRoot.root (alignedQuadraticPolynomial46 H))

set_option maxHeartbeats 2000000 in
/-- Affine depression of an aligned nonsquare source, with `L = 0`. -/
theorem nonsquareAlignedDepressedSource68
    (p q : k[X][X]) (j : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned : (4 : k[X]) * p.coeff 5 * H -
      (3 : k[X]) * q.coeff 7 = 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j)) :
    Nonempty (NonsquareAlignedDepressedSource68 H p q j) := by
  let h : F68 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  let a5 : F68 := quadraticCoefficientMap46 H (p.coeff 5)
  let a4 : F68 := quadraticCoefficientMap46 H (p.coeff 4)
  let a3 : F68 := quadraticCoefficientMap46 H (p.coeff 3)
  let a2 : F68 := quadraticCoefficientMap46 H (p.coeff 2)
  let a1 : F68 := quadraticCoefficientMap46 H (p.coeff 1)
  let a0 : F68 := quadraticCoefficientMap46 H (p.coeff 0)
  let b7 : F68 := quadraticCoefficientMap46 H (q.coeff 7)
  let b6 : F68 := quadraticCoefficientMap46 H (q.coeff 6)
  let b5 : F68 := quadraticCoefficientMap46 H (q.coeff 5)
  let b4 : F68 := quadraticCoefficientMap46 H (q.coeff 4)
  let b3 : F68 := quadraticCoefficientMap46 H (q.coeff 3)
  let b2 : F68 := quadraticCoefficientMap46 H (q.coeff 2)
  let b1 : F68 := quadraticCoefficientMap46 H (q.coeff 1)
  let b0 : F68 := quadraticCoefficientMap46 H (q.coeff 0)
  let r : F68 := sexticDepressionR68 h a5
  let A : F68 := depressedA68 h r a5 a4
  let B : F68 := depressedB68 h r a5 a4 a3
  let C0 : F68 := depressedC68 h r a5 a4 a3 a2
  let D : F68 := depressedD68 h r a5 a4 a3 a2 a1
  let E : F68 := depressedE68 h r a5 a4 a3 a2 a1 a0
  let L : F68 := depressedL68 h r b7
  let P0 : F68 := depressedP68 h r b7 b6
  let Q0 : F68 := depressedQ68 h r b7 b6 b5
  let R0 : F68 := depressedR68 h r b7 b6 b5 b4
  let S0 : F68 := depressedS68 h r b7 b6 b5 b4 b3
  let T0 : F68 := depressedT68 h r b7 b6 b5 b4 b3 b2
  let U0 : F68 := depressedU68 h r b7 b6 b5 b4 b3 b2 b1
  let V0 : F68 := depressedV68 h r b7 b6 b5 b4 b3 b2 b1 b0
  have hHne : H ≠ 0 := by
    intro hzero
    exact NonsquarePolynomial46.not_sq (H := H) (0 : k[X]) (by
      simp [hzero])
  have hrootSq : h ^ 2 = quadraticCoefficientMap46 H H :=
    alignedQuadraticRoot_sq46 H
  have hphi : Function.Injective (quadraticCoefficientMap46 H) :=
    (algebraMap (RatFunc k) F68).injective.comp
      (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  have hh : h ≠ 0 := by
    intro hz
    have : quadraticCoefficientMap46 H H = 0 := by
      rw [← hrootSq, hz]
      simp
    exact hHne (hphi (this.trans (map_zero _).symm))
  have hpTop : quadraticCoefficientMap46 H (p.coeff 6) = h ^ 6 := by
    rw [hp6, map_pow, ← hrootSq]
    ring
  have hqTop : quadraticCoefficientMap46 H (q.coeff 8) = h ^ 8 := by
    rw [hq8, map_pow, ← hrootSq]
    ring
  have hpDep : affineDepress68 h r (sourceToQuadratic46 H p) =
      depressedSextic68 A B C0 D E := by
    rw [sourceToQuadratic68_eq_rawSextic H p h hp hpTop]
    exact affineDepress_rawSextic68 h r a5 a4 a3 a2 a1 a0 hh rfl
  have hqDep : affineDepress68 h r (sourceToQuadratic46 H q) =
      depressedOctic68 L P0 Q0 R0 S0 T0 U0 V0 := by
    rw [sourceToQuadratic68_eq_rawOctic H q h hq hqTop]
    exact affineDepress_rawOctic68 h r b7 b6 b5 b4 b3 b2 b1 b0 hh
  have halignedF : 4 * a5 * h ^ 2 - 3 * b7 = 0 := by
    have hmapped := congrArg (quadraticCoefficientMap46 H) haligned
    simp only [map_sub, map_mul, map_ofNat, map_zero] at hmapped
    rw [hrootSq]
    simpa only [a5, b7] using hmapped
  have hL : L = 0 :=
    depressedL68_eq_zero_of_aligned h a5 b7 hh halignedF
  have hbracket := differentialJacobian_affineDepress_sourceToQuadratic68
    H p q j h r hh hD
  rw [hpDep, hqDep, hL] at hbracket
  have hrOdd : alignedQuadraticDeck46 H r = -r := by
    simp only [r, h, sexticDepressionR68, map_div₀, map_mul, map_ofNat,
      map_pow, alignedQuadraticDeck46_root,
      alignedQuadraticDeck46_coefficient, a5]
    field_simp [hh]
  have hpMap := sourceAffineDepress_map_deck68 H p h r
    (alignedQuadraticDeck46_root H) hrOdd
  rw [hpDep] at hpMap
  obtain ⟨hAEven, hBOdd, hCEven, hDOdd, hEEven⟩ :=
    depressedSextic_deckParity68 H A B C0 D E hpMap
  have hqMap := sourceAffineDepress_map_deck68 H q h r
    (alignedQuadraticDeck46_root H) hrOdd
  rw [hqDep] at hqMap
  obtain ⟨_hLOdd, _hPEven, hQOdd, _hREven, hSOdd, _hTEven, hUOdd, _hVEven⟩ :=
    depressedOctic_deckParity68 H L P0 Q0 R0 S0 T0 U0 V0 hqMap
  exact ⟨{
    r := r
    A := A
    B := B
    C0 := C0
    D := D
    E := E
    P0 := P0
    Q0 := Q0
    R0 := R0
    S0 := S0
    T0 := T0
    U0 := U0
    V0 := V0
    scale_ne_zero := hh
    r_odd := hrOdd
    A_even := hAEven
    B_odd := hBOdd
    C_even := hCEven
    D_odd := hDOdd
    E_even := hEEven
    Q_odd := hQOdd
    S_odd := hSOdd
    U_odd := hUOdd
    sextic_eq := hpDep
    octic_eq := by
      rw [hqDep, hL]
    bracket_eq := hbracket
  }⟩

set_option maxHeartbeats 4000000 in
/-- A literal aligned source in the nonsquare branch produces the complete
quadratic-field packet with odd Faber constants killed. -/
theorem nonsquareAlignedSourceCurveData68
    (p q : k[X][X]) (j : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned : (4 : k[X]) * p.coeff 5 * H -
      (3 : k[X]) * q.coeff 7 = 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j)) :
    Nonempty (NonsquareAlignedSourceCurveData68 H p q j) := by
  obtain ⟨D0⟩ :=
    nonsquareAlignedDepressedSource68 (H := H) p q j hp hq hp6 hq8
      haligned hD
  let h : F68 := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta,
      hl, hP, hQ, hR, hS, hT, hU, hV⟩ :=
    depressedCoefficients_integrate_over_quadratic68 H
      0 D0.P0 D0.Q0 D0.R0 D0.S0 D0.T0 D0.U0 D0.V0
      D0.A D0.B D0.C0 D0.D D0.E (algebraMap k F68 j / h) D0.bracket_eq
  have hl0 : l = 0 := (algebraMap k F68).injective (by
    simpa using hl.symm)
  subst hl0
  have hQ0 : D0.Q0 = integratedQ68 0 D0.A D0.B (algebraMap k F68 beta) := by
    simpa using hQ
  have hbeta : beta = 0 :=
    quadraticDeck_kills_beta68 H D0.A D0.B beta D0.B_odd (by
      rw [← hQ0]
      exact D0.Q_odd)
  have hS0 : D0.S0 = integratedS68 0 D0.A D0.B D0.C0 D0.D
      (algebraMap k F68 alpha) 0 (algebraMap k F68 delta) := by
    simpa [hbeta] using hS
  have hdelta : delta = 0 :=
    quadraticDeck_kills_delta68 H D0.A D0.B D0.C0 D0.D alpha delta
      D0.A_even D0.B_odd D0.D_odd (by
        rw [← hS0]
        exact D0.S_odd)
  have hU0 : D0.U0 = integratedU68 0 D0.A D0.B D0.C0 D0.D D0.E
      (algebraMap k F68 alpha) 0 (algebraMap k F68 gamma) 0
      (algebraMap k F68 zeta) := by
    simpa [hbeta, hdelta] using hU
  have hzeta : zeta = 0 :=
    quadraticDeck_kills_zeta68 H D0.A D0.B D0.C0 D0.D D0.E alpha gamma zeta
      D0.A_even D0.B_odd D0.C_even D0.D_odd (by
        rw [← hU0]
        exact D0.U_odd)
  have hqIntegrated :
      affineDepress68 h D0.r (sourceToQuadratic46 H q) =
        depressedOctic68 0
          (integratedP68 D0.A (algebraMap k F68 alpha))
          (integratedQ68 0 D0.A D0.B 0)
          (integratedR68 0 D0.A D0.B D0.C0 (algebraMap k F68 alpha)
            (algebraMap k F68 gamma))
          (integratedS68 0 D0.A D0.B D0.C0 D0.D (algebraMap k F68 alpha) 0 0)
          (integratedT68 0 D0.A D0.B D0.C0 D0.D D0.E (algebraMap k F68 alpha) 0
            (algebraMap k F68 gamma) (algebraMap k F68 epsilon))
          (integratedU68 0 D0.A D0.B D0.C0 D0.D D0.E (algebraMap k F68 alpha) 0
            (algebraMap k F68 gamma) 0 0)
          (integratedV68 0 D0.A D0.B D0.C0 D0.D D0.E (algebraMap k F68 alpha) 0
            (algebraMap k F68 gamma) 0 (algebraMap k F68 epsilon)
            (algebraMap k F68 eta)) := by
    rw [D0.octic_eq, hP, hQ, hR, hS, hT, hU, hV, hbeta, hdelta, hzeta]
    simp only [map_zero]
  have hbracketIntegrated :
      differentialJacobian (quadraticDerivation46 H)
          (depressedSextic68 D0.A D0.B D0.C0 D0.D D0.E)
          (depressedOctic68 0
            (integratedP68 D0.A (algebraMap k F68 alpha))
            (integratedQ68 0 D0.A D0.B 0)
            (integratedR68 0 D0.A D0.B D0.C0 (algebraMap k F68 alpha)
              (algebraMap k F68 gamma))
            (integratedS68 0 D0.A D0.B D0.C0 D0.D (algebraMap k F68 alpha) 0 0)
            (integratedT68 0 D0.A D0.B D0.C0 D0.D D0.E
              (algebraMap k F68 alpha) 0 (algebraMap k F68 gamma)
              (algebraMap k F68 epsilon))
            (integratedU68 0 D0.A D0.B D0.C0 D0.D D0.E
              (algebraMap k F68 alpha) 0 (algebraMap k F68 gamma) 0 0)
            (integratedV68 0 D0.A D0.B D0.C0 D0.D D0.E
              (algebraMap k F68 alpha) 0 (algebraMap k F68 gamma) 0
              (algebraMap k F68 epsilon) (algebraMap k F68 eta))) =
        C (algebraMap k F68 j / h) := by
    have hbracket := D0.bracket_eq
    rw [hP, hQ, hR, hS, hT, hU, hV, hbeta, hdelta, hzeta] at hbracket
    simpa only [map_zero] using hbracket
  have hcenterS : (depressedSextic68 D0.A D0.B D0.C0 D0.D D0.E).eval D0.r =
      quadraticCoefficientMap46 H (p.coeff 0) := by
    have hpCenter := congrArg (fun f : F68[X] => f.eval D0.r) D0.sextic_eq
    rw [eval_affineDepress68_center] at hpCenter
    simpa [sourceToQuadratic46, coeff_map] using hpCenter.symm
  have hcenterO :
      (depressedOctic68 0
          (integratedP68 D0.A (algebraMap k F68 alpha))
          (integratedQ68 0 D0.A D0.B 0)
          (integratedR68 0 D0.A D0.B D0.C0 (algebraMap k F68 alpha)
            (algebraMap k F68 gamma))
          (integratedS68 0 D0.A D0.B D0.C0 D0.D (algebraMap k F68 alpha) 0 0)
          (integratedT68 0 D0.A D0.B D0.C0 D0.D D0.E (algebraMap k F68 alpha) 0
            (algebraMap k F68 gamma) (algebraMap k F68 epsilon))
          (integratedU68 0 D0.A D0.B D0.C0 D0.D D0.E (algebraMap k F68 alpha) 0
            (algebraMap k F68 gamma) 0 0)
          (integratedV68 0 D0.A D0.B D0.C0 D0.D D0.E (algebraMap k F68 alpha) 0
            (algebraMap k F68 gamma) 0 (algebraMap k F68 epsilon)
            (algebraMap k F68 eta))).eval D0.r =
        quadraticCoefficientMap46 H (q.coeff 0) := by
    have hqCenter := congrArg (fun f : F68[X] => f.eval D0.r) hqIntegrated
    rw [eval_affineDepress68_center] at hqCenter
    simpa [sourceToQuadratic46, coeff_map] using hqCenter.symm
  exact ⟨{
    r := D0.r
    A := D0.A
    B := D0.B
    C0 := D0.C0
    D := D0.D
    E := D0.E
    alpha := alpha
    gamma := gamma
    epsilon := epsilon
    eta := eta
    scale_ne_zero := D0.scale_ne_zero
    r_odd := D0.r_odd
    A_even := D0.A_even
    B_odd := D0.B_odd
    C_even := D0.C_even
    D_odd := D0.D_odd
    E_even := D0.E_even
    sextic_eq := D0.sextic_eq
    octic_eq := hqIntegrated
    bracket_eq := hbracketIntegrated
    centerSextic := hcenterS
    centerOctic := hcenterO
  }⟩

/-- Even coordinates, squares, and mixed even products descend to `k(x)`. -/
theorem NonsquareAlignedSourceCurveData68.evenCoordinatesDescend
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    (∃ aR : RatFunc k,
        S.A = algebraMap (RatFunc k) F68 aR) ∧
    (∃ cR : RatFunc k,
        S.C0 = algebraMap (RatFunc k) F68 cR) ∧
    (∃ eR : RatFunc k,
        S.E = algebraMap (RatFunc k) F68 eR) ∧
    (∃ qR : RatFunc k,
        S.r ^ 2 = algebraMap (RatFunc k) F68 qR) ∧
    (∃ kB : RatFunc k,
        S.B ^ 2 = algebraMap (RatFunc k) F68 kB) ∧
    (∃ kD : RatFunc k,
        S.D ^ 2 = algebraMap (RatFunc k) F68 kD) ∧
    (∃ wB : RatFunc k,
        S.r * S.B = algebraMap (RatFunc k) F68 wB) ∧
    (∃ wD : RatFunc k,
        S.r * S.D = algebraMap (RatFunc k) F68 wD) ∧
    (∃ mB : RatFunc k,
        AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.B =
          algebraMap (RatFunc k) F68 mB) ∧
    (∃ mD : RatFunc k,
        AdjoinRoot.root (alignedQuadraticPolynomial46 H) * S.D =
          algebraMap (RatFunc k) F68 mD) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact alignedQuadraticFixedElementDescends46 H S.A S.A_even
  · exact alignedQuadraticFixedElementDescends46 H S.C0 S.C_even
  · exact alignedQuadraticFixedElementDescends46 H S.E S.E_even
  · apply alignedQuadraticFixedElementDescends46 H
    simp only [map_pow, S.r_odd]
    ring
  · apply alignedQuadraticFixedElementDescends46 H
    simp only [map_pow, S.B_odd]
    ring
  · apply alignedQuadraticFixedElementDescends46 H
    simp only [map_pow, S.D_odd]
    ring
  · apply alignedQuadraticFixedElementDescends46 H
    simp only [map_mul, S.r_odd, S.B_odd]
    ring
  · apply alignedQuadraticFixedElementDescends46 H
    simp only [map_mul, S.r_odd, S.D_odd]
    ring
  · apply alignedQuadraticFixedElementDescends46 H
    simp only [map_mul, alignedQuadraticDeck46_root, S.B_odd]
    ring
  · apply alignedQuadraticFixedElementDescends46 H
    simp only [map_mul, alignedQuadraticDeck46_root, S.D_odd]
    ring

set_option maxHeartbeats 4000000 in
/-- Finite residual packet: `I₄ = 0`, `I₃` in `k`, the two remaining
one-form rows, and the last Keller row `h(U E' - D V') = j`. -/
theorem NonsquareAlignedSourceCurveData68.residualPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    firstIntegralFour68 0 S.A S.B S.C0 S.D S.E 0
        (algebraMap k F68 S.gamma) 0 (algebraMap k F68 S.epsilon) 0 = 0 ∧
    (∃ i3 : k,
      firstIntegralThree68 0 S.A S.B S.C0 S.D S.E 0
          (algebraMap k F68 S.gamma) 0 (algebraMap k F68 S.epsilon) 0 =
        algebraMap k F68 i3) ∧
    (let ck := algebraMap k F68
     let d := quadraticDerivation46 H
     let T := integratedT68 0 S.A S.B S.C0 S.D S.E (ck S.alpha) 0
       (ck S.gamma) (ck S.epsilon)
     let U := integratedU68 0 S.A S.B S.C0 S.D S.E (ck S.alpha) 0
       (ck S.gamma) 0 0
     let V := integratedV68 0 S.A S.B S.C0 S.D S.E (ck S.alpha) 0
       (ck S.gamma) 0 (ck S.epsilon) (ck S.eta)
     let SS := integratedS68 0 S.A S.B S.C0 S.D (ck S.alpha) 0 0
     U * d S.C0 + 2 * T * d S.D + 3 * SS * d S.E -
         3 * S.B * d V - 2 * S.C0 * d U - S.D * d T = 0) ∧
    (let ck := algebraMap k F68
     let d := quadraticDerivation46 H
     let T := integratedT68 0 S.A S.B S.C0 S.D S.E (ck S.alpha) 0
       (ck S.gamma) (ck S.epsilon)
     let U := integratedU68 0 S.A S.B S.C0 S.D S.E (ck S.alpha) 0
       (ck S.gamma) 0 0
     let V := integratedV68 0 S.A S.B S.C0 S.D S.E (ck S.alpha) 0
       (ck S.gamma) 0 (ck S.epsilon) (ck S.eta)
     U * d S.D + 2 * T * d S.E - 2 * S.C0 * d V - S.D * d U = 0) ∧
    AdjoinRoot.root (alignedQuadraticPolynomial46 H) *
        (integratedU68 0 S.A S.B S.C0 S.D S.E
            (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0 0 *
          quadraticDerivation46 H S.E -
          S.D * quadraticDerivation46 H
            (integratedV68 0 S.A S.B S.C0 S.D S.E
              (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0
              (algebraMap k F68 S.epsilon) (algebraMap k F68 S.eta))) =
      algebraMap k F68 j := by
  have hconst (c : k) :
      quadraticDerivation46 H (algebraMap k F68 c) = 0 := by
    simp only [quadraticDerivation46_apply]
    exact GCD369BaseConstants c
  have hlow := constantBracket_integrated68_lowerSystem
    (quadraticDerivation46 H) 0 S.A S.B S.C0 S.D S.E
    (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0
    (algebraMap k F68 S.epsilon) 0 (algebraMap k F68 S.eta)
    (algebraMap k F68 j /
      AdjoinRoot.root (alignedQuadraticPolynomial46 H))
    (by simp [quadraticDerivation46_apply])
    (hconst S.alpha)
    (by simp [quadraticDerivation46_apply])
    (hconst S.gamma)
    (by simp [quadraticDerivation46_apply])
    (hconst S.epsilon)
    (by simp [quadraticDerivation46_apply])
    (hconst S.eta) S.bracket_eq
  dsimp only at hlow
  have hI4D : Differential.deriv
      (firstIntegralFour68 0 S.A S.B S.C0 S.D S.E 0
        (algebraMap k F68 S.gamma) 0 (algebraMap k F68 S.epsilon) 0) = 0 := by
    simpa only [quadraticDerivation46_apply] using hlow.1
  have hI3D : Differential.deriv
      (firstIntegralThree68 0 S.A S.B S.C0 S.D S.E 0
        (algebraMap k F68 S.gamma) 0 (algebraMap k F68 S.epsilon) 0) = 0 := by
    simpa only [quadraticDerivation46_apply] using hlow.2.1
  obtain ⟨i4, hi4⟩ := alignedQuadraticConstants46 H
    NonsquarePolynomial46.not_sq _ hI4D
  obtain ⟨i3, hi3⟩ := alignedQuadraticConstants46 H
    NonsquarePolynomial46.not_sq _ hI3D
  have hI4odd := firstIntegralFour68_alignedDeckOdd H S.A S.B S.C0 S.D S.E
    (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon)
    S.A_even S.B_odd S.C_even S.D_odd S.E_even
    (alignedQuadraticDeck46_ground H S.gamma)
    (alignedQuadraticDeck46_ground H S.epsilon)
  have hi4F : algebraMap k F68 i4 = 0 := by
    have hfix := congrArg (alignedQuadraticDeck46 H) hi4
    simp only [alignedQuadraticDeck46_ground] at hfix
    rw [hI4odd, hi4] at hfix
    linear_combination (-1 / 2 : F68) * hfix
  have hI4 : firstIntegralFour68 0 S.A S.B S.C0 S.D S.E 0
      (algebraMap k F68 S.gamma) 0 (algebraMap k F68 S.epsilon) 0 = 0 := by
    rw [hi4, hi4F]
  have hlast :
      AdjoinRoot.root (alignedQuadraticPolynomial46 H) *
          (integratedU68 0 S.A S.B S.C0 S.D S.E
              (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0 0 *
            quadraticDerivation46 H S.E -
            S.D * quadraticDerivation46 H
              (integratedV68 0 S.A S.B S.C0 S.D S.E
                (algebraMap k F68 S.alpha) 0 (algebraMap k F68 S.gamma) 0
                (algebraMap k F68 S.epsilon) (algebraMap k F68 S.eta))) =
        algebraMap k F68 j := by
    have hrow := hlow.2.2.2.2
    rw [hrow]
    field_simp [S.scale_ne_zero]
  exact ⟨hI4, ⟨i3, hi3⟩, hlow.2.2.1, hlow.2.2.2.1, hlast⟩

end QuadraticSource68

section AlignedNonsquareHandoff68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Every aligned normalized scale-two source whose core is not a
polynomial square produces the quadratic-field packet. -/
theorem normalized68ScaleTwo_alignedNonsquare_quadraticSourceData
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    let _inst : NonsquarePolynomial46 H := ⟨hnsq⟩
    ∃ j : k, j ≠ 0 ∧ Nonempty (NonsquareAlignedSourceCurveData68 H p q j) := by
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  letI : NonsquarePolynomial46 H := ⟨hnsq⟩
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp6, hq8, hKeller⟩
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 8 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq8' : q.coeff 8 = H ^ 4 := by simpa only [q] using hq8
  have haligned' : (4 : k[X]) * p.coeff 5 * H -
      (3 : k[X]) * q.coeff 7 = 0 := by
    simpa only [p, q] using haligned
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q = C (C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  refine ⟨j, hj, ?_⟩
  exact nonsquareAlignedSourceCurveData68 (H := H) p q j
    hp hq hp6' hq8' haligned' hD

/-- The exact remaining quadratic-field packet.  No last-row unit-product
or polynomial-representative contradiction is claimed. -/
def PlaneKeller68AlignedNonsquareQuadraticPacketExclusion : Prop :=
  ∀ (H : k[X]) [NonsquarePolynomial46 H] (p q : k[X][X]) (j : k),
    NonsquareAlignedSourceCurveData68 H p q j → j ≠ 0 → False

/-- The aligned nonsquare source chamber is closed by precisely the
quadratic-field packet exclusion above. -/
theorem planeKeller68AlignedNonsquareExclusion_of_quadraticPacket
    (hpacket : PlaneKeller68AlignedNonsquareQuadraticPacketExclusion
      (k := k)) :
    PlaneKeller68AlignedNonsquareExclusion (k := k) := by
  intro P Q H hsource hnsq haligned
  obtain ⟨j, hj, ⟨S⟩⟩ :=
    normalized68ScaleTwo_alignedNonsquare_quadraticSourceData
      hsource hnsq haligned
  letI : NonsquarePolynomial46 H := ⟨hnsq⟩
  exact hpacket H _ _ j S hj

end AlignedNonsquareHandoff68

#print axioms eval_affineDepress68_center
#print axioms sourceToQuadratic68_eq_rawSextic
#print axioms sourceToQuadratic68_eq_rawOctic
#print axioms differentialJacobian_affineDepress_sourceToQuadratic68
#print axioms sourceAffineDepress_map_deck68
#print axioms depressedSextic_deckParity68
#print axioms depressedOctic_deckParity68
#print axioms depressedCoefficients_integrate_over_quadratic68
#print axioms firstIntegralFour68_alignedDeckOdd
#print axioms quadraticDeck_kills_beta68
#print axioms quadraticDeck_kills_delta68
#print axioms quadraticDeck_kills_zeta68
#print axioms nonsquareAlignedDepressedSource68
#print axioms nonsquareAlignedSourceCurveData68
#print axioms NonsquareAlignedSourceCurveData68.evenCoordinatesDescend
#print axioms NonsquareAlignedSourceCurveData68.residualPacket
#print axioms normalized68ScaleTwo_alignedNonsquare_quadraticSourceData
#print axioms planeKeller68AlignedNonsquareExclusion_of_quadraticPacket

end Max11DegreeRoutes
