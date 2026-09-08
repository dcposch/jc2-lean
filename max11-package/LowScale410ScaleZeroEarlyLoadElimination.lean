import LowScale410ScaleZeroSourceBridge
import LowScale410BetaWall

/-!
# Exact early-load reduction for the scale-zero `(4,10)` source

This module does not assume that constant leading core makes the Faber loads
vanish.  Instead it applies every completed wall theorem to an arbitrary
integrated trajectory.  The `l` wall closes completely; the remaining
exhaustive packet has one beta leaf and two genuinely mixed later-load
leaves.
-/

noncomputable section

set_option maxHeartbeats 3000000

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section EarlyLoadElimination410

variable {k : Type*} [Field k] [CharZero k]

/-- The exact residue after applying the unconditional `l` wall, the
`B = 0` beta wall, the pure gamma and delta walls, and the completed
effective-load assembly. -/
def EarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (B : k[X]) : Prop :=
  (beta ≠ 0 ∧ B ≠ 0) ∨
  (beta = 0 ∧ gamma ≠ 0 ∧
    (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0)) ∨
  (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
    (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

/-- Exhaustive wall reduction at the polynomial trajectory interface.
Every surviving trajectory has `l = 0` and lies in exactly one of the three
unclosed early-load cones recorded by `EarlyLoadResidual410`. -/
theorem constantIntegral410_earlyLoad_exhaustive_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota k2 k1
      terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k1)
    (hLower : lowerRowZeroPolynomial410
      (integratedWPolynomial410 l alpha beta gamma delta epsilon zeta theta
        A B C0)
      (integratedZPolynomial410 l alpha beta gamma delta epsilon zeta eta
        iota A B C0) B C0 = C terminal) :
    l = 0 ∧ EarlyLoadResidual410 beta gamma delta zeta eta theta B := by
  have hl : l = 0 := by
    by_contra hlne
    exact lWall410_unconditional_original_impossible
      l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
        A B C0 hlne hterminal hTwo hOne hLower
  refine ⟨hl, ?_⟩
  by_cases hbeta : beta = 0
  · by_cases hgamma : gamma = 0
    · by_cases hdelta : delta = 0
      · subst l
        subst beta
        subst gamma
        subst delta
        exact (scaleZero410_polynomial_trajectory_impossible
          alpha epsilon zeta eta theta iota k2 k1 terminal A B C0
            hterminal hTwo hOne hLower).elim
      · right
        right
        refine ⟨hbeta, hgamma, hdelta, ?_⟩
        subst l
        subst beta
        subst gamma
        exact deltaWall410_laterEffectiveLoad_residual
          alpha delta epsilon zeta eta theta iota k2 k1 terminal
            A B C0 hterminal hTwo hOne hLower
    · right
      left
      refine ⟨hbeta, hgamma, ?_⟩
      subst l
      subst beta
      exact gammaWall410_laterEffectiveLoad_residual
        alpha gamma delta epsilon zeta eta theta iota k2 k1 terminal
          A B C0 hterminal hTwo hOne hLower
  · left
    refine ⟨hbeta, ?_⟩
    intro hB
    subst l
    subst B
    exact betaWall410_B_eq_zero_impossible
      0 alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
        A C0 rfl hbeta hterminal hTwo hOne hLower

/-- Rational fully integrated brackets inherit the exact polynomial
early-load residual.  This is the reusable target of the still-missing
ground-constant integration adapter. -/
theorem integrated410_earlyLoad_exhaustive_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket :
      differentialJacobian ratFuncDerivation46
        (depressedQuartic46
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0))
        (depressedDecic410 (RatFunc.C l)
          (integratedP410 (algebraMap k[X] (RatFunc k) A)
            (RatFunc.C alpha))
          (integratedQ410 (RatFunc.C l)
            (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B) (RatFunc.C beta))
          (integratedR410 (RatFunc.C l)
            (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0)
            (RatFunc.C alpha) (RatFunc.C gamma))
          (integratedS410 (RatFunc.C l)
            (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0)
            (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C delta))
          (integratedT410 (RatFunc.C l)
            (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0)
            (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
            (RatFunc.C epsilon))
          (integratedU410 (RatFunc.C l)
            (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0)
            (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
            (RatFunc.C delta) (RatFunc.C zeta))
          (integratedV410 (RatFunc.C l)
            (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0)
            (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
            (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C eta))
          (integratedW410 (RatFunc.C l)
            (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0)
            (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
            (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
            (RatFunc.C theta))
          (integratedZ410 (RatFunc.C l)
            (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0)
            (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
            (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
            (RatFunc.C eta) (RatFunc.C iota))) = C (RatFunc.C terminal)) :
    l = 0 ∧ EarlyLoadResidual410 beta gamma delta zeta eta theta B := by
  have hconst (c : k) : ratFuncDerivation46 (RatFunc.C c) = 0 := by
    have hp := ratFuncDerivation46_polynomial (C c : k[X])
    simpa [RatFunc.algebraMap_C] using hp
  obtain ⟨hTwo, hOne, hLower⟩ :=
    integrated410_lowerSystem_of_constantBracket
      (k := k) (F := RatFunc k) ratFuncDerivation46
      (RatFunc.C l) (algebraMap k[X] (RatFunc k) A)
      (algebraMap k[X] (RatFunc k) B)
      (algebraMap k[X] (RatFunc k) C0)
      (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
      (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
      (RatFunc.C eta) (RatFunc.C theta) (RatFunc.C iota)
      (RatFunc.C terminal)
      (hconst l) (hconst alpha) (hconst beta) (hconst gamma)
      (hconst delta) (hconst epsilon) (hconst zeta) (hconst eta)
      (hconst theta) (hconst iota) hbracket
  obtain ⟨k2, k1, hTwoPoly, hOnePoly⟩ :=
    polynomialFirstIntegrals410_exist_constants
      (k := k) l beta gamma delta zeta eta theta A B C0 hTwo hOne
  have hLowerMapped :
      algebraMap k[X] (RatFunc k)
          (integratedWPolynomial410 l alpha beta gamma delta epsilon zeta
            theta A B C0) *
          ratFuncDerivation46 (algebraMap k[X] (RatFunc k) C0) -
        algebraMap k[X] (RatFunc k) B *
          ratFuncDerivation46
            (algebraMap k[X] (RatFunc k)
              (integratedZPolynomial410 l alpha beta gamma delta epsilon
                zeta eta iota A B C0)) = RatFunc.C terminal := by
    rw [algebraMap_integratedWPolynomial410,
      algebraMap_integratedZPolynomial410]
    exact hLower
  have hLowerPoly := polynomial_lowerRow410_eq_constant_of_ratFunc
    (k := k)
    (integratedWPolynomial410 l alpha beta gamma delta epsilon zeta theta
      A B C0)
    (integratedZPolynomial410 l alpha beta gamma delta epsilon zeta eta iota
      A B C0) B C0 terminal hLowerMapped
  exact constantIntegral410_earlyLoad_exhaustive_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwoPoly hOnePoly hLowerPoly

/-- The remaining source-transport lemma is now only ground integration of
the ten depressed decic coefficients.  Unlike the previous early-zero
interface, it does not assert any load vanishing. -/
def ScaleZero410GroundIntegrationBridge : Prop :=
  ∀ (terminal : k) (A B C0 L P Q R S T U V W Z : k[X]),
    terminal ≠ 0 →
    differentialJacobian ratFuncDerivation46
      (depressedQuartic46
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0))
      (depressedDecic410
        (algebraMap k[X] (RatFunc k) L)
        (algebraMap k[X] (RatFunc k) P)
        (algebraMap k[X] (RatFunc k) Q)
        (algebraMap k[X] (RatFunc k) R)
        (algebraMap k[X] (RatFunc k) S)
        (algebraMap k[X] (RatFunc k) T)
        (algebraMap k[X] (RatFunc k) U)
        (algebraMap k[X] (RatFunc k) V)
        (algebraMap k[X] (RatFunc k) W)
        (algebraMap k[X] (RatFunc k) Z)) = C (RatFunc.C terminal) →
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota : k,
      differentialJacobian ratFuncDerivation46
        (depressedQuartic46
          (algebraMap k[X] (RatFunc k) A)
          (algebraMap k[X] (RatFunc k) B)
          (algebraMap k[X] (RatFunc k) C0))
        (depressedDecic410 (RatFunc.C l)
          (integratedP410 (algebraMap k[X] (RatFunc k) A)
            (RatFunc.C alpha))
          (integratedQ410 (RatFunc.C l)
            (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B) (RatFunc.C beta))
          (integratedR410 (RatFunc.C l)
            (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0)
            (RatFunc.C alpha) (RatFunc.C gamma))
          (integratedS410 (RatFunc.C l)
            (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0)
            (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C delta))
          (integratedT410 (RatFunc.C l)
            (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0)
            (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
            (RatFunc.C epsilon))
          (integratedU410 (RatFunc.C l)
            (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0)
            (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
            (RatFunc.C delta) (RatFunc.C zeta))
          (integratedV410 (RatFunc.C l)
            (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0)
            (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
            (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C eta))
          (integratedW410 (RatFunc.C l)
            (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0)
            (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
            (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
            (RatFunc.C theta))
          (integratedZ410 (RatFunc.C l)
            (algebraMap k[X] (RatFunc k) A)
            (algebraMap k[X] (RatFunc k) B)
            (algebraMap k[X] (RatFunc k) C0)
            (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
            (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
            (RatFunc.C eta) (RatFunc.C iota))) = C (RatFunc.C terminal)

variable [IsAlgClosed k]

/-- Source-facing exact reduction.  Once the mechanical ground-integration
bridge is supplied, every normalized scale-zero source lands in the explicit
three-leaf early-load residual and nowhere else. -/
theorem normalized410ScaleZero_earlyLoad_exhaustive_residual
    (hground : ScaleZero410GroundIntegrationBridge (k := k))
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          EarlyLoadResidual410 beta gamma delta zeta eta theta B := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hbracket⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    hground terminal A B C0 L P1 Q1 R S T U V W Z hterminal hbracket
  have hresidual := integrated410_earlyLoad_exhaustive_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal hintegrated
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hresidual.1, hresidual.2⟩

end EarlyLoadElimination410

end Max11DegreeRoutes
