import LowScale410ScaleZeroBetaCubicBalancedWall

/-!
# Deleting the beta-cubic leaf from the scale-zero source packet

The completed cubic-wall theorem removes the algebraic degeneration in the
nonzero-beta Newton packet.  What remains is a genuinely noncubic `I1` beta
face, split exactly into its degree-zero component and its degree-competition
component.  This refinement is transported through the fully integrated
bracket and back to the raw normalized source.  No later load vanishes.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section CubicDeletedEarlyLoad410

variable {k : Type*} [Field k] [CharZero k]

/-- The genuine noncubic beta packet.  The first conjunct is the unchanged
`I2` beta-core Newton residue.  The second records that the factored `I1`
core is nonzero and is either literally degree zero (together with `B`) or
is bounded by a zero-load/later-load competitor. -/
def NoncubicBetaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (betaTwoCorePolynomial410 A B C0 = 0 ∨
      (betaTwoCorePolynomial410 A B C0).natDegree = 0 ∨
      (betaTwoCorePolynomial410 A B C0).natDegree ≤
        max
          (firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
          (betaLoadTwoRest410 gamma delta zeta eta theta A B C0).natDegree) ∧
    betaOneCorePolynomial410 A B C0 ≠ 0 ∧
      ((B.natDegree = 0 ∧
          (betaOneCorePolynomial410 A B C0).natDegree = 0) ∨
        B.natDegree + (betaOneCorePolynomial410 A B C0).natDegree ≤
          max
            (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
            (betaLoadOneRest410 gamma delta zeta eta theta A B C0).natDegree)

/-- Early-load selector after deleting the complete beta-cubic wall. -/
def CubicDeletedEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta ≠ 0 ∧ B ≠ 0 ∧
      NoncubicBetaNewtonResidual410 gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0)) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

/-- Polynomial trajectory assembly with the entire cubic leaf removed. -/
theorem constantIntegral410_cubicDeleted_earlyLoad_residual
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
    l = 0 ∧
      CubicDeletedEarlyLoadResidual410 beta gamma delta zeta eta theta
        A B C0 := by
  have hold := constantIntegral410_refined_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hbeta | hlater
  · left
    refine ⟨hbeta.1, hbeta.2.1, ?_⟩
    have hTwo0 : firstIntegralTwoPolynomial410
        0 beta gamma delta zeta eta theta A B C0 = C k2 := by
      simpa [hold.1] using hTwo
    have hOne0 : firstIntegralOnePolynomial410
        0 beta gamma delta zeta eta theta A B C0 = C k1 := by
      simpa [hold.1] using hOne
    have hLower0 : lowerRowZeroPolynomial410
        (integratedWPolynomial410 0 alpha beta gamma delta epsilon zeta theta
          A B C0)
        (integratedZPolynomial410 0 alpha beta gamma delta epsilon zeta eta
          iota A B C0) B C0 = C terminal := by
      simpa [hold.1] using hLower
    have hnoncubic : betaOneCorePolynomial410 A B C0 ≠ 0 := by
      intro hwall
      exact constantIntegral410_betaCubicWall_impossible
        alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
          A B C0 hbeta.2.1 hterminal hwall hTwo0 hOne0 hLower0
    rcases hbeta.2.2 with ⟨hTwoCore, hOneCore⟩
    refine ⟨hTwoCore, hnoncubic, ?_⟩
    rcases hOneCore with hwall | hzero | hbound
    · exact (hnoncubic hwall).elim
    · exact Or.inl (Nat.add_eq_zero.mp hzero)
    · exact Or.inr hbound
  · exact Or.inr hlater

/-! ## Integrated and source-facing transport -/

/-- A ground-integrated bracket supplies both polynomial first integrals and
the exact polynomial terminal row. -/
theorem groundIntegratedBracket410_exists_polynomialLowerSystem
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X])
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    ∃ k2 k1 : k,
      firstIntegralTwoPolynomial410
          l beta gamma delta zeta eta theta A B C0 = C k2 ∧
        firstIntegralOnePolynomial410
          l beta gamma delta zeta eta theta A B C0 = C k1 ∧
        lowerRowZeroPolynomial410
          (integratedWPolynomial410 l alpha beta gamma delta epsilon zeta
            theta A B C0)
          (integratedZPolynomial410 l alpha beta gamma delta epsilon zeta eta
            iota A B C0) B C0 = C terminal := by
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
      (hconst theta) (hconst iota)
      (by simpa [GroundIntegratedConstantBracket410] using hbracket)
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
  exact ⟨k2, k1, hTwoPoly, hOnePoly, hLowerPoly⟩

/-- Fully integrated brackets inherit the cubic-deleted selector. -/
theorem integrated410_cubicDeleted_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      CubicDeletedEarlyLoadResidual410 beta gamma delta zeta eta theta
        A B C0 := by
  obtain ⟨k2, k1, hTwo, hOne, hLower⟩ :=
    groundIntegratedBracket410_exists_polynomialLowerSystem
      l alpha beta gamma delta epsilon zeta eta theta iota terminal
        A B C0 hbracket
  exact constantIntegral410_cubicDeleted_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower

variable [IsAlgClosed k]

/-- Raw normalized scale-zero sources land in the cubic-deleted packet. -/
theorem normalized410ScaleZero_cubicDeleted_earlyLoad_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          CubicDeletedEarlyLoadResidual410 beta gamma delta zeta eta theta
            A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_cubicDeleted_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end CubicDeletedEarlyLoad410

end Max11DegreeRoutes
