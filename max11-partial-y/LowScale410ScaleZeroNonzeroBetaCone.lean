import LowScale410ScaleZeroGroundIntegration

/-!
# The nonzero-beta Newton packet for the scale-zero `(4,10)` source

After `l = 0`, the beta parts of the two first integrals have small
denominator-free cores.  This file proves that neither beta core can be a
unique positive-degree Newton face against the zero-load curve and the
strictly later loads.  For the second invariant the beta face factors by
`B`; hence on the surviving `B != 0` cone its only algebraic degeneration is
the explicit cubic wall below.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Polynomial
open scoped Polynomial.Bivariate

namespace Max11DegreeRoutes

section NonzeroBetaCone410

variable {k : Type*} [Field k] [CharZero k]

/-- Denominator-free beta face of the first (`z^2`) invariant. -/
def betaTwoCorePolynomial410 (A B C0 : k[X]) : k[X] :=
  (5 : k) • A ^ 4 - (48 : k) • (A ^ 2 * C0) -
    (48 : k) • (A * B ^ 2) + (192 : k) • C0 ^ 2

/-- The cubic core left after factoring `B` from the beta face of the
second (`z`) invariant. -/
def betaOneCorePolynomial410 (A B C0 : k[X]) : k[X] :=
  (5 : k) • A ^ 3 - (24 : k) • (A * C0) - (4 : k) • B ^ 2

theorem betaLoadTwoPolynomial410_eq_core
    (beta : k) (A B C0 : k[X]) :
    betaLoadTwoPolynomial410 beta A B C0 =
      (7 / 512 * beta : k) • betaTwoCorePolynomial410 A B C0 := by
  simp only [betaLoadTwoPolynomial410, betaTwoCorePolynomial410]
  module

theorem betaLoadOnePolynomial410_eq_core
    (beta : k) (A B C0 : k[X]) :
    betaLoadOnePolynomial410 beta A B C0 =
      (7 / 128 * beta : k) •
        (B * betaOneCorePolynomial410 A B C0) := by
  have h35 : (35 / 128 * beta : k) = (7 / 128 * beta) * 5 := by ring
  have h21 : (21 / 16 * beta : k) = (7 / 128 * beta) * 24 := by ring
  have h7 : (7 / 32 * beta : k) = (7 / 128 * beta) * 4 := by ring
  simp only [betaLoadOnePolynomial410, betaOneCorePolynomial410,
    h35, h21, h7, Polynomial.smul_eq_C_mul]
  simp only [map_mul]
  ring

/-- Exact finite Newton residue on the `beta != 0`, `B != 0` cone.

Each clause says that the corresponding beta core either vanishes, has
degree zero, or is not above both the zero-load face and every later load.
Thus the packet removes both open chambers in which beta alone is the top
face, without assuming that any later load vanishes. -/
def NonzeroBetaNewtonResidual410
    (gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (betaTwoCorePolynomial410 A B C0 = 0 ∨
      (betaTwoCorePolynomial410 A B C0).natDegree = 0 ∨
      (betaTwoCorePolynomial410 A B C0).natDegree ≤
        max
          (firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
          (betaLoadTwoRest410 gamma delta zeta eta theta A B C0).natDegree) ∧
    (betaOneCorePolynomial410 A B C0 = 0 ∨
      B.natDegree + (betaOneCorePolynomial410 A B C0).natDegree = 0 ∨
      B.natDegree + (betaOneCorePolynomial410 A B C0).natDegree ≤
        max
          (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0).natDegree
          (betaLoadOneRest410 gamma delta zeta eta theta A B C0).natDegree)

/-- Constant first integrals exclude both unique-beta Newton chambers.  The
conclusion is independent of `alpha`, `epsilon`, `iota`, and the terminal
row; those data re-enter only in the source-facing exhaustive assembly. -/
theorem constantIntegrals410_nonzeroBeta_newton_residual
    (l beta gamma delta zeta eta theta k2 k1 : k) (A B C0 : k[X])
    (hl : l = 0) (hbeta : beta ≠ 0) (hB : B ≠ 0)
    (hTwo : firstIntegralTwoPolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k2)
    (hOne : firstIntegralOnePolynomial410
      l beta gamma delta zeta eta theta A B C0 = C k1) :
    NonzeroBetaNewtonResidual410 gamma delta zeta eta theta A B C0 := by
  subst l
  constructor
  · by_cases hcore : betaTwoCorePolynomial410 A B C0 = 0
    · exact Or.inl hcore
    · right
      by_cases hdegree :
          (betaTwoCorePolynomial410 A B C0).natDegree = 0
      · exact Or.inl hdegree
      · right
        by_contra hle
        have hstrict :
            max
                (firstIntegralTwoPolynomial410 0 0 0 0 0 0 0
                  A B C0).natDegree
                (betaLoadTwoRest410 gamma delta zeta eta theta
                  A B C0).natDegree <
              (betaTwoCorePolynomial410 A B C0).natDegree := by
          omega
        have hrest :
            (firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0 +
                betaLoadTwoRest410 gamma delta zeta eta theta A B C0).natDegree <
              (betaTwoCorePolynomial410 A B C0).natDegree := by
          exact (natDegree_add_le _ _).trans_lt (by omega)
        have heq :
            (7 / 512 * beta : k) • betaTwoCorePolynomial410 A B C0 +
                (firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0 +
                  betaLoadTwoRest410 gamma delta zeta eta theta A B C0) =
              C k2 := by
          rw [firstIntegralTwoPolynomial410_eq_zero_add_loadCorrection,
            loadCorrectionTwoPolynomial410_eq_beta_add_rest,
            betaLoadTwoPolynomial410_eq_core] at hTwo
          simpa only [add_assoc, add_left_comm, add_comm] using hTwo
        exact (smul_add_lower_ne_C410
          (7 / 512 * beta) k2 (betaTwoCorePolynomial410 A B C0)
          (firstIntegralTwoPolynomial410 0 0 0 0 0 0 0 A B C0 +
            betaLoadTwoRest410 gamma delta zeta eta theta A B C0)
          (betaTwoCorePolynomial410 A B C0).natDegree
          (mul_ne_zero (by norm_num) hbeta) hcore (by omega) rfl hrest) heq
  · by_cases hcore : betaOneCorePolynomial410 A B C0 = 0
    · exact Or.inl hcore
    · right
      by_cases hdegree :
          B.natDegree + (betaOneCorePolynomial410 A B C0).natDegree = 0
      · exact Or.inl hdegree
      · right
        by_contra hle
        have hstrict :
            max
                (firstIntegralOnePolynomial410 0 0 0 0 0 0 0
                  A B C0).natDegree
                (betaLoadOneRest410 gamma delta zeta eta theta
                  A B C0).natDegree <
              B.natDegree +
                (betaOneCorePolynomial410 A B C0).natDegree := by
          omega
        have hrest :
            (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0 +
                betaLoadOneRest410 gamma delta zeta eta theta A B C0).natDegree <
              B.natDegree +
                (betaOneCorePolynomial410 A B C0).natDegree := by
          exact (natDegree_add_le _ _).trans_lt (by omega)
        have hmonomial :
            (B * betaOneCorePolynomial410 A B C0).natDegree =
              B.natDegree +
                (betaOneCorePolynomial410 A B C0).natDegree := by
          rw [natDegree_mul hB hcore]
        have heq :
            (7 / 128 * beta : k) •
                  (B * betaOneCorePolynomial410 A B C0) +
                (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0 +
                  betaLoadOneRest410 gamma delta zeta eta theta A B C0) =
              C k1 := by
          rw [firstIntegralOnePolynomial410_eq_zero_add_loadCorrection,
            loadCorrectionOnePolynomial410_eq_beta_add_rest,
            betaLoadOnePolynomial410_eq_core] at hOne
          simpa only [add_assoc, add_left_comm, add_comm] using hOne
        exact (smul_add_lower_ne_C410
          (7 / 128 * beta) k1
          (B * betaOneCorePolynomial410 A B C0)
          (firstIntegralOnePolynomial410 0 0 0 0 0 0 0 A B C0 +
            betaLoadOneRest410 gamma delta zeta eta theta A B C0)
          (B.natDegree + (betaOneCorePolynomial410 A B C0).natDegree)
          (mul_ne_zero (by norm_num) hbeta) (mul_ne_zero hB hcore)
          (by omega) hmonomial hrest) heq

/-- The exact early-load residue with its first leaf sharpened by the two
Newton exclusions above. -/
def RefinedEarlyLoadResidual410
    (beta gamma delta zeta eta theta : k) (A B C0 : k[X]) : Prop :=
  (beta ≠ 0 ∧ B ≠ 0 ∧
      NonzeroBetaNewtonResidual410 gamma delta zeta eta theta A B C0) ∨
    (beta = 0 ∧ gamma ≠ 0 ∧
      (delta ≠ 0 ∨ zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0)) ∨
    (beta = 0 ∧ gamma = 0 ∧ delta ≠ 0 ∧
      (zeta ≠ 0 ∨ eta ≠ 0 ∨ theta ≠ 0))

/-- Polynomial trajectory assembly: every nonzero-beta survivor satisfies
the exact two-core Newton packet, while the two later-load leaves are
unchanged. -/
theorem constantIntegral410_refined_earlyLoad_residual
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
      RefinedEarlyLoadResidual410 beta gamma delta zeta eta theta A B C0 := by
  have hold := constantIntegral410_earlyLoad_exhaustive_residual
    l alpha beta gamma delta epsilon zeta eta theta iota k2 k1 terminal
      A B C0 hterminal hTwo hOne hLower
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hbeta | hlater
  · left
    exact ⟨hbeta.1, hbeta.2,
      constantIntegrals410_nonzeroBeta_newton_residual
        l beta gamma delta zeta eta theta k2 k1 A B C0 hold.1
          hbeta.1 hbeta.2 hTwo hOne⟩
  · exact Or.inr hlater

/-- Compact name for the fully ground-integrated constant bracket used by
the source-facing refinement below. -/
def GroundIntegratedConstantBracket410
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) : Prop :=
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

/-- A fully integrated bracket inherits the refined early-load packet. -/
theorem integrated410_refined_earlyLoad_residual
    (l alpha beta gamma delta epsilon zeta eta theta iota terminal : k)
    (A B C0 : k[X]) (hterminal : terminal ≠ 0)
    (hbracket : GroundIntegratedConstantBracket410
      l alpha beta gamma delta epsilon zeta eta theta iota terminal A B C0) :
    l = 0 ∧
      RefinedEarlyLoadResidual410 beta gamma delta zeta eta theta A B C0 := by
  have hold := integrated410_earlyLoad_exhaustive_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal (by simpa [GroundIntegratedConstantBracket410]
        using hbracket)
  refine ⟨hold.1, ?_⟩
  rcases hold.2 with hbeta | hlater
  · left
    refine ⟨hbeta.1, hbeta.2, ?_⟩
    have hconst (c : k) : ratFuncDerivation46 (RatFunc.C c) = 0 := by
      have hp := ratFuncDerivation46_polynomial (C c : k[X])
      simpa [RatFunc.algebraMap_C] using hp
    obtain ⟨hTwo, hOne, _hLower⟩ :=
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
    exact constantIntegrals410_nonzeroBeta_newton_residual
      l beta gamma delta zeta eta theta k2 k1 A B C0 hold.1
        hbeta.1 hbeta.2 hTwoPoly hOnePoly
  · exact Or.inr hlater

variable [IsAlgClosed k]

/-- Raw normalized scale-zero sources land in the refined packet.  Ground
integration is supplied by the canonical mechanical bridge; no load
vanishing is inserted in this adapter. -/
theorem normalized410ScaleZero_refined_earlyLoad_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 0) :
    ∃ l alpha beta gamma delta epsilon zeta eta theta iota terminal : k,
      ∃ A B C0 : k[X],
        terminal ≠ 0 ∧ l = 0 ∧
          RefinedEarlyLoadResidual410 beta gamma delta zeta eta theta
            A B C0 := by
  obtain ⟨terminal, A, B, C0, L, P1, Q1, R, S, T, U, V, W, Z,
      hterminal, hraw⟩ :=
    normalized410ScaleZero_exists_depressedPolynomialBracket hsource
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
      hintegrated⟩ :=
    scaleZero410_groundIntegrationBridge
      terminal A B C0 L P1 Q1 R S T U V W Z hterminal hraw
  have hrefined := integrated410_refined_earlyLoad_residual
    l alpha beta gamma delta epsilon zeta eta theta iota terminal
      A B C0 hterminal
      (by simpa [GroundIntegratedConstantBracket410] using hintegrated)
  exact ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, theta, iota,
    terminal, A, B, C0, hterminal, hrefined.1, hrefined.2⟩

end NonzeroBetaCone410

end Max11DegreeRoutes
