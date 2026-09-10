import Grok810ScaleZeroQuarticSigmaLadderPart94Scratch

/-! Part 95 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

variable {k : Type*} [Field k] [CharZero k]

section QuarticSigmaLadderAssembly810

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]


set_option maxHeartbeats 64000000 in
/-- Honest leftover after File A of the σ-defect ladder.

Closed relative to `quarticConeA810_residual`: the 67-way
`QuarticSigmaSupportCone810` (all-zero leaf killed by
`quarticADominant_allLettersZero_impossible`), the kappa `l`
column implication `QuarticKappaLoadTopL810 → l = 0`, and the
`l` band disjunction of §2.2.  The 63 σ-cones and the four mixed
residual cones `QuarticMixedSigmaCone{BF,BG,CF,CG}810` are not
killed (Files B/C).  Corner H is not closed.  Named unclosable
sub-chamber: `B = 0 ∧ s ≥ 4a ∧ S ⊆ {C,D,E} ∧ γ ≠ 0`.
Next unused row: kappa rest bounds for `β/δ/ζ` and `N₂` kills
on the three k=3 cones, then per-cone letter-face rest bounds.
No finite-root shortcut. -/
theorem normalized810ScaleZero_quarticSigmaResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t j lambda cleared l beta gamma delta epsilon zeta eta theta
        cXi cMu cOm : k) (A B C D E F G : k[X]),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      derivative
          (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
            eta theta A B C D E F G) =
        Polynomial.C (j / t) ∧
      (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree = 0 ∧
      (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree = 0 ∧
      (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0 ∧
      (
        (QuarticRatioConeA810 A B C D E F G ∧
          QuarticSigmaSupportCone810 A B C D E F G ∧
          (QuarticKappaLoadTopL810 A B C D E F G → l = 0) ∧
          (l = 0 ∨
      5 * A.natDegree ≤ 4 * B.natDegree ∨
      7 * A.natDegree ≤ 4 * C.natDegree ∨
      9 * A.natDegree ≤ 4 * D.natDegree ∨
      11 * A.natDegree ≤ 4 * E.natDegree ∨
      13 * A.natDegree ≤ 4 * F.natDegree ∨
      15 * A.natDegree ≤ 4 * G.natDegree) ∧
          ((l = 0 ∧ beta = 0 ∧ delta = 0 ∧ zeta = 0) ∨
            ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
                E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0)) ∧
          ¬ (B = 0 ∧ D = 0 ∧ F = 0 ∧ 0 < C.natDegree ∧
              2 * E.natDegree < 3 * C.natDegree ∧
              G.natDegree < 2 * C.natDegree) ∧
          ¬ (B = 0 ∧ D = 0 ∧ F = 0 ∧ 0 < E.natDegree ∧
              3 * C.natDegree < 2 * E.natDegree ∧
              3 * G.natDegree < 2 * E.natDegree)) ∨
        QuarticRatioConeABCDEFG810 A B C D E F G) := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
      eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv,
      hHsq, hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, hdisj⟩ :=
    quarticConeA810_residual hsource
  refine ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
    eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv, hHsq,
    hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, ?_⟩
  rcases hdisj with hA | hABCDEFG
  · rcases hA with ⟨hconeA, hconst, hevenC, hevenE⟩
    refine Or.inl ⟨hconeA, ?hexh, ?hl, ?hlB, hconst, hevenC, hevenE⟩
    · exact quarticSigmaSupportCone810_of l beta gamma delta epsilon zeta
        eta theta A B C D E F G hconeA hjdiv hder
    · intro htop
      exact quarticSigma_l_eq_zero l beta gamma delta epsilon zeta eta
        theta A B C D E F G htop hkapDeg
    · exact quarticSigma_l_band_disjunction (l := l) A B C D E F G hconeA
        (fun htop => quarticSigma_l_eq_zero l beta gamma delta epsilon
          zeta eta theta A B C D E F G htop hkapDeg)
  · exact Or.inr hABCDEFG


end QuarticSigmaLadderAssembly810
end Max11DegreeRoutes
end
