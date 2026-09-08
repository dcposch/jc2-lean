import LowScale68ScaleZeroAssembly
import LowScale68SecondaryResidualStripSelector
import LowScale68SecondaryResidualThreeGapBoundarySelector
import LowScale68SecondaryFirstGapBoundary
import LowScale68SecondaryLargeGapClosure
import LowScale68SecondaryAlphaWallBalancedRowZero
import LowScale68SecondaryDeepGapMiddleRightEndgame
import Sol68LaterDeepLowerParentFiveToSixGlobalSourceClosureScratch

/-! # Exact global residual for the normalized scale-zero `(6,8)` source

Every secondary-gap chamber below the later-deep wall is already empty.  The
later-deep selector therefore enters the five-to-six stride packet.  The
verified offset-120 source theorem deletes `(n,g)=(120,360)`, but the
normalized source interface has no transverse-degree bound, so larger radii
cannot be discarded.  This file records the resulting exact source-facing
residual without adding such a bound.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section ScaleZeroGlobalResidual68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Arithmetic inventory after the full-stride divisibility and the deletion
of the exact `(120,360)` wall.  The four alternatives are exhaustive. -/
theorem fiveToSix_radius_inventory_after_oneTwenty68
    (n g : ℕ) (hn : 30 ∣ n) (hg : 30 ∣ g) (hnlarge : 30 < n)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hnotwall : ¬ (n = 120 ∧ g = 360)) :
    (n = 60 ∧ g = 180) ∨
      (n = 90 ∧ (g = 240 ∨ g = 270)) ∨
      (n = 120 ∧ g = 330) ∨ 120 < n := by
  obtain ⟨N, rfl⟩ := hn
  obtain ⟨G, rfl⟩ := hg
  omega

/-- The strongest currently source-backed survivor of the global secondary
selector.  It contains the full first stride, the exact offset-90 split, the
deletion of the offset-120 load wall, and the remaining radius inventory. -/
def FiveToSixGlobalResidual68
    (zeta : k) (A B c D e d : k[X]) (n g : ℕ) : Prop :=
  5 * n < 2 * g ∧ 2 * g ≤ 6 * n ∧
    firstSecondaryFour68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 ∧
    firstSecondaryThree68
      (A.coeff (2 * n)) (B.coeff (3 * n - g))
      (c.coeff (4 * n - g)) (D.coeff (5 * n - g))
      (e.coeff (6 * n - g)) = 0 ∧
    30 ∣ n ∧ 30 ∣ g ∧ 30 < n ∧
    (∀ s, 1 ≤ s → s < 60 →
      d.coeff (5 * n - g - s) = 0 ∧
      e.coeff (6 * n - g - s) = 0) ∧
    d.natDegree ≤ 5 * n - g - 60 ∧
    e.natDegree ≤ 6 * n - g - 60 ∧
    (((n = 60 ∧ g = 180 ∧ zeta = 0) ∨ 60 < n) ∧
      ((d.coeff (5 * n - g - 60) = 0 ∧
          e.coeff (6 * n - g - 60) = 0 ∧
          d.natDegree ≤ 5 * n - g - 120 ∧
          e.natDegree ≤ 6 * n - g - 120 ∧
          (n = 90 ∧ g = 270 → zeta = 0)) ∨
        (60 ∣ n ∧ 60 ∣ g ∧
          B.coeff (3 * n - g) ≠ 0 ∧
          c.coeff (4 * n - g) ≠ 0 ∧
          d.coeff (5 * n - g - 60) ≠ 0 ∧
          e.coeff (6 * n - g - 60) ≠ 0 ∧
          A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
            3 * c.coeff (4 * n - g) ^ 2 = 0 ∧
          d.coeff (5 * n - g - 90) = 0 ∧
          e.coeff (6 * n - g - 90) = 0))) ∧
    ¬ (n = 120 ∧ g = 360) ∧
    ((n = 60 ∧ g = 180) ∨
      (n = 90 ∧ (g = 240 ∨ g = 270)) ∨
      (n = 120 ∧ g = 330) ∨ 120 < n)

/-- Exhaustive global selector for an arbitrary nonzero integrated lower
system.  All chambers before `3n ≤ 2g` are discharged by their verified
closures; the later-deep branch is then reduced to
`FiveToSixGlobalResidual68`. -/
theorem integratedPolynomialLowerSystem68_global_fiveToSix_residual
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
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
    FiveToSixGlobalResidual68 zeta Ae Be ce De ee d n g := by
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
  change FiveToSixGlobalResidual68 zeta Ae Be ce De ee d n g
  have hlater : 3 * n ≤ 2 * g := by
    by_contra hnot
    have hbelow : 2 * g < 3 * n := by omega
    rcases lt_trichotomy (2 * g) n with hsmall | hhalf | hlarge
    · rcases lt_trichotomy n (3 * g) with hstrip | hthree | htiny
      · exact False.elim
          (maximalExpandedIntegratedPolynomialLowerSystem_residualStrictStrip_impossible68
            l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
            hterminal hsys (by
              simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
                (⟨hsmall, hstrip⟩ : 2 * g < n ∧ n < 3 * g)))
      · exact False.elim
          (maximalExpandedIntegratedPolynomialLowerSystem_residualThreeGapBoundary_impossible68
            l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
            hterminal hsys (by
              simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hthree))
      · exact False.elim
          (maximalExpandedIntegratedPolynomialLowerSystem_secondaryResidualSmallChamber_impossible68
            l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
            hterminal hsys (by
              simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using htiny))
    · exact False.elim
        (maximalExpandedIntegratedPolynomialLowerSystem_firstGapBoundary_impossible68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
          hterminal hsys (by
            simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hhalf))
    · rcases lt_trichotomy g n with hgap | hwall | hdeep
      · exact False.elim
          (maximalExpandedIntegratedPolynomialLowerSystem_largeGapLoadZero_impossible68
            l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
            hterminal hsys (by
              simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
                (⟨hlarge, hgap⟩ : n < 2 * g ∧ g < n)))
      · exact False.elim
          (maximalExpandedIntegratedPolynomialLowerSystem_alphaWallImpossible68
            l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
            hterminal hsys (by
              simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall))
      · exact False.elim
          (maximalExpandedIntegratedPolynomialLowerSystem_deepGapFirst_impossible68
            l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
            hterminal hsys (by
              simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using
                (⟨hdeep, hbelow⟩ : n < g ∧ 2 * g < 3 * n)))
  have hparent :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_forces_fiveToSixStride68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlater)
  change 5 * n < 2 * g ∧ 2 * g ≤ 6 * n ∧ _ = 0 ∧ _ = 0 ∧
    30 ∣ n ∧ 30 ∣ g ∧ 30 < n ∧ _ ∧
    d.natDegree ≤ 5 * n - g - 60 ∧
    ee.natDegree ≤ 6 * n - g - 60 at hparent
  have hoffset :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_offsetNinetyPacket68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlater)
  change (((n = 60 ∧ g = 180 ∧ zeta = 0) ∨ 60 < n) ∧
      ((_ ∧ _ ∧ _ ∧ _ ∧ _) ∨
        (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))) at hoffset
  have hnotwall : ¬ (n = 120 ∧ g = 360) := by
    intro hwall
    exact
      maximalExpandedIntegratedPolynomialLowerSystem_offsetOneTwenty_source_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlater)
        (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hwall)
  have hinventory := fiveToSix_radius_inventory_after_oneTwenty68 n g
    hparent.2.2.2.2.1 hparent.2.2.2.2.2.1 hparent.2.2.2.2.2.2.1
    ⟨hparent.1, hparent.2.1⟩ hnotwall
  exact ⟨hparent.1, hparent.2.1, hparent.2.2.1, hparent.2.2.2.1,
    hparent.2.2.2.2.1, hparent.2.2.2.2.2.1,
    hparent.2.2.2.2.2.2.1, hparent.2.2.2.2.2.2.2.1,
    hparent.2.2.2.2.2.2.2.2.1, hparent.2.2.2.2.2.2.2.2.2,
    hoffset, hnotwall, hinventory⟩

/-- Literal normalized scale-zero source reduction.  This is the exact
upstream statement justified by the current closure graph: a source produces
an integrated system in the displayed five-to-six residual. -/
theorem normalized68ScaleZero_global_fiveToSix_residual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 0) :
    ∃ (l alpha beta gamma delta epsilon zeta eta terminal : k)
        (A B C0 D E : k[X]),
      terminal ≠ 0 ∧
      IntegratedPolynomialLowerSystem68 l alpha beta gamma delta epsilon zeta
        eta terminal A B C0 D E ∧
      (let n := weightedRadius68 A B C0 D E
       let Ae := expand k 60 A
       let Be := expand k 60 B
       let Ce := expand k 60 C0
       let ce := cubicCDefectPolynomial68 Ae Ce
       let De := expand k 60 D
       let Ee := expand k 60 E
       let ee := cubicEDefectPolynomial68 Ae Ce Ee
       let g := cubicDefectGap68 n Be ce De ee
       let d := secondaryDDefectPolynomial68 Ae Be De
       FiveToSixGlobalResidual68 zeta Ae Be ce De ee d n g) := by
  obtain ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, terminal,
      A, B, C0, D, E, hterminal, hsys⟩ :=
    normalized68ScaleZero_exists_integratedPolynomialLowerSystem hsource
  refine ⟨l, alpha, beta, gamma, delta, epsilon, zeta, eta, terminal,
    A, B, C0, D, E, hterminal, hsys, ?_⟩
  exact integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys

#print axioms fiveToSix_radius_inventory_after_oneTwenty68
#print axioms integratedPolynomialLowerSystem68_global_fiveToSix_residual
#print axioms normalized68ScaleZero_global_fiveToSix_residual

end ScaleZeroGlobalResidual68

end Max11DegreeRoutes
