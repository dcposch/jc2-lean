import Grok810ScaleZeroQuarticChamberUnownedKills1Scratch
import Grok810ScaleZeroQuarticChamberUnownedKills2Scratch
import Grok810ScaleZeroQuarticChamberUnownedKills3Scratch
import Grok810ScaleZeroQuarticChamberUnownedKills4Scratch
import Grok810ScaleZeroQuarticChamberUnownedKills5Scratch
import Grok810ScaleZeroQuarticChamberUnownedKills6Scratch
import Grok810ScaleZeroQuarticChamberUnownedKills7Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystems1Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystems2Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystems3Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystems4Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystems5Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystems6Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystems7Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystems8Scratch
import Grok810ScaleZeroQuarticChamberUnownedSplitsScratch

/-! # Assembly core, `(8,10)` scale zero

`normalized810ScaleZero_impossible_of_residualKills`: the whole cone-`A`
route of modules 1-30, reduced to three named obligations — the
172 chambers of `QuarticChamberResidual4810`, the all-constant
corner, and the sibling cone `ABCDEFG`.  Gate-able now; the tracked-name
glue is `Grok810ScaleZeroQuarticAssemblyScratch`.  Untracked working note.
-/

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

section QuarticAssemblyCore810

variable [IsAlgClosed k]

/-! ## The three obligations the chamber ladder does not discharge

Everything else on cone `A` is closed by modules 1-30.  These are
exactly the inputs the parallel lanes owe. -/

set_option maxHeartbeats 64000000 in
/-- Assembly core: `Normalized810LeadingCoreSource P Q H 0` is impossible once

* `hresid` kills every chamber of `QuarticChamberResidual4810` (the tower lane's
  2 open / 19 deep-rescue / 405-wall families and the power-certificate lane's
  `power_target` systems);
* `hcorner` kills the all-constant corner `l = β = δ = ζ = 0` with every letter
  constant (File A's `quarticADominant_constantLetters_impossible_of_*` handle
  the four cases where one of those loads is non-zero; this is the remaining
  `θ`/`B³` tie on `A⁴`);
* `habcdefg` kills the sibling cone `QuarticRatioConeABCDEFG810`.

No `sorry`, no new axioms, no finite-root shortcut. -/
theorem normalized810ScaleZero_impossible_of_residualKills
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hresid :
      ∀ (j t l beta gamma delta epsilon zeta eta theta : k)
        (A B C D E F G : k[X]),
        j / t ≠ 0 →
        derivative
            (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
              eta theta A B C D E F G) =
          Polynomial.C (j / t) →
        (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree = 0 →
        (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree = 0 →
        (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree = 0 →
        (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree = 0 →
        (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree = 0 →
        (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree = 0 →
        QuarticRatioConeA810 A B C D E F G →
        QuarticChamberResidual6810 A B C D E F G →
        False)
    (hcorner :
      ∀ (j t gamma epsilon eta theta : k) (A B C D E F G : k[X]),
        j / t ≠ 0 →
        derivative
            (degreeZeroPrimitiveQuartic810 0 0 gamma 0 epsilon 0 eta theta
              A B C D E F G) =
          Polynomial.C (j / t) →
        QuarticRatioConeA810 A B C D E F G →
        B.natDegree = 0 → C.natDegree = 0 → D.natDegree = 0 →
        E.natDegree = 0 → F.natDegree = 0 → G.natDegree = 0 →
        False)
    (habcdefg :
      ∀ (j t l beta gamma delta epsilon zeta eta theta : k)
        (A B C D E F G : k[X]),
        j / t ≠ 0 →
        derivative
            (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
              eta theta A B C D E F G) =
          Polynomial.C (j / t) →
        (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
            A B C D E F G).natDegree = 0 →
        QuarticRatioConeABCDEFG810 A B C D E F G →
        False)
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    False := by
  obtain ⟨t, j, lambda, cleared, l, beta, gamma, delta, epsilon, zeta,
      eta, theta, cXi, cMu, cOm, A, B, C, D, E, F, G, ht, hj, hjdiv,
      hHsq, hder, hxiDeg, hmuDeg, homiDeg, hkapDeg, hnuDeg, hpiDeg, hdisj⟩ :=
    normalized810ScaleZero_quarticChamber6Residual hsource
  rcases hdisj with ⟨hconeA, hcase⟩ | habc
  · rcases hcase with ⟨hl0, hb0, hd0, hz0, hBn, hCn, hDn, hEn, hFn, hGn⟩ | hres
    · subst hl0; subst hb0; subst hd0; subst hz0
      exact hcorner j t gamma epsilon eta theta A B C D E F G hjdiv hder
        hconeA hBn hCn hDn hEn hFn hGn
    · exact hresid j t l beta gamma delta epsilon zeta eta theta
        A B C D E F G hjdiv hder hxiDeg hmuDeg homiDeg hkapDeg hnuDeg hpiDeg
        hconeA hres
  · exact habcdefg j t l beta gamma delta epsilon zeta eta theta
      A B C D E F G hjdiv hder hkapDeg habc


end QuarticAssemblyCore810

end Max11DegreeRoutes
