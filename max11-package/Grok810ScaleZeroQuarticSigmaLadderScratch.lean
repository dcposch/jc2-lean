import Grok810ScaleZeroQuarticSigmaLadderPart101Scratch
import Grok810ScaleZeroQuarticSigmaLadderPart102Scratch
import Grok810ScaleZeroQuarticSigmaLadderPart104Scratch
import Grok810ScaleZeroQuarticSigmaLadderPart105Scratch
import Grok810ScaleZeroQuarticSigmaLadderPart103Scratch

/-! # Scale-zero quartic σ-defect ladder, `(8,10)`, cone `A`

Continuation of `Grok810ScaleZeroQuarticADominantScratch`.  That file
ends at `quarticConeA810_residual`: cone `A` after closing the
all-constant cell with `l/β/δ/ζ` live and even-core `{C}`, `{E}`.

Plan `Grok810ScaleZeroQuarticSigmaLadderPlanScratch.md` File A: the
63 cost-argmin support cones (k=3 primed cones `{B}`, `{C}`, `{B,C}`
with the four extra cost conjuncts of §2.5 via mixed `pair_lt`;
60 k=2 cones) plus the four *mixed residual* cones
`QuarticMixedSigmaCone{BF,BG,CF,CG}810`, the 64-way vanishing exhaust
(a linear tournament on the singleton-face costs `u_X = k_X σ_X`,
then the four §2.5 mixed comparisons; emitter
`scripts/emit_810_quartic_sigma_exhaust.py`), the auxiliary `N₂ = ν + (1/8) A κ`,
kappa and `N₂` load-kill predicates, the all-letters-zero and
`B = D = F = 0` parity corners, and the residual.

CAS `scripts/derive_810_scale_zero_quartic_adominant.py` plus
`scripts/_810_quartic_sigma_ladder_cas.py`: cost assertion OK, `N₂`
has the 8 load-free monomials and five pure-`A` columns of §2.3,
band unions are strict (no walls), corner H letter-count scan
recorded below.

The 63 cones of the plan are **not** exhaustive: their cost comparison
is not transitive.  `a = 4, b = 1, d = 2, f = 5`, `C = E = G = 0`
(so `s_B = 10, s_D = 16, s_F = 18`) satisfies cone `A` and none of the
63: `B` fails `2σ_B < σ_F`, `D` fails `2σ_D < 3σ_B`, `F` fails
`σ_F < σ_D`, and no tie holds.  There the cost minimum is the mixed
monomial `BF` (`s_B + s_F = 28 < 30 = 3 s_B`), whose face is none of the
63 faces; the four new cones name exactly that chamber and need faces
and kills in Files B/C (or a taxonomy fix upstream).

A second, independent gap is **not** repaired here: inside a k=2 cone
the level-2 face on `S` need not be the cost minimum either, since a
mixed monomial can undercut it.  `a = 10, b = 8, d = 15, f = 23`,
`C = E = G = 0` (`s_B = 14, s_D = 20, s_F = 24`) satisfies
`QuarticLoadSigmaConeD810` (`2 s_D = 40 < 42 = 3 s_B`, `s_D < s_F`)
while `BF` costs `s_B + s_F = 38 < 40 = 2 s_D`, so `D²` is not the top
face there.  Pinning the face down needs the three-letter conjunct
`2 s_D < s_B + s_F`, which no pairwise cone can state; the rest bounds
of Files B/C have to carry it (or the taxonomy has to be re-derived).

Does not close the 63 + 4 cones (Files B/C) or the remaining even core
(File D).  Corner H (`s ≥ 4a`, `B = 0`, unkillable even loads
`γ/ε/η`) is not closed here.  Unclosable sub-chamber named in the
residual docstring: `B = 0 ∧ s ≥ 4a ∧ S ⊆ {C,D,E} ∧ γ ≠ 0`
(CAS also lists further H-supports whose `γ/ε/η` columns have
letter count 1: `D`, `E`, `DE`, and several F/G-containing
supports).  No `sorry`, no new axioms, no finite-root shortcut.
Untracked working note.
-/

/-! This module is now a pure import aggregator: its declarations live in the
`Part..` modules above, one per file, so that no single module elaborates them
all at once.  Every statement, name, binder and section context is unchanged. -/

namespace Max11DegreeRoutes

#print axioms degreeZeroN2Quartic810_natDegree_le
#print axioms degreeZeroN2Quartic810_eq_l_add_rest
#print axioms quarticSigma_l_eq_zero
#print axioms quarticADominant_allLettersZero_impossible
#print axioms quarticParityCorner_BDF_zero_impossible
#print axioms quarticSigmaSupportCone810_of
#print axioms normalized810ScaleZero_quarticSigmaResidual


end Max11DegreeRoutes
