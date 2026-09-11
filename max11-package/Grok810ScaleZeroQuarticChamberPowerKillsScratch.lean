import Grok810ScaleZeroQuarticChamberRests5Scratch
import Grok810ScaleZeroQuarticPowerCertificatesScratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart102Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart103Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart104Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart105Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart106Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart107Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart108Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart109Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart110Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart111Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart112Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart113Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart114Scratch
import Grok810ScaleZeroQuarticChamberPowerKillsPart115Scratch

/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

end QuarticChamberPowerKills810

end Max11DegreeRoutes
