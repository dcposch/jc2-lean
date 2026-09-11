import Fable610ScaleTwoAlignedFaceScratch
import Grok810SpeedValLibScratch

open scoped Polynomial.Bivariate
noncomputable section
open MvPolynomial Polynomial
namespace Max11DegreeRoutes
set_option maxRecDepth 100000000

/-- Literal consumed base equation, with its integration constant retained. -/
def alignedTwelfthBaseEquation610 {K : Type*} [CommRing K]
    (H a4 a5 b8 : K[X]) (κ : K) : K[X] :=
  alignedSecondDefect610 H a4 a5 b8 - Polynomial.C κ * H ^ 5

end Max11DegreeRoutes
