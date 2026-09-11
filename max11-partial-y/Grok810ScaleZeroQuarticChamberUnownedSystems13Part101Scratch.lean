import Mathlib
import Grok810ScaleZeroQuarticChamberUnownedSystemBridges1Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystems13Part1Row0Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystems13Part1Row1Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystems13Part3Row101Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystems13Part3Row2Scratch

/-! # Unowned multi-carrier systems, part 13/15

2 of the 48 chambers `UNOWNED_CHAMBERS.md` §3.3 closes with a
Singular-lifted top-coefficient system.  Every load column of every row
carries an exact rational Farkas verdict (`dominated`, `dominated-hnc` or
a named band).
Untracked working note.
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

section QuarticChamberUnownedSystems13810

set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `BCDEFG` / `CG·DD·CCC` leaf 2: the 10 face rows force `c * d * f = 0`. -/
theorem quarticUnownedSystemBCDEFG102L2810_cert
    (a b c d e f g : k)
    (hr0 : (-15 / 128 : k) * b * c ^ 2 + (5 / 16 : k) * b * g + (5 / 16 : k) * c * f = 0)
    (hr1 : (-5 / 128 : k) * a * d ^ 2 + (-5 / 128 : k) * c ^ 3 + (5 / 16 : k) * c * g = 0)
    (hr2 : (15 / 1024 : k) * a * b * c ^ 2 + (-5 / 128 : k) * a * b * g + (-5 / 128 : k) * a * c * f + (-15 / 128 : k) * c ^ 2 * d + (5 / 16 : k) * d * g = 0)
    (hr3 : (15 / 256 : k) * a * b * c * d + (-5 / 64 : k) * a * d * f + (-15 / 128 : k) * c * d ^ 2 = 0)
    (hr4 : (15 / 16384 : k) * a ^ 2 * b * c ^ 2 + (-5 / 2048 : k) * a ^ 2 * b * g + (-5 / 2048 : k) * a ^ 2 * c * f + (15 / 1024 : k) * a * c ^ 2 * d + (-5 / 128 : k) * a * d * g = 0)
    (hr5 : (5 / 32 : k) * a * c * d ^ 2 + (15 / 256 : k) * c ^ 4 + (-5 / 16 : k) * c ^ 2 * g + (5 / 4 : k) * g ^ 2 = 0)
    (hr6 : (15 / 16384 : k) * a ^ 3 * b * c ^ 2 + (-5 / 2048 : k) * a ^ 3 * b * g + (-5 / 2048 : k) * a ^ 3 * c * f + (15 / 2048 : k) * a ^ 2 * c ^ 2 * d + (-5 / 256 : k) * a ^ 2 * d * g = 0)
    (hr7 : (-15 / 128 : k) * c ^ 2 * d + (5 / 16 : k) * d * g = 0)
    (hr8 : (45 / 2048 : k) * a * c ^ 2 * d + (-15 / 256 : k) * a * d * g = 0)
    (hr9 : (-15 / 2048 : k) * a ^ 2 * c ^ 2 * d + (5 / 256 : k) * a ^ 2 * d * g = 0)
    (hCc : (c : k) ≠ 0)
    (hDc : (d : k) ≠ 0)
    (hFc : (f : k) ≠ 0) :
    False := by
  have ht : c * d * f = 0 := by
    linear_combination ((16 / 5 : k) * d) * hr0 + ((-16 / 5 : k) * b) * hr7
  exact (mul_ne_zero (mul_ne_zero hCc hDc) hFc) ht

end QuarticChamberUnownedSystems13810

end Max11DegreeRoutes
/-! # Unowned multi-carrier systems, part 13/15

2 of the 48 chambers `UNOWNED_CHAMBERS.md` §3.3 closes with a
Singular-lifted top-coefficient system.  Every load column of every row
carries an exact rational Farkas verdict (`dominated`, `dominated-hnc` or
a named band).
Untracked working note.
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

section QuarticChamberUnownedSystems13810

open private quarticRefinedBCDEFG102L2810_impossible_row0 from Grok810ScaleZeroQuarticChamberUnownedSystems13Part1Row0Scratch in
open private quarticRefinedBCDEFG102L2810_impossible_row7 from Grok810ScaleZeroQuarticChamberUnownedSystems13Part1Row1Scratch in
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `BCDEFG` / `CG·DD·CCC` leaf 2 dies on the 10-carrier system (κ, μ, ν, ξ, ο, π, Π, N₂, N₃, N₄). -/
theorem quarticRefinedBCDEFG102L2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDEFG102L2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmuDeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxiDeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hcell, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hx9, hx10⟩ := id hch
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hcell
  have hin0 := quarticRefinedBCDEFG102L2810_impossible_row0 l beta gamma delta epsilon zeta eta theta A B C D E F G hch hnc hkap hprim homi hnu hmuDeg hxiDeg hpiDeg
  have hin7 := quarticRefinedBCDEFG102L2810_impossible_row7 l beta gamma delta epsilon zeta eta theta A B C D E F G hch hnc hkap hprim homi hnu hmuDeg hxiDeg hpiDeg
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  have ht : C.leadingCoeff * D.leadingCoeff * F.leadingCoeff = 0 := by
    linear_combination ((16 / 5 : k) * D.leadingCoeff) * hin0 + ((-16 / 5 : k) * B.leadingCoeff) * hin7
  exact (mul_ne_zero (mul_ne_zero hCc hDc) hFc) ht

end QuarticChamberUnownedSystems13810

end Max11DegreeRoutes
/-! # Unowned multi-carrier systems, part 13/15

2 of the 48 chambers `UNOWNED_CHAMBERS.md` §3.3 closes with a
Singular-lifted top-coefficient system.  Every load column of every row
carries an exact rational Farkas verdict (`dominated`, `dominated-hnc` or
a named band).
Untracked working note.
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

section QuarticChamberUnownedSystems13810

set_option maxHeartbeats 64000000 in
/-- The Singular-lifted certificate of chamber `BCDEFG` / `CG·DD·CCC` leaf 5: the 10 face rows force `d * g ^ 2 = 0`. -/
theorem quarticUnownedSystemBCDEFG102L5810_cert
    (a b c d e f g : k)
    (hr0 : (-15 / 128 : k) * b * c ^ 2 + (5 / 16 : k) * b * g + (5 / 16 : k) * c * f + (5 / 16 : k) * d * e = 0)
    (hr1 : (-5 / 128 : k) * a * d ^ 2 + (-5 / 128 : k) * c ^ 3 + (5 / 16 : k) * c * g = 0)
    (hr2 : (15 / 1024 : k) * a * b * c ^ 2 + (-5 / 128 : k) * a * b * g + (-5 / 128 : k) * a * c * f + (-5 / 128 : k) * a * d * e + (-15 / 128 : k) * c ^ 2 * d + (5 / 16 : k) * d * g = 0)
    (hr3 : (15 / 256 : k) * a * b * c * d + (-5 / 64 : k) * a * d * f + (-15 / 128 : k) * c ^ 2 * e + (-15 / 128 : k) * c * d ^ 2 + (5 / 16 : k) * e * g = 0)
    (hr4 : (15 / 16384 : k) * a ^ 2 * b * c ^ 2 + (-5 / 2048 : k) * a ^ 2 * b * g + (-5 / 2048 : k) * a ^ 2 * c * f + (-5 / 2048 : k) * a ^ 2 * d * e + (15 / 1024 : k) * a * c ^ 2 * d + (-5 / 128 : k) * a * d * g = 0)
    (hr5 : (5 / 32 : k) * a * c * d ^ 2 + (15 / 256 : k) * c ^ 4 + (-5 / 16 : k) * c ^ 2 * g + (5 / 4 : k) * g ^ 2 = 0)
    (hr6 : (15 / 16384 : k) * a ^ 3 * b * c ^ 2 + (-5 / 2048 : k) * a ^ 3 * b * g + (-5 / 2048 : k) * a ^ 3 * c * f + (-5 / 2048 : k) * a ^ 3 * d * e + (15 / 2048 : k) * a ^ 2 * c ^ 2 * d + (-5 / 256 : k) * a ^ 2 * d * g = 0)
    (hr7 : (-15 / 128 : k) * c ^ 2 * d + (5 / 16 : k) * d * g = 0)
    (hr8 : (45 / 2048 : k) * a * c ^ 2 * d + (-15 / 256 : k) * a * d * g = 0)
    (hr9 : (-15 / 2048 : k) * a ^ 2 * c ^ 2 * d + (5 / 256 : k) * a ^ 2 * d * g = 0)
    (hDc : (d : k) ≠ 0)
    (hGc : (g : k) ≠ 0) :
    False := by
  have ht : d * g ^ 2 = 0 := by
    linear_combination ((72 / 55 : k) * c * d) * hr1 + ((18 / 55 : k) * d) * hr5 + ((-3 / 11 : k) * c ^ 2 + (104 / 55 : k) * g) * hr7
  exact (mul_ne_zero hDc (pow_ne_zero 2 hGc)) ht

end QuarticChamberUnownedSystems13810

end Max11DegreeRoutes
/-! # Unowned multi-carrier systems, part 13/15

2 of the 48 chambers `UNOWNED_CHAMBERS.md` §3.3 closes with a
Singular-lifted top-coefficient system.  Every load column of every row
carries an exact rational Farkas verdict (`dominated`, `dominated-hnc` or
a named band).
Untracked working note.
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

section QuarticChamberUnownedSystems13810

open private quarticRefinedBCDEFG102L5810_impossible_row1 from Grok810ScaleZeroQuarticChamberUnownedSystems13Part3Row101Scratch in
open private quarticRefinedBCDEFG102L5810_impossible_row5 from Grok810ScaleZeroQuarticChamberUnownedSystems13Part3Row101Scratch in
open private quarticRefinedBCDEFG102L5810_impossible_row7 from Grok810ScaleZeroQuarticChamberUnownedSystems13Part3Row2Scratch in
set_option maxHeartbeats 64000000 in
/-- Unowned chamber `BCDEFG` / `CG·DD·CCC` leaf 5 dies on the 10-carrier system (κ, μ, ν, ξ, ο, π, Π, N₂, N₃, N₄). -/
theorem quarticRefinedBCDEFG102L5810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDEFG102L5810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmuDeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxiDeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hcell, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16, hx17, hx18, hx19, hx20, hx21, hx22, hx23⟩ := id hch
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hcell
  have hin1 := quarticRefinedBCDEFG102L5810_impossible_row1 l beta gamma delta epsilon zeta eta theta A B C D E F G hch hnc hkap hprim homi hnu hmuDeg hxiDeg hpiDeg
  have hin5 := quarticRefinedBCDEFG102L5810_impossible_row5 l beta gamma delta epsilon zeta eta theta A B C D E F G hch hnc hkap hprim homi hnu hmuDeg hxiDeg hpiDeg
  have hin7 := quarticRefinedBCDEFG102L5810_impossible_row7 l beta gamma delta epsilon zeta eta theta A B C D E F G hch hnc hkap hprim homi hnu hmuDeg hxiDeg hpiDeg
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  have ht : D.leadingCoeff * G.leadingCoeff ^ 2 = 0 := by
    linear_combination ((72 / 55 : k) * C.leadingCoeff * D.leadingCoeff) * hin1 + ((18 / 55 : k) * D.leadingCoeff) * hin5 + ((-3 / 11 : k) * C.leadingCoeff ^ 2 + (104 / 55 : k) * G.leadingCoeff) * hin7
  exact (mul_ne_zero hDc (pow_ne_zero 2 hGc)) ht

end QuarticChamberUnownedSystems13810

end Max11DegreeRoutes
