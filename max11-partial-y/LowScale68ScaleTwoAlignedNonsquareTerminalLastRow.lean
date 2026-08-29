import LowScale68ScaleTwoAlignedNonsquareTerminalQuotient

/-! # Quotient terminal face with the cleared descended last row -/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

section QuotientFace68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- The terminal valuation witnesses, with the common `H²` cancelled from
the source `I₄` identity. -/
theorem NonsquareAlignedSourceCurveData68.terminalI4_quotientPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) :
    ∃ (g r t b1 d1 w1 phi1 : k[X]),
      p.coeff 5 = H * g ∧ g = H * r ∧ p.coeff 4 = H * t ∧
      cubicBNumerator68 (p.coeff 3) t r = H * b1 ∧
      cubicDNumerator68 H (p.coeff 1) (p.coeff 2) (p.coeff 3) t r = H * d1 ∧
      cubicWNumerator68 H (p.coeff 2) (p.coeff 3) t r S.gamma = H * w1 ∧
      cubicPhiNumerator68 H (p.coeff 0) (p.coeff 1) (p.coeff 2)
        (p.coeff 3) t r S.gamma S.epsilon = H * phi1 ∧
      b1 * phi1 + (6 : k[X]) * w1 * d1 = 0 := by
  obtain ⟨g, r, t, hg, hr, ht, hBdvd, hDdvd, hWdvd, hPhidvd⟩ :=
    S.cubicCoreTerminalValuationPacket (H := H) hdeg hp hq hp6 hq8
      haligned hjac
  obtain ⟨b1, hb1⟩ := hBdvd
  obtain ⟨d1, hd1⟩ := hDdvd
  obtain ⟨w1, hw1⟩ := hWdvd
  obtain ⟨phi1, hphi1⟩ := hPhidvd
  have hsource := S.terminalI4_cleared_source_identity (H := H) hp hp6
    hg hr ht
  rw [hb1, hd1, hw1, hphi1] at hsource
  have hfactor : H ^ 2 *
      (b1 * phi1 + (6 : k[X]) * w1 * d1) = 0 := by
    linear_combination hsource
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hquot : b1 * phi1 + (6 : k[X]) * w1 * d1 = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left (pow_ne_zero 2 hH)
  exact ⟨g, r, t, b1, d1, w1, phi1, hg, hr, ht, hb1, hd1, hw1,
    hphi1, hquot⟩

end QuotientFace68

section ClearedLastRowAlgebra68

variable {F : Type*} [Field F] [CharZero F]

/-- Clearing the single core denominator in the descended last row.  The
constant Jacobian becomes `j*H`; hence root evaluation is homogeneous and
does not by itself contradict `j ≠ 0`. -/
theorem descendedLastRow_clear_core_68
    (H b1 w1 d1 e' v' c j : F) (hH : H ≠ 0)
    (hrow : b1 * (w1 / H) * e' - (d1 / H) * (v' - c * e') = j) :
    b1 * w1 * e' - d1 * (v' - c * e') = j * H := by
  field_simp [hH] at hrow ⊢
  linear_combination hrow

/-- The terminal quotient face and the cleared last row are a finite
two-equation packet; neither equation alone forces a chosen external
parameter `r` to vanish. -/
theorem terminalQuotient_lastRow_finitePacket_68
    (H b1 phi1 w1 d1 e' v' c j : F) (hH : H ≠ 0)
    (hI4 : b1 * phi1 + 6 * w1 * d1 = 0)
    (hrow : b1 * (w1 / H) * e' - (d1 / H) * (v' - c * e') = j) :
    b1 * phi1 + 6 * w1 * d1 = 0 ∧
      b1 * w1 * e' - d1 * (v' - c * e') = j * H :=
  ⟨hI4, descendedLastRow_clear_core_68 H b1 w1 d1 e' v' c j hH hrow⟩

end ClearedLastRowAlgebra68

end Max11DegreeRoutes
