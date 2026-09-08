import Grok810ScaleZeroConeExhaustionSpeedReflValDegSplitBaseScratch

/-! # SPEED: theorems of `Grok810ScaleZeroConeExhaustionSpeedReflValDegScratch`, part 0 of 8, so that no single
module retains all the reflective bridge proof terms at once.
Statements unchanged. -/

noncomputable section

open scoped Polynomial.Bivariate
open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 8000000

section ExhaustIdentities810

variable {k : Type*} [Field k] [CharZero k]

/-- Groebner membership `C₀⁶ ∈ (μ_inner, ξ_inner)`.  CAS: saturating by
`s` yields `(1)`. -/
theorem mu_xi_AC02_inner_identity (r s : k) :
    (231 * r ^ 6 - 4004 * r ^ 4 * s + 8736 * r ^ 2 * s ^ 2 - 2048 * s ^ 3) *
        muAC02Inner810 r s +
      (-(49 : k) * r * (11 * r ^ 4 - 176 * r ^ 2 * s + 192 * s ^ 2)) *
        xiAC02Inner810 r s =
      (1048576 : k) * s ^ 6 := by
  simp only [muAC02Inner810, xiAC02Inner810]
  ring


theorem mu_xi_AC02_inner_s_pow (r s : k)
    (hmu : muAC02Inner810 r s = 0)
    (hxi : xiAC02Inner810 r s = 0) :
    s ^ 6 = 0 := by
  have hid := mu_xi_AC02_inner_identity (k := k) r s
  have hcomb : (1048576 : k) * s ^ 6 = 0 := by
    rw [← hid, hmu, hxi]
    simp
  have hne : (1048576 : k) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hcomb).resolve_left hne


theorem mu_xi_AE06_inner_identity (r v : k) :
    (231 * r ^ 6 + 3668 * r ^ 3 * v + 1248 * v ^ 2) * muAE06Inner810 r v +
      (-(49 : k) * r ^ 2 * (11 * r ^ 3 + 172 * v)) * xiAE06Inner810 r v =
      (2555904 : k) * v ^ 4 := by
  simp only [muAE06Inner810, xiAE06Inner810]
  ring


theorem mu_xi_AE06_inner_v_pow (r v : k)
    (hmu : muAE06Inner810 r v = 0)
    (hxi : xiAE06Inner810 r v = 0) :
    v ^ 4 = 0 := by
  have hid := mu_xi_AE06_inner_identity (k := k) r v
  have hcomb : (2555904 : k) * v ^ 4 = 0 := by
    rw [← hid, hmu, hxi]
    simp
  have hne : (2555904 : k) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hcomb).resolve_left hne


theorem mu_omicron_BE02_inner_identity (s w : k) :
    (21 * s ^ 4 - 328 * s ^ 2 * w + 256 * w ^ 2) * muBE02Inner810 s w +
      (-(s : k) * (7 * s ^ 2 - 104 * w)) * omicronBE02Inner810 s w =
      (16384 : k) * w ^ 4 := by
  simp only [muBE02Inner810, omicronBE02Inner810]
  ring


theorem mu_omicron_BE02_inner_w_pow (s w : k)
    (hmu : muBE02Inner810 s w = 0)
    (hom : omicronBE02Inner810 s w = 0) :
    w ^ 4 = 0 := by
  have hid := mu_omicron_BE02_inner_identity (k := k) s w
  have hcomb : (16384 : k) * w ^ 4 = 0 := by
    rw [← hid, hmu, hom]
    simp
  have hne : (16384 : k) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hcomb).resolve_left hne


/-- `(r/121) μ_inner + (8/605) ξ_inner = r⁷`. -/
theorem mu_xi_AD05_inner_identity (r d : k) :
    (5 : k) * r ^ 2 * (77 * r ^ 5 - 1536 * d ^ 2) -
        24 * r ^ 2 * (11 * r ^ 5 - 320 * d ^ 2) =
      (121 : k) * r ^ 7 := by
  ring


theorem mu_xi_AD05_inner_r_pow (r d : k)
    (hmu : muAD05Inner810 r d = 0)
    (hxi : xiAD05Inner810 r d = 0) :
    r ^ 7 = 0 := by
  have hid := mu_xi_AD05_inner_identity (k := k) r d
  have h5 : (5 : k) * r * (77 * r ^ 5 - 1536 * d ^ 2) = 0 := hmu
  have h15 : (15 : k) * r ^ 2 * (11 * r ^ 5 - 320 * d ^ 2) = 0 := by
    have := hxi
    simpa [xiAD05Inner810, neg_mul] using this
  have hleft :
      (5 : k) * r ^ 2 * (77 * r ^ 5 - 1536 * d ^ 2) -
          24 * r ^ 2 * (11 * r ^ 5 - 320 * d ^ 2) = 0 := by
    have hr : (5 : k) * r ^ 2 * (77 * r ^ 5 - 1536 * d ^ 2) =
        r * ((5 : k) * r * (77 * r ^ 5 - 1536 * d ^ 2)) := by ring
    have h24 : (24 : k) * r ^ 2 * (11 * r ^ 5 - 320 * d ^ 2) =
        (8 : k) / 5 * ((15 : k) * r ^ 2 * (11 * r ^ 5 - 320 * d ^ 2)) := by
      ring
    simp [hr, h5, h24, h15]
  have h121 : (121 : k) * r ^ 7 = 0 := by
    rw [← hid, hleft]
  have hne : (121 : k) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h121).resolve_left hne


end ExhaustIdentities810

section ExhaustCombined810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 16000000 in
theorem degreeZeroMuPolynomial810_eq_A6_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      muA6Face810 A +
        degreeZeroMuNoA6Polynomial810 l beta gamma delta epsilon zeta eta
          theta A B C0 D0 E0 F0 G0 := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroMuPolynomial810, muA6Face810,
    degreeZeroMuNoA6Polynomial810]
  module


set_option maxHeartbeats 16000000 in
theorem degreeZeroMuPolynomial810_eq_AC02_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      muAC02Combined810 A C0 +
        degreeZeroMuNoAC02Polynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroMuPolynomial810, muAC02Combined810,
    degreeZeroMuNoAC02Polynomial810]
  module


set_option maxHeartbeats 16000000 in
theorem degreeZeroXiPolynomial810_eq_AC02_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      xiAC02Combined810 A C0 +
        degreeZeroXiNoAC02Polynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroXiPolynomial810, xiAC02Combined810,
    degreeZeroXiNoAC02Polynomial810]
  module


set_option maxHeartbeats 16000000 in
theorem degreeZeroMuPolynomial810_eq_AE06_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroMuPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      muAE06Combined810 A E0 +
        degreeZeroMuNoAE06Polynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroMuPolynomial810, muAE06Combined810,
    degreeZeroMuNoAE06Polynomial810]
  module


set_option maxHeartbeats 16000000 in
theorem degreeZeroXiPolynomial810_eq_AE06_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C0 D0 E0 F0 G0 : k[X]) :
    degreeZeroXiPolynomial810 l beta gamma delta epsilon zeta eta theta
        A B C0 D0 E0 F0 G0 =
      xiAE06Combined810 A E0 +
        degreeZeroXiNoAE06Polynomial810 l beta gamma delta epsilon zeta
          eta theta A B C0 D0 E0 F0 G0 := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroXiPolynomial810, xiAE06Combined810,
    degreeZeroXiNoAE06Polynomial810]
  module


end ExhaustCombined810

end Max11DegreeRoutes

end
