import LowScale46LocalChart

/-! # Eliminated local equations in the aligned `(4,6)` branch

When the mismatch constant `L` vanishes, the first local boundary equation
eliminates `Z` exactly.  This module verifies the three reviewed polynomial
equations obtained from the remaining boundary and coefficient-curve rows.
-/

noncomputable section

namespace Max11DegreeRoutes

section AlignedChart

variable {F : Type*} [Field F] [CharZero F]

/-- Exact elimination of `Z` from the first local boundary row. -/
def alignedLocalZ46 (s Q Y d0 : F) : F :=
  4 * (Y + Q ^ 2 - d0 * s ^ 4)

/-- The reviewed aligned boundary polynomial after eliminating `Z`. -/
def alignedLocalG46 (s Q Y beta gamma delta d0 e0 : F) : F :=
  4 * Q ^ 3 - 3 * Y ^ 2 + 4 * beta * s ^ 3 -
    12 * beta * Q * s ^ 3 - 6 * beta * Y * s ^ 3 -
    (8 * gamma + 12 * d0) * Q * s ^ 4 - 8 * delta * s ^ 5 +
    8 * e0 * s ^ 6

/-- The reviewed aligned `J₂` polynomial after eliminating `Z`. -/
def alignedLocalJTwo46
    (s Q Y beta gamma delta d0 k2 : F) : F :=
  -6 * Q ^ 2 * Y - 6 * Y ^ 2 + 3 * beta * s ^ 3 -
    6 * beta * Q * s ^ 3 - 3 * beta * Q ^ 2 * s ^ 3 -
    6 * beta * Y * s ^ 3 + (4 * gamma + 6 * d0) * Y * s ^ 4 -
    4 * delta * s ^ 5 + 4 * delta * Q * s ^ 5 +
    (6 * beta * d0 - 2 * k2) * s ^ 7

/-- The reviewed aligned `J₁` polynomial after eliminating `Z`. -/
def alignedLocalJOne46
    (s Q Y beta gamma delta d0 k1 : F) : F :=
  3 * Q ^ 4 + 6 * Q ^ 2 * Y - 3 * Q * Y ^ 2 + 6 * Y ^ 2 +
    3 * beta * Y * s ^ 3 - 3 * beta * Q * Y * s ^ 3 -
    (4 * gamma + 6 * d0) * Q ^ 2 * s ^ 4 -
    (4 * gamma + 6 * d0) * Y * s ^ 4 + 2 * delta * Y * s ^ 5 +
    (4 * gamma * d0 + 3 * d0 ^ 2 - 2 * k1) * s ^ 8

/-- The aligned eliminated boundary equation is `-8` times the original
weight-six local row. -/
theorem alignedLocalG46_eq
    (s Q Y beta gamma delta d0 e0 : F) :
    alignedLocalG46 s Q Y beta gamma delta d0 e0 =
      -8 * localChartG46 0 s Q Y (alignedLocalZ46 s Q Y d0)
        beta gamma delta e0 := by
  simp only [alignedLocalG46, alignedLocalZ46, localChartG46]
  ring

/-- The aligned eliminated first curve equation is twice the original
weight-seven local row. -/
theorem alignedLocalJTwo46_eq
    (s Q Y beta gamma delta d0 k2 : F) :
    alignedLocalJTwo46 s Q Y beta gamma delta d0 k2 =
      2 * localChartJTwo46 0 s Q Y (alignedLocalZ46 s Q Y d0)
        beta gamma delta k2 := by
  simp only [alignedLocalJTwo46, alignedLocalZ46, localChartJTwo46]
  ring

/-- The aligned eliminated second curve equation is twice the original
weight-eight local row. -/
theorem alignedLocalJOne46_eq
    (s Q Y beta gamma delta d0 k1 : F) :
    alignedLocalJOne46 s Q Y beta gamma delta d0 k1 =
      2 * localChartJOne46 0 s Q Y (alignedLocalZ46 s Q Y d0)
        beta gamma delta k1 := by
  simp only [alignedLocalJOne46, alignedLocalZ46, localChartJOne46]
  ring

end AlignedChart

section LastAlignedStratum

variable {F : Type*} [Field F] [CharZero F]

/-- Shift which exposes the reducible last aligned coefficient curve. -/
def alignedShiftV46 (U gamma : F) : F := U - (8 / 3 : F) * gamma

/-- Shifted coordinate `X=B+beta` used for the complete aligned curve. -/
def alignedShiftX46 (B beta : F) : F := B + beta

/-- First polynomial on the aligned plane-curve model. -/
def alignedPhi46 (A beta gamma delta k2 : F) : F :=
  (4 / 3 : F) * delta * A + (1 / 2 : F) * beta * A ^ 2 -
    (4 / 3 : F) * (k2 + 2 * beta * gamma)

/-- Second polynomial on the aligned plane-curve model. -/
def alignedR46 (A X beta gamma delta k1 : F) : F :=
  8 * A * X * (X - beta) - (32 / 3 : F) * delta * (X - beta) +
    (32 / 3 : F) * (k1 + (2 / 3 : F) * gamma ^ 2)

/-- Exact identity behind the aligned equation `X*V=Phi(A)`. -/
theorem aligned_curveTwo_identity
    (A B U beta gamma delta k2 : F) :
    alignedShiftX46 B beta * alignedShiftV46 U gamma -
        alignedPhi46 A beta gamma delta k2 =
      (-4 / 3 : F) *
        (coefficientCurveTwo46 0 A B U beta gamma delta - k2) := by
  simp only [alignedShiftX46, alignedShiftV46, alignedPhi46,
    coefficientCurveTwo46]
  ring

/-- Exact identity behind the aligned equation `V²=R(A,X)`. -/
theorem aligned_curveOne_identity
    (A B U beta gamma delta k1 : F) :
    alignedShiftV46 U gamma ^ 2 -
        alignedR46 A (alignedShiftX46 B beta) beta gamma delta k1 =
      (32 / 3 : F) *
        (coefficientCurveOne46 0 A B U beta gamma delta - k1) := by
  simp only [alignedShiftX46, alignedShiftV46, alignedR46,
    coefficientCurveOne46]
  ring

/-- The two aligned coefficient-curve equations imply the explicit plane
curve `Phi(A)^2=X^2*R(A,X)` after eliminating `V`. -/
theorem aligned_planeCurve46
    (A X V beta gamma delta k1 k2 : F)
    (hXV : X * V = alignedPhi46 A beta gamma delta k2)
    (hV2 : V ^ 2 = alignedR46 A X beta gamma delta k1) :
    alignedPhi46 A beta gamma delta k2 ^ 2 =
      X ^ 2 * alignedR46 A X beta gamma delta k1 := by
  rw [← hXV, ← hV2]
  ring

/-- The aligned one-form in the shifted variables. -/
theorem eta46_aligned_shifted
    (A B U beta gamma delta dA dB dU : F) :
    eta46 0 A B U beta gamma delta dA dB dU =
      ((3 / 16 : F) * (alignedShiftX46 B beta - beta) *
          alignedShiftV46 U gamma +
        (3 / 8 : F) * beta * A ^ 2 +
        (1 / 2 : F) * delta * A) * dA -
      (3 / 4 : F) * alignedShiftX46 B beta *
          (alignedShiftX46 B beta - beta) * dB +
      ((-3 / 16 : F) * beta * A - (1 / 4 : F) * delta) * dU := by
  simp only [eta46, etaA46, etaB46, etaU46, alignedShiftX46,
    alignedShiftV46]
  ring

/-- Nonvanishing leading coefficient in the `beta != 0` aligned polynomial
cone, once its leading `X*V=Phi(A)` relation is known. -/
theorem aligned_beta_leadingEtaCoefficient
    (A0 X0 V0 beta : F) (hbeta : beta ≠ 0) (hA0 : A0 ≠ 0)
    (hlead : X0 * V0 = (1 / 2 : F) * beta * A0 ^ 2) :
    (3 / 16 : F) * X0 * V0 + (3 / 8 : F) * beta * A0 ^ 2 =
        (15 / 32 : F) * beta * A0 ^ 2 ∧
      (15 / 32 : F) * beta * A0 ^ 2 ≠ 0 := by
  constructor
  · linear_combination (3 / 16 : F) * hlead
  · exact mul_ne_zero (mul_ne_zero (by norm_num) hbeta) (pow_ne_zero 2 hA0)

/-- Nonvanishing leading coefficient in the `beta=0, delta != 0` aligned
polynomial cone. -/
theorem aligned_delta_leadingEtaCoefficient
    (A0 X0 V0 delta : F) (hdelta : delta ≠ 0) (hA0 : A0 ≠ 0)
    (hlead : X0 * V0 = (4 / 3 : F) * delta * A0) :
    (3 / 16 : F) * X0 * V0 + (1 / 2 : F) * delta * A0 =
        (3 / 4 : F) * delta * A0 ∧
      (3 / 4 : F) * delta * A0 ≠ 0 := by
  constructor
  · linear_combination (3 / 16 : F) * hlead
  · exact mul_ne_zero (mul_ne_zero (by norm_num) hdelta) hA0

/-- With `L=beta=delta=0`, the first coefficient-curve function is a
constant multiple of `B*V`. -/
theorem coefficientCurveTwo46_aligned_eq
    (A B U gamma : F) :
    coefficientCurveTwo46 0 A B U 0 gamma 0 =
      (-3 / 4 : F) * B * alignedShiftV46 U gamma := by
  simp only [coefficientCurveTwo46, alignedShiftV46]
  ring

/-- With `L=beta=delta=0`, the second coefficient-curve equation becomes
the reviewed quadratic equation in `V`. -/
theorem coefficientCurveOne46_aligned_identity
    (A B U gamma : F) :
    alignedShiftV46 U gamma ^ 2 - 8 * A * B ^ 2 =
      (32 / 3 : F) *
        (coefficientCurveOne46 0 A B U 0 gamma 0 +
          (2 / 3 : F) * gamma ^ 2) := by
  simp only [coefficientCurveOne46, alignedShiftV46]
  ring

/-- Exact first equation of the last aligned coefficient curve. -/
theorem aligned_curveTwo_iff
    (A B U gamma k2 : F) :
    coefficientCurveTwo46 0 A B U 0 gamma 0 = k2 ↔
      B * alignedShiftV46 U gamma = (-4 / 3 : F) * k2 := by
  rw [coefficientCurveTwo46_aligned_eq]
  constructor <;> intro h
  · linear_combination (-4 / 3 : F) * h
  · linear_combination (-3 / 4 : F) * h

/-- Exact second equation of the last aligned coefficient curve. -/
theorem aligned_curveOne_iff
    (A B U gamma k1 : F) :
    coefficientCurveOne46 0 A B U 0 gamma 0 = k1 ↔
      alignedShiftV46 U gamma ^ 2 =
        8 * A * B ^ 2 +
          (32 / 3 : F) * (k1 + (2 / 3 : F) * gamma ^ 2) := by
  have hid := coefficientCurveOne46_aligned_identity A B U gamma
  constructor <;> intro h
  · rw [h] at hid
    linear_combination hid
  · have hc : (32 / 3 : F) ≠ 0 := by norm_num
    apply mul_left_cancel₀ hc
    linear_combination h - hid

/-- On the component `V=0`, the final-row one-form restricts exactly to
`-(3/4) B² dB`. -/
theorem eta46_alignedShiftV_zero
    (A B U gamma dA dB dU : F)
    (hV : alignedShiftV46 U gamma = 0) :
    eta46 0 A B U 0 gamma 0 dA dB dU =
      (-3 / 4 : F) * B ^ 2 * dB := by
  rw [alignedShiftV46] at hV
  simp only [eta46, etaA46, etaB46, etaU46]
  linear_combination (3 / 16 * B * dA) * hV

/-- The shifted polynomial boundary parameter `P=D+2gamma/3`. -/
def alignedBoundaryP46 (D gamma : F) : F :=
  D + (2 / 3 : F) * gamma

/-- The two boundary definitions give `w=P-q²` on `V=0`. -/
theorem aligned_boundary_w_eq
    (r q B U gamma D : F)
    (hV : alignedShiftV46 U gamma = 0)
    (hD : boundaryD46 r q B U = D) :
    r * B = alignedBoundaryP46 D gamma - q ^ 2 := by
  simp only [alignedShiftV46] at hV
  simp only [boundaryD46, alignedBoundaryP46] at hD ⊢
  linear_combination hD + (1 / 4 * hV)

/-- The second boundary equation on `V=0`, expressed through
`P=D+2gamma/3` and `K=B²`. -/
theorem aligned_boundary_E_eq
    (r q B U gamma D E : F)
    (hV : alignedShiftV46 U gamma = 0)
    (hD : boundaryD46 r q B U = D)
    (hE : boundaryE46 0 r q B U 0 gamma 0 = E) :
    E = (-1 / 2 : F) * q ^ 3 +
      (3 / 2 : F) * alignedBoundaryP46 D gamma * q +
      (3 / 8 : F) * B ^ 2 := by
  have hw := aligned_boundary_w_eq r q B U gamma D hV hD
  simp only [alignedBoundaryP46] at hw
  simp only [boundaryE46] at hE
  simp only [alignedShiftV46] at hV
  simp only [alignedBoundaryP46]
  linear_combination -hE + (3 / 2 * q) * hw - (3 / 8 * q) * hV

/-- The identity `w²=qK-theta/2`, where `w=rB`, `K=B²`, and
`theta=A B²`, follows solely from `q=r²+A/2`. -/
theorem aligned_boundary_w_sq
    (r q A B : F) (hq : q = r ^ 2 + (1 / 2 : F) * A) :
    (r * B) ^ 2 = q * B ^ 2 - (1 / 2 : F) * (A * B ^ 2) := by
  rw [hq]
  ring

/-- Exact monic quartic obtained by eliminating `w` and `K` from the two
boundary equations on a nonzero-`theta` component. -/
theorem aligned_boundary_monicQuartic
    (q K w theta P E : F)
    (hw : w = P - q ^ 2)
    (hE : E = (-1 / 2 : F) * q ^ 3 + (3 / 2 : F) * P * q +
      (3 / 8 : F) * K)
    (hw2 : w ^ 2 = q * K - (1 / 2 : F) * theta) :
    q ^ 4 - 6 * P * q ^ 2 + 8 * E * q - 3 * P ^ 2 -
      (3 / 2 : F) * theta = 0 := by
  rw [hw] at hw2
  linear_combination 8 * q * hE - 3 * hw2

/-- On the `A=0` component, eliminating `B` from both boundaries gives the
reviewed monic degree-eight equation in `r`. -/
theorem aligned_boundary_A_zero_monicOctic
    (r B P E : F)
    (hP : P = r * B + r ^ 4)
    (hE : E = r ^ 6 + (3 / 2 : F) * r ^ 3 * B +
      (3 / 8 : F) * B ^ 2) :
    r ^ 8 - 6 * P * r ^ 4 + 8 * E * r ^ 2 - 3 * P ^ 2 = 0 := by
  rw [hP, hE]
  ring

end LastAlignedStratum

end Max11DegreeRoutes
