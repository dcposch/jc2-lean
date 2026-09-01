import Grok410ScaleTwoThirteenthFaceScratch

/-! # Terminal tenth-face `ι` residual for the normalized `(4,10)` nonzero source

On the nonzero first face `H = h²` and `N = 5 p₃ H³ - 2 q₉ = λ h⁹` with
`h.natDegree = 1`, the thirteenth-face packet exhausts the Keller
coefficient tower: there is no unused Jacobian row below degree `0`.
The degree-`0` identity `W C' - B Z' = j` is not an exact first
integral, and none is constructed or cleared against `Z`.

The remaining exact tenth-face residual is `ι`, expanded in
`iotaResidual410_eq_expanded` from the source first integrals `α`
through `η` and the degree-`3` Jacobian coordinate `Z`.  On the
verified twelfth/thirteenth jet — the first-integral defect
evaluations `2 vis = 5 p₁`, `8 w₇₃ = p₁ (30 t₂ - 9 λ)`,
`8 b₄₂ = 15 p₁²`, the fifth leftover, `64 b₃₁ = 15 p₁² (4 t₂ - 3 λ)`,
and `256 q₂ = p₁² (256 s₂₂ - 400 a₂₂ + 243 λ t₂ - 540 t₂²)` —
the order-`-3` polar coefficient of `ι` is exactly
`15 p₁³ (λ + 4 t₂) / 256`, and the order-`-2` coefficient is
`3 p₁²` times an explicit quartic in `(a₂₂, s₂₂, t₂, λ)`.
Combined with the three cofactor evaluations this is the strongest
honest terminal factorization: it does not force a unique vanishing
of `p₁(a)` or of `λ + 4 t₂(a)`, does not kill the ground constants
`α, β, γ, δ`, and does not claim that `ρ, ν, ξ` vanish individually.
The nonzero face does not close.

No total-degree or twice-prime theorem is used.  The aligned face
`N = 0` is not opened.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

/-! ## Order-three and order-two polar coefficients of `ι` -/

section TerminalIotaPolar410

variable {F : Type*} [Field F] [CharZero F]

/-- Order-`-3` polar coefficient of `ι` on the depressed jet, assembled
from the source expansion `iotaResidual410_eq_expanded`. -/
def iotaOrderThree410 (a1 t2 vis w73 b31 b42 lam : F) : F :=
  (3 / 8 : F) * a1 ^ 3 * lam + (5 / 8 : F) * a1 ^ 3 * t2 -
    (7 / 4 : F) * a1 ^ 2 * t2 * vis + (3 / 4 : F) * a1 ^ 2 * w73 -
    (3 / 4 : F) * a1 * b31 + a1 * b42 * t2

/-- Order-`-2` polar coefficient of `ι` on the depressed jet. -/
def iotaOrderTwo410 (a0 a1 t2 a22 s22 vis w73 q54 b42 b31 b2 lam : F) :
    F :=
  -(5 / 2 : F) * a0 * a1 ^ 2 + (7 / 4 : F) * a0 * a1 * vis - a0 * b42 +
    (15 / 4 : F) * a1 ^ 2 * a22 ^ 2 -
    (27 / 8 : F) * a1 ^ 2 * a22 * lam * t2 -
    (2 : F) * a1 ^ 2 * a22 * s22 + (15 / 8 : F) * a1 ^ 2 * a22 * t2 ^ 2 +
    (9 / 4 : F) * a1 ^ 2 * lam * t2 ^ 3 +
    (3 : F) * a1 ^ 2 * s22 * t2 ^ 2 - (5 : F) * a1 ^ 2 * t2 ^ 4 -
    (7 / 4 : F) * a1 * a22 ^ 2 * vis + (5 / 4 : F) * a1 * a22 * q54 +
    (21 / 4 : F) * a1 * a22 * t2 ^ 2 * vis -
    (3 : F) * a1 * a22 * t2 * w73 - (5 / 4 : F) * a1 * q54 * t2 ^ 2 -
    (7 / 4 : F) * a1 * t2 ^ 4 * vis + (3 / 2 : F) * a1 * t2 ^ 3 * w73 +
    (1 / 2 : F) * a22 ^ 2 * b42 - (1 / 2 : F) * a22 * b2 +
    (3 / 4 : F) * a22 * b31 * t2 - a22 * b42 * t2 ^ 2 +
    (1 / 4 : F) * b2 * t2 ^ 2 - (1 / 4 : F) * b31 * t2 ^ 3 +
    (1 / 4 : F) * b42 * t2 ^ 4

/-- The order-`-3` coefficient is the most polar part of the source
expansion of `ι`: the `B U`, `B² R`, `B C Q`, `C T`, `L B³`, and
`B² C` terms of `iotaResidual410_eq_expanded`. -/
theorem iotaOrderThree410_from_expanded (a1 t2 vis w73 b31 b42 lam : F) :
    iotaOrderThree410 a1 t2 vis w73 b31 b42 lam =
      -(3 / 4 : F) * a1 * (b31 - t2 * b42) +
        (3 / 4 : F) * a1 ^ 2 *
          (-(7 / 4 : F) * t2 * vis + w73) +
        (7 / 4 : F) * a1 * (-(1 / 4 : F) * a1 * t2) * vis +
        (-(-(1 / 4 : F) * a1 * t2) * b42) +
        -(3 / 4 : F) * (-(1 / 2 : F) * lam) * a1 ^ 3 +
        -(5 / 2 : F) * a1 ^ 2 * (-(1 / 4 : F) * a1 * t2) := by
  simp only [iotaOrderThree410]
  ring

/-- On the twelfth/thirteenth jet the order-`-3` coefficient factors as
`15 p₁³ (λ + 4 t₂) / 256`. -/
theorem terminalIota_orderThree_onJet410 (a1 t2 vis w73 b31 b42 lam : F)
    (hT : (64 : F) * vis - (160 : F) * a1 = 0)
    (hU : (8 : F) * w73 = a1 * ((30 : F) * t2 - (9 : F) * lam))
    (hW : (8 : F) * b42 = (15 : F) * a1 ^ 2)
    (hX : (64 : F) * b31 =
      (15 : F) * a1 ^ 2 * ((4 : F) * t2 - (3 : F) * lam)) :
    iotaOrderThree410 a1 t2 vis w73 b31 b42 lam =
      (15 / 256 : F) * a1 ^ 3 * (lam + (4 : F) * t2) := by
  have hU0 : (8 : F) * w73 -
      a1 * ((30 : F) * t2 - (9 : F) * lam) = 0 := by
    linear_combination hU
  have hW0 : (8 : F) * b42 - (15 : F) * a1 ^ 2 = 0 := by
    linear_combination hW
  have hX0 : (64 : F) * b31 -
      (15 : F) * a1 ^ 2 * ((4 : F) * t2 - (3 : F) * lam) = 0 := by
    linear_combination hX
  have hid :
      (256 : F) * iotaOrderThree410 a1 t2 vis w73 b31 b42 lam -
          (15 : F) * a1 ^ 3 * (lam + (4 : F) * t2) =
        (-(7 : F) * a1 ^ 2 * t2) *
            ((64 : F) * vis - (160 : F) * a1) +
          (24 : F) * a1 ^ 2 *
            ((8 : F) * w73 -
              a1 * ((30 : F) * t2 - (9 : F) * lam)) +
          (32 : F) * a1 * t2 *
            ((8 : F) * b42 - (15 : F) * a1 ^ 2) +
          (-(3 : F) * a1) *
            ((64 : F) * b31 -
              (15 : F) * a1 ^ 2 * ((4 : F) * t2 - (3 : F) * lam)) := by
    simp only [iotaOrderThree410]
    ring
  have h256 : (256 : F) ≠ 0 := by norm_num
  have hcomb :
      (256 : F) * iotaOrderThree410 a1 t2 vis w73 b31 b42 lam -
          (15 : F) * a1 ^ 3 * (lam + (4 : F) * t2) =
        0 := by
    rw [hid]
    linear_combination (-(7 : F) * a1 ^ 2 * t2) * hT +
      (24 : F) * a1 ^ 2 * hU0 + (32 : F) * a1 * t2 * hW0 +
        (-(3 : F) * a1) * hX0
  have hmul :
      (256 : F) *
          (iotaOrderThree410 a1 t2 vis w73 b31 b42 lam -
            (15 / 256 : F) * a1 ^ 3 * (lam + (4 : F) * t2)) =
        (256 : F) * iotaOrderThree410 a1 t2 vis w73 b31 b42 lam -
          (15 : F) * a1 ^ 3 * (lam + (4 : F) * t2) := by
    ring
  have : (256 : F) *
        (iotaOrderThree410 a1 t2 vis w73 b31 b42 lam -
          (15 / 256 : F) * a1 ^ 3 * (lam + (4 : F) * t2)) =
      0 := by
    rw [hmul, hcomb]
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h256)

/-- On the twelfth/thirteenth jet the order-`-2` coefficient factors as
`3 p₁² (-160 a₂₂² + 18 a₂₂ λ t₂ + 440 a₂₂ t₂² - 27 λ t₂³ + 256 s₂₂ t₂² - 180 t₂⁴) / 1024`. -/
theorem terminalIota_orderTwo_onJet410 (a0 a1 t2 a22 s22 vis w73 q54 b42
    b31 b2 lam : F)
    (hT : (64 : F) * vis - (160 : F) * a1 = 0)
    (hU : (8 : F) * w73 = a1 * ((30 : F) * t2 - (9 : F) * lam))
    (hW : (8 : F) * b42 = (15 : F) * a1 ^ 2)
    (hV : (32 : F) * q54 + (40 : F) * a1 * a22 - (64 : F) * a1 * s22 -
        (27 : F) * a1 * lam * t2 + (90 : F) * a1 * t2 ^ 2 =
      0)
    (hX : (64 : F) * b31 =
      (15 : F) * a1 ^ 2 * ((4 : F) * t2 - (3 : F) * lam))
    (hY : (256 : F) * b2 =
      a1 ^ 2 *
        ((256 : F) * s22 - (400 : F) * a22 + (243 : F) * lam * t2 -
          (540 : F) * t2 ^ 2)) :
    iotaOrderTwo410 a0 a1 t2 a22 s22 vis w73 q54 b42 b31 b2 lam =
      (3 / 1024 : F) * a1 ^ 2 *
        (-(160 : F) * a22 ^ 2 + (18 : F) * a22 * lam * t2 +
          (440 : F) * a22 * t2 ^ 2 - (27 : F) * lam * t2 ^ 3 +
          (256 : F) * s22 * t2 ^ 2 - (180 : F) * t2 ^ 4) := by
  have hU0 : (8 : F) * w73 -
      a1 * ((30 : F) * t2 - (9 : F) * lam) = 0 := by
    linear_combination hU
  have hW0 : (8 : F) * b42 - (15 : F) * a1 ^ 2 = 0 := by
    linear_combination hW
  have hX0 : (64 : F) * b31 -
      (15 : F) * a1 ^ 2 * ((4 : F) * t2 - (3 : F) * lam) = 0 := by
    linear_combination hX
  have hY0 : (256 : F) * b2 -
      a1 ^ 2 *
        ((256 : F) * s22 - (400 : F) * a22 + (243 : F) * lam * t2 -
          (540 : F) * t2 ^ 2) =
      0 := by
    linear_combination hY
  have hid :
      (1024 : F) *
            iotaOrderTwo410 a0 a1 t2 a22 s22 vis w73 q54 b42 b31 b2
              lam -
          (3 : F) * a1 ^ 2 *
            (-(160 : F) * a22 ^ 2 + (18 : F) * a22 * lam * t2 +
              (440 : F) * a22 * t2 ^ 2 - (27 : F) * lam * t2 ^ 3 +
              (256 : F) * s22 * t2 ^ 2 - (180 : F) * t2 ^ 4) =
        (-(28 : F) * a1 *
              (-a0 + a22 ^ 2 - (3 : F) * a22 * t2 ^ 2 + t2 ^ 4)) *
            ((64 : F) * vis - (160 : F) * a1) +
          (192 : F) * a1 * t2 * (-(2 : F) * a22 + t2 ^ 2) *
            ((8 : F) * w73 -
              a1 * ((30 : F) * t2 - (9 : F) * lam)) +
          (32 : F) *
              (-(4 : F) * a0 + (2 : F) * a22 ^ 2 -
                (4 : F) * a22 * t2 ^ 2 + t2 ^ 4) *
            ((8 : F) * b42 - (15 : F) * a1 ^ 2) +
          (-(40 : F) * a1 * (-a22 + t2 ^ 2)) *
            ((32 : F) * q54 + (40 : F) * a1 * a22 -
              (64 : F) * a1 * s22 - (27 : F) * a1 * lam * t2 +
              (90 : F) * a1 * t2 ^ 2) +
          (-(4 : F) * t2 * (-(3 : F) * a22 + t2 ^ 2)) *
            ((64 : F) * b31 -
              (15 : F) * a1 ^ 2 * ((4 : F) * t2 - (3 : F) * lam)) +
          (-(2 : F) * a22 + t2 ^ 2) *
            ((256 : F) * b2 -
              a1 ^ 2 *
                ((256 : F) * s22 - (400 : F) * a22 +
                  (243 : F) * lam * t2 - (540 : F) * t2 ^ 2)) := by
    simp only [iotaOrderTwo410]
    ring
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have hcomb :
      (1024 : F) *
            iotaOrderTwo410 a0 a1 t2 a22 s22 vis w73 q54 b42 b31 b2
              lam -
          (3 : F) * a1 ^ 2 *
            (-(160 : F) * a22 ^ 2 + (18 : F) * a22 * lam * t2 +
              (440 : F) * a22 * t2 ^ 2 - (27 : F) * lam * t2 ^ 3 +
              (256 : F) * s22 * t2 ^ 2 - (180 : F) * t2 ^ 4) =
        0 := by
    rw [hid]
    linear_combination
      (-(28 : F) * a1 *
            (-a0 + a22 ^ 2 - (3 : F) * a22 * t2 ^ 2 + t2 ^ 4)) *
          hT +
        (192 : F) * a1 * t2 * (-(2 : F) * a22 + t2 ^ 2) * hU0 +
          (32 : F) *
              (-(4 : F) * a0 + (2 : F) * a22 ^ 2 -
                (4 : F) * a22 * t2 ^ 2 + t2 ^ 4) *
            hW0 +
            (-(40 : F) * a1 * (-a22 + t2 ^ 2)) * hV +
              (-(4 : F) * t2 * (-(3 : F) * a22 + t2 ^ 2)) * hX0 +
                (-(2 : F) * a22 + t2 ^ 2) * hY0
  have hmul :
      (1024 : F) *
          (iotaOrderTwo410 a0 a1 t2 a22 s22 vis w73 q54 b42 b31 b2 lam -
            (3 / 1024 : F) * a1 ^ 2 *
              (-(160 : F) * a22 ^ 2 + (18 : F) * a22 * lam * t2 +
                (440 : F) * a22 * t2 ^ 2 - (27 : F) * lam * t2 ^ 3 +
                (256 : F) * s22 * t2 ^ 2 - (180 : F) * t2 ^ 4)) =
        (1024 : F) *
            iotaOrderTwo410 a0 a1 t2 a22 s22 vis w73 q54 b42 b31 b2
              lam -
          (3 : F) * a1 ^ 2 *
            (-(160 : F) * a22 ^ 2 + (18 : F) * a22 * lam * t2 +
              (440 : F) * a22 * t2 ^ 2 - (27 : F) * lam * t2 ^ 3 +
              (256 : F) * s22 * t2 ^ 2 - (180 : F) * t2 ^ 4) := by
    ring
  have : (1024 : F) *
        (iotaOrderTwo410 a0 a1 t2 a22 s22 vis w73 q54 b42 b31 b2 lam -
          (3 / 1024 : F) * a1 ^ 2 *
            (-(160 : F) * a22 ^ 2 + (18 : F) * a22 * lam * t2 +
              (440 : F) * a22 * t2 ^ 2 - (27 : F) * lam * t2 ^ 3 +
              (256 : F) * s22 * t2 ^ 2 - (180 : F) * t2 ^ 4)) =
      0 := by
    rw [hmul, hcomb]
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h1024)

/-- Combined polar factorization of `ι` on the twelfth/thirteenth jet
together with the three thirteenth-face cofactor identities.  The
factors `p₁` and `λ + 4 t₂` are not claimed to vanish separately, and
`ρ, ν, ξ` are not claimed to vanish except through the displayed
`p₁` cofactors. -/
theorem terminalIota_jetFactorization410 (a0 a1 t2 a22 s22 vis w73 q54
    b42 b31 b2 rho nu xi lam : F)
    (hT : (64 : F) * vis - (160 : F) * a1 = 0)
    (hU : (8 : F) * w73 = a1 * ((30 : F) * t2 - (9 : F) * lam))
    (hW : (8 : F) * b42 = (15 : F) * a1 ^ 2)
    (hV : (32 : F) * q54 + (40 : F) * a1 * a22 - (64 : F) * a1 * s22 -
        (27 : F) * a1 * lam * t2 + (90 : F) * a1 * t2 ^ 2 =
      0)
    (hX : (64 : F) * b31 =
      (15 : F) * a1 ^ 2 * ((4 : F) * t2 - (3 : F) * lam))
    (hY : (256 : F) * b2 =
      a1 ^ 2 *
        ((256 : F) * s22 - (400 : F) * a22 + (243 : F) * lam * t2 -
          (540 : F) * t2 ^ 2))
    (hW1 : rho + (48 : F) * a1 *
          ((64 : F) * t2 * s22 + (40 : F) * t2 * a22 -
            (24 : F) * lam * a22 + (27 : F) * lam * t2 ^ 2 -
            (90 : F) * t2 ^ 3) =
        0)
    (hX1 : nu + (256 : F) * a1 *
          (-(320 : F) * a22 ^ 2 + (512 : F) * a22 * s22 -
            (1560 : F) * a22 * t2 ^ 2 + (720 : F) * lam * a22 * t2 -
            (1344 : F) * s22 * t2 ^ 2 - (567 : F) * lam * t2 ^ 3 +
            (1890 : F) * t2 ^ 4) =
        0)
    (hY1 : xi + (96 : F) * a1 *
          ((288 : F) * lam * a22 ^ 2 - (160 : F) * t2 * a22 ^ 2 -
            (1280 : F) * t2 * a22 * s22 -
            (900 : F) * lam * t2 ^ 2 * a22 +
            (2400 : F) * t2 ^ 3 * a22 + (960 : F) * t2 ^ 3 * s22 +
            (405 : F) * lam * t2 ^ 4 - (1350 : F) * t2 ^ 5) =
        0) :
    iotaOrderThree410 a1 t2 vis w73 b31 b42 lam =
          (15 / 256 : F) * a1 ^ 3 * (lam + (4 : F) * t2) ∧
      iotaOrderTwo410 a0 a1 t2 a22 s22 vis w73 q54 b42 b31 b2 lam =
          (3 / 1024 : F) * a1 ^ 2 *
            (-(160 : F) * a22 ^ 2 + (18 : F) * a22 * lam * t2 +
              (440 : F) * a22 * t2 ^ 2 - (27 : F) * lam * t2 ^ 3 +
              (256 : F) * s22 * t2 ^ 2 - (180 : F) * t2 ^ 4) ∧
      rho + (48 : F) * a1 *
            ((64 : F) * t2 * s22 + (40 : F) * t2 * a22 -
              (24 : F) * lam * a22 + (27 : F) * lam * t2 ^ 2 -
              (90 : F) * t2 ^ 3) =
          0 ∧
      nu + (256 : F) * a1 *
            (-(320 : F) * a22 ^ 2 + (512 : F) * a22 * s22 -
              (1560 : F) * a22 * t2 ^ 2 + (720 : F) * lam * a22 * t2 -
              (1344 : F) * s22 * t2 ^ 2 - (567 : F) * lam * t2 ^ 3 +
              (1890 : F) * t2 ^ 4) =
          0 ∧
      xi + (96 : F) * a1 *
            ((288 : F) * lam * a22 ^ 2 - (160 : F) * t2 * a22 ^ 2 -
              (1280 : F) * t2 * a22 * s22 -
              (900 : F) * lam * t2 ^ 2 * a22 +
              (2400 : F) * t2 ^ 3 * a22 + (960 : F) * t2 ^ 3 * s22 +
              (405 : F) * lam * t2 ^ 4 - (1350 : F) * t2 ^ 5) =
          0 :=
  ⟨terminalIota_orderThree_onJet410 a1 t2 vis w73 b31 b42 lam hT hU hW
      hX,
    terminalIota_orderTwo_onJet410 a0 a1 t2 a22 s22 vis w73 q54 b42 b31
      b2 lam hT hU hW hV hX hY,
    hW1, hX1, hY1⟩

/-- The `p₁ = 0` branch of the order-three factor forces the three
thirteenth-face cofactors to vanish at the root.  The complementary
branch `λ + 4 t₂ = 0` is not eliminated. -/
theorem terminalIota_a1_zero_cofactors410 (rho nu xi a1 t2 a22 s22 lam :
    F)
    (ha1 : a1 = 0)
    (hW1 : rho + (48 : F) * a1 *
          ((64 : F) * t2 * s22 + (40 : F) * t2 * a22 -
            (24 : F) * lam * a22 + (27 : F) * lam * t2 ^ 2 -
            (90 : F) * t2 ^ 3) =
        0)
    (hX1 : nu + (256 : F) * a1 *
          (-(320 : F) * a22 ^ 2 + (512 : F) * a22 * s22 -
            (1560 : F) * a22 * t2 ^ 2 + (720 : F) * lam * a22 * t2 -
            (1344 : F) * s22 * t2 ^ 2 - (567 : F) * lam * t2 ^ 3 +
            (1890 : F) * t2 ^ 4) =
        0)
    (hY1 : xi + (96 : F) * a1 *
          ((288 : F) * lam * a22 ^ 2 - (160 : F) * t2 * a22 ^ 2 -
            (1280 : F) * t2 * a22 * s22 -
            (900 : F) * lam * t2 ^ 2 * a22 +
            (2400 : F) * t2 ^ 3 * a22 + (960 : F) * t2 ^ 3 * s22 +
            (405 : F) * lam * t2 ^ 4 - (1350 : F) * t2 ^ 5) =
        0) :
    rho = 0 ∧ nu = 0 ∧ xi = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [ha1] using hW1
  · simpa [ha1] using hX1
  · simpa [ha1] using hY1

end TerminalIotaPolar410

#print axioms iotaOrderThree410_from_expanded
#print axioms terminalIota_orderThree_onJet410
#print axioms terminalIota_orderTwo_onJet410
#print axioms terminalIota_jetFactorization410
#print axioms terminalIota_a1_zero_cofactors410

end Max11DegreeRoutes
