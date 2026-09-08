import Grok810ScaleZeroQuarticLoadLadderScratch

/-! # All-constant corner, `(8,10)` scale zero (the `θ`/`B³` tie on `A⁴`)

`quarticAllConstantCorner810_impossible`: cone `A`, `l = β = δ = ζ = 0`,
every letter `B,…,G` of `natDegree 0`, and
`derivative Π = C (j/t) ≠ 0` is impossible.

The assembly-core `hcorner` binder (lines 81-91 of
`Grok810ScaleZeroQuarticAssemblyCoreScratch.lean`) records only `Π`.
That statement is not true of `Π` alone: CAS with constant letters
gives `Π`'s `A⁴` coefficient `5(−B³ + 16 θ)/65536`, so `θ = B³/16`
cancels the face, and if the other letters vanish the remainder is
`(69/8192) B⁵ A` of degree `a`.  Plan §2.3 / §4.3 therefore use the
packet: `κ`'s `A¹` coefficient `(5/512) B³ + θ/8` together with `Π`'s
`A⁴` is the 2×2 of determinant `45/2097152 ≠ 0`, forcing `B = θ = 0`;
then `μ`'s `A¹` kills `D` and `π`'s `A¹` kills `F`; then File A's
`quarticParityCorner_BDF_zero_impossible`.  The six `natDegree = 0`
hypotheses are exactly the packet degrees the residual already has at
the `hcorner` call site.

CAS `scripts/_tmp_810_constant_corner_cas.py` (from
`out_810_scale_zero_quartic_coordinates.json`).  No `sorry`, no new
axioms, no finite-root shortcut.  Untracked working note.
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

/-! ## `κ` as `A · K₁ + K₀` with constant letters -/

/-- The `A¹` coefficient of `κ` at `l = β = δ = ζ = 0`:
`(5/512) B³ + θ/8`. -/
def kappaQuarticA1Coeff810 (theta : k) (B : k[X]) : k[X] :=
  (5 / 512 : k) • B ^ 3 + C (1 / 8 * theta)

/-- The `A⁰` part of `κ` at `l = β = δ = ζ = 0`. -/
def kappaQuarticA0Rest810 (gamma epsilon eta : k)
    (B C D E F G : k[X]) : k[X] :=
  (-(15 / 128 : k)) • (B ^ 2 * D)
  - (15 / 128 : k) • (B * C ^ 2)
  + (5 / 16 : k) • (B * G)
  + (5 / 16 : k) • (C * F)
  + (5 / 16 : k) • (D * E)
  - (3 / 16 * gamma : k) • (B * C)
  + (3 / 4 * gamma : k) • F
  + (1 / 2 * epsilon : k) • D
  + (1 / 4 * eta : k) • B

set_option maxHeartbeats 64000000 in
/-- `κ = A · K₁ + K₀` after the four odd loads below `θ` are 0. -/
theorem degreeZeroKappaQuartic810_eq_A_mul_coeff
    (gamma epsilon eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 0 0 gamma 0 epsilon 0 eta theta
        A B C D E F G =
      A * kappaQuarticA1Coeff810 theta B +
        kappaQuarticA0Rest810 gamma epsilon eta B C D E F G := by
  simp only [degreeZeroKappaQuartic810, kappaQuarticA1Coeff810,
    kappaQuarticA0Rest810, zero_mul, mul_zero, zero_smul, smul_zero,
    add_zero, zero_add, sub_zero, neg_zero, sub_self]
  -- remaining: `(5/512) • (A * B³) + (θ/8) • A = A * ((5/512) • B³ + C(θ/8))`
  simp [smul_eq_C_mul, mul_add, mul_assoc, mul_left_comm, mul_comm]
  abel

set_option maxHeartbeats 64000000 in
theorem kappaQuarticA1Coeff810_natDegree_eq_zero
    (theta : k) {B : k[X]} (hB : B.natDegree = 0) :
    (kappaQuarticA1Coeff810 theta B).natDegree = 0 := by
  have hB3 : ((5 / 512 : k) • B ^ 3).natDegree ≤ 0 :=
    (natDegree_smul_le810 _ _).trans (by rw [natDegree_pow, hB])
  have hC : (C (1 / 8 * theta) : k[X]).natDegree = 0 := natDegree_C _
  exact natDegree_eq_zero_of_le_zero <|
    (natDegree_add_le _ _).trans (max_le hB3 hC.le)

set_option maxHeartbeats 64000000 in
theorem kappaQuarticA0Rest810_natDegree_eq_zero
    (gamma epsilon eta : k) {B C D E F G : k[X]}
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (kappaQuarticA0Rest810 gamma epsilon eta B C D E F G).natDegree = 0 := by
  have hle : (kappaQuarticA0Rest810 gamma epsilon eta B C D E F G).natDegree ≤
      0 := by
    simp only [kappaQuarticA0Rest810]
    compute_degree
    omega
  exact natDegree_eq_zero_of_le_zero hle

set_option maxHeartbeats 64000000 in
/-- `natDegree κ = 0` and constant letters force the `A¹` coefficient to
vanish (otherwise `natDegree κ = a > 0`). -/
theorem kappaQuarticA1Coeff810_eq_zero_of_natDegree
    (gamma epsilon eta theta : k) (A B C D E F G : k[X])
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 0 0 gamma 0 epsilon 0 eta theta
          A B C D E F G).natDegree = 0) :
    kappaQuarticA1Coeff810 theta B = 0 := by
  by_contra hne
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hKdeg := kappaQuarticA1Coeff810_natDegree_eq_zero theta hB
  have hlead : (A * kappaQuarticA1Coeff810 theta B).natDegree =
      A.natDegree := by
    rw [natDegree_mul hAne hne, hKdeg, add_zero]
  have hrest :
      (kappaQuarticA0Rest810 gamma epsilon eta B C D E F G).natDegree <
        A.natDegree := by
    have := kappaQuarticA0Rest810_natDegree_eq_zero gamma epsilon eta
      hB hC hD hE hF hG
    omega
  rw [degreeZeroKappaQuartic810_eq_A_mul_coeff,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hkap
  omega

/-! ## `Π` as `A⁴ · P₄ + rest` with constant letters -/

/-- The `A⁴` coefficient of `Π` at `l = β = δ = ζ = 0`:
`−(5/65536) B³ + (5/4096) θ`. -/
def primitiveQuarticA4Coeff810 (theta : k) (B : k[X]) : k[X] :=
  (-(5 / 65536 : k)) • B ^ 3 + C ((5 / 4096 : k) * theta)

set_option maxHeartbeats 64000000 in
def rhoBaseLetters1QuarticNoA4B3810
    (A B C D E F G : k[X]) : k[X] :=
  (-(15 / 16384 : k)) • (A ^ 3 * B ^ 2 * D)
  + (15 / 16384 : k) • (A ^ 3 * B * C ^ 2)
  + (15 / 8192 : k) • (A ^ 2 * B ^ 3 * C)
  + (65 / 8192 : k) • (A * B ^ 5)
  - (5 / 2048 : k) • (A ^ 3 * B * G)
  - (5 / 2048 : k) • (A ^ 3 * C * F)
  - (5 / 2048 : k) • (A ^ 3 * D * E)
  - (5 / 2048 : k) • (A ^ 2 * B ^ 2 * F)
  + (15 / 1024 : k) • (A ^ 2 * B * C * E)
  - (25 / 2048 : k) • (A ^ 2 * B * D ^ 2)
  + (15 / 2048 : k) • (A ^ 2 * C ^ 2 * D)
  - (25 / 512 : k) • (A * B ^ 3 * E)
  - (135 / 1024 : k) • (A * B ^ 2 * C * D)
  - (15 / 1024 : k) • (A * B * C ^ 3)
  - (125 / 2048 : k) • (B ^ 4 * D)
  - (265 / 2048 : k) • (B ^ 3 * C ^ 2)
  - (5 / 256 : k) • (A ^ 2 * D * G)
  - (5 / 256 : k) • (A ^ 2 * E * F)

def rhoThetaGroupQuarticNoA4810
    (A B C D E G : k[X]) : k[X] :=
  (3 / 128 : k) • (A ^ 2 * C)
  + (1 / 128 : k) • (A * B ^ 2)
  + (1 / 8 : k) • (A * E)
  - (1 / 8 : k) • (B * D)
  - (1 / 16 : k) • C ^ 2
  + (1 : k) • G

set_option maxHeartbeats 64000000 in
def degreeZeroPrimitiveQuarticNoA4_l0beta0delta0zeta0810
    (gamma epsilon eta theta : k)
    (A B C D E F G : k[X]) : k[X] :=
  rhoBaseLetters1QuarticNoA4B3810 A B C D E F G +
    rhoBaseLetters2Quartic810 A B C D E F G +
    gamma • rhoGammaGroupQuartic810 A B C D E F +
    epsilon • rhoEpsilonGroupQuartic810 A B C D E F +
    eta • rhoEtaGroupQuartic810 A B C D E F +
    theta • rhoThetaGroupQuarticNoA4810 A B C D E G

set_option maxHeartbeats 64000000 in
theorem rhoBaseLetters1Quartic810_eq_A4B3_add_rest
    (A B C D E F G : k[X]) :
    rhoBaseLetters1Quartic810 A B C D E F G =
      (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3) +
        rhoBaseLetters1QuarticNoA4B3810 A B C D E F G := by
  simp only [rhoBaseLetters1Quartic810, rhoBaseLetters1QuarticNoA4B3810]
  module

theorem rhoThetaGroupQuartic810_eq_A4_add_rest
    (A B C D E G : k[X]) :
    rhoThetaGroupQuartic810 A B C D E G =
      (5 / 4096 : k) • A ^ 4 +
        rhoThetaGroupQuarticNoA4810 A B C D E G := by
  simp only [rhoThetaGroupQuartic810, rhoThetaGroupQuarticNoA4810]
  module

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticA4_mul_coeff
    (theta : k) (A B : k[X]) :
    A ^ 4 * primitiveQuarticA4Coeff810 theta B =
      (-(5 / 65536 : k)) • (A ^ 4 * B ^ 3) +
        (5 / 4096 * theta : k) • A ^ 4 := by
  simp only [primitiveQuarticA4Coeff810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitiveQuartic810_eq_A4_mul_coeff
    (gamma epsilon eta theta : k) (A B C D E F G : k[X]) :
    degreeZeroPrimitiveQuartic810 0 0 gamma 0 epsilon 0 eta theta
        A B C D E F G =
      A ^ 4 * primitiveQuarticA4Coeff810 theta B +
        degreeZeroPrimitiveQuarticNoA4_l0beta0delta0zeta0810 gamma epsilon
          eta theta A B C D E F G := by
  calc
    degreeZeroPrimitiveQuartic810 0 0 gamma 0 epsilon 0 eta theta
          A B C D E F G =
        rhoBaseLetters1Quartic810 A B C D E F G +
          rhoBaseLetters2Quartic810 A B C D E F G +
          gamma • rhoGammaGroupQuartic810 A B C D E F +
          epsilon • rhoEpsilonGroupQuartic810 A B C D E F +
          eta • rhoEtaGroupQuartic810 A B C D E F +
          theta • rhoThetaGroupQuartic810 A B C D E G := by
      simp only [degreeZeroPrimitiveQuartic810,
        rhoBaseGroupQuartic810_eq_letters_of_l_zero, zero_smul, add_zero,
        zero_add]
    _ = ((-(5 / 65536 : k)) • (A ^ 4 * B ^ 3) +
            rhoBaseLetters1QuarticNoA4B3810 A B C D E F G) +
          rhoBaseLetters2Quartic810 A B C D E F G +
          gamma • rhoGammaGroupQuartic810 A B C D E F +
          epsilon • rhoEpsilonGroupQuartic810 A B C D E F +
          eta • rhoEtaGroupQuartic810 A B C D E F +
          theta • ((5 / 4096 : k) • A ^ 4 +
            rhoThetaGroupQuarticNoA4810 A B C D E G) := by
      simp only [rhoBaseLetters1Quartic810_eq_A4B3_add_rest,
        rhoThetaGroupQuartic810_eq_A4_add_rest]
    _ = ((-(5 / 65536 : k)) • (A ^ 4 * B ^ 3) +
            (5 / 4096 * theta : k) • A ^ 4) +
          (rhoBaseLetters1QuarticNoA4B3810 A B C D E F G +
            rhoBaseLetters2Quartic810 A B C D E F G +
            gamma • rhoGammaGroupQuartic810 A B C D E F +
            epsilon • rhoEpsilonGroupQuartic810 A B C D E F +
            eta • rhoEtaGroupQuartic810 A B C D E F +
            theta • rhoThetaGroupQuarticNoA4810 A B C D E G) := by
      have hth : theta • ((5 / 4096 : k) • A ^ 4) =
          (5 / 4096 * theta : k) • A ^ 4 := by
        rw [smul_smul, mul_comm]
      simp only [smul_add, hth]
      abel
    _ = A ^ 4 * primitiveQuarticA4Coeff810 theta B +
          degreeZeroPrimitiveQuarticNoA4_l0beta0delta0zeta0810 gamma epsilon
            eta theta A B C D E F G := by
      rw [primitiveQuarticA4_mul_coeff]
      simp only [degreeZeroPrimitiveQuarticNoA4_l0beta0delta0zeta0810]

set_option maxHeartbeats 64000000 in
theorem rhoBaseLetters1QuarticNoA4B3810_natDegree_le
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (rhoBaseLetters1QuarticNoA4B3810 A B C D E F G).natDegree ≤
      3 * A.natDegree := by
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  simp only [rhoBaseLetters1QuarticNoA4B3810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem rhoBaseLetters2Quartic810_natDegree_le_three
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (rhoBaseLetters2Quartic810 A B C D E F G).natDegree ≤
      3 * A.natDegree := by
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  simp only [rhoBaseLetters2Quartic810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem rhoThetaGroupQuarticNoA4810_natDegree_le
    {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (rhoThetaGroupQuarticNoA4810 A B C D E G).natDegree ≤
      3 * A.natDegree := by
  have hA1 : 0 + 1 ≤ A.natDegree := Nat.succ_le_of_lt hApos
  simp only [rhoThetaGroupQuarticNoA4810]
  compute_degree
  omega

set_option maxHeartbeats 64000000 in
theorem degreeZeroPrimitiveQuarticNoA4_l0beta0delta0zeta0810_natDegree_le
    (gamma epsilon eta theta : k) {A B C D E F G : k[X]}
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (degreeZeroPrimitiveQuarticNoA4_l0beta0delta0zeta0810 gamma epsilon eta
          theta A B C D E F G).natDegree ≤
      3 * A.natDegree := by
  have h1 :=
    rhoBaseLetters1QuarticNoA4B3810_natDegree_le hApos hB hC hD hE hF hG
  have h2 :=
    rhoBaseLetters2Quartic810_natDegree_le_three hApos hB hC hD hE hF hG
  have hgamma := natDegree_smul_le_of_le810 gamma
    (rhoGammaGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
  have heps := natDegree_smul_le_of_le810 epsilon
    (rhoEpsilonGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
  have heta := natDegree_smul_le_of_le810 eta
    (rhoEtaGroupQuartic810_natDegree_le hApos hB hC hD hE hF hG)
  have htheta := natDegree_smul_le_of_le810 theta
    (rhoThetaGroupQuarticNoA4810_natDegree_le hApos hB hC hD hE hF hG)
  simp only [degreeZeroPrimitiveQuarticNoA4_l0beta0delta0zeta0810]
  exact natDegree_add_le810
    (natDegree_add_le810
      (natDegree_add_le810
        (natDegree_add_le810 (natDegree_add_le810 h1 h2) hgamma) heps)
      heta)
    htheta

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticA4Coeff810_natDegree_eq_zero
    (theta : k) {B : k[X]} (hB : B.natDegree = 0) :
    (primitiveQuarticA4Coeff810 theta B).natDegree = 0 := by
  have hB3 : ((-(5 / 65536 : k)) • B ^ 3).natDegree ≤ 0 :=
    (natDegree_smul_le810 _ _).trans (by rw [natDegree_pow, hB])
  have hC : (C ((5 / 4096 : k) * theta) : k[X]).natDegree = 0 :=
    natDegree_C _
  exact natDegree_eq_zero_of_le_zero <|
    (natDegree_add_le _ _).trans (max_le hB3 hC.le)

set_option maxHeartbeats 64000000 in
/-- `natDegree Π = 1` and constant letters force the `A⁴` coefficient to
vanish (otherwise `natDegree Π = 4 a > 1`). -/
theorem primitiveQuarticA4Coeff810_eq_zero_of_derivative
    {j t : k} (gamma epsilon eta theta : k) (A B C D E F G : k[X])
    (hApos : 0 < A.natDegree)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0)
    (hD : D.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 0 0 gamma 0 epsilon 0 eta theta
          A B C D E F G) =
      Polynomial.C (j / t)) :
    primitiveQuarticA4Coeff810 theta B = 0 := by
  by_contra hne
  have hdeg :
      (degreeZeroPrimitiveQuartic810 0 0 gamma 0 epsilon 0 eta theta
          A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hPdeg := primitiveQuarticA4Coeff810_natDegree_eq_zero theta hB
  have hlead : (A ^ 4 * primitiveQuarticA4Coeff810 theta B).natDegree =
      4 * A.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hAne) hne, natDegree_pow, hPdeg,
      add_zero]
  have hrest :
      (degreeZeroPrimitiveQuarticNoA4_l0beta0delta0zeta0810 gamma epsilon
            eta theta A B C D E F G).natDegree <
        4 * A.natDegree :=
    natDegree_lt_of_le_mul810
      (degreeZeroPrimitiveQuarticNoA4_l0beta0delta0zeta0810_natDegree_le
        gamma epsilon eta theta hApos hB hC hD hE hF hG)
      (by omega : 3 < 4) hApos
  rw [degreeZeroPrimitiveQuartic810_eq_A4_mul_coeff,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead] at hdeg
  omega

/-! ## The 2×2 on `(B³, θ)`: determinant `45/2097152 ≠ 0` -/

set_option maxHeartbeats 64000000 in
theorem kappaA1_add_128_primitiveA4
    (theta : k) (B : k[X]) :
    kappaQuarticA1Coeff810 theta B +
        (128 : k) • primitiveQuarticA4Coeff810 theta B =
      C ((9 / 32 : k) * theta) := by
  simp only [kappaQuarticA1Coeff810, primitiveQuarticA4Coeff810]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 64000000 in
theorem quarticConstantCorner_theta_B_eq_zero
    (theta : k) (B : k[X])
    (hK : kappaQuarticA1Coeff810 theta B = 0)
    (hP : primitiveQuarticA4Coeff810 theta B = 0) :
    theta = 0 ∧ B = 0 := by
  have hsum :
      kappaQuarticA1Coeff810 theta B +
          (128 : k) • primitiveQuarticA4Coeff810 theta B =
        0 := by
    simp [hK, hP]
  rw [kappaA1_add_128_primitiveA4] at hsum
  have ht : (9 / 32 : k) * theta = 0 := C_eq_zero.mp hsum
  have h932 : (9 / 32 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have ht0 : theta = 0 := by
    rcases mul_eq_zero.mp ht with h | h
    · exact (h932 h).elim
    · exact h
  refine ⟨ht0, ?_⟩
  subst ht0
  have hB3 : (5 / 512 : k) • B ^ 3 = 0 := by
    simpa [kappaQuarticA1Coeff810, mul_zero, C_0, add_zero] using hK
  have h512 : (5 / 512 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hpow : B ^ 3 = 0 :=
    (smul_eq_zero.mp hB3).resolve_left h512
  exact (pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hpow

/-! ## `μ` after `B = 0`: the `A D²` column -/

def muQuarticAD2Face810 (A D : k[X]) : k[X] :=
  (-(5 / 128 : k)) • (A * D ^ 2)

def muQuarticNoAD2_B0810 (gamma epsilon eta : k)
    (C D E F G : k[X]) : k[X] :=
  (-(5 / 128 : k)) • C ^ 3
  - (3 / 32 * gamma : k) • C ^ 2
  + (1 / 4 * eta : k) • C
  + (5 / 16 : k) • (C * G)
  + (5 / 16 : k) • (D * F)
  + (5 / 32 : k) • E ^ 2
  + (1 / 2 * epsilon : k) • E
  + (3 / 4 * gamma : k) • G

set_option maxHeartbeats 64000000 in
theorem degreeZeroMuQuartic810_eq_AD2_of_B_zero
    (gamma epsilon eta theta : k) (A C D E F G : k[X]) :
    degreeZeroMuQuartic810 0 0 gamma 0 epsilon 0 eta theta
        A 0 C D E F G =
      muQuarticAD2Face810 A D +
        muQuarticNoAD2_B0810 gamma epsilon eta C D E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  simp only [degreeZeroMuQuartic810, muQuarticAD2Face810,
    muQuarticNoAD2_B0810, hpow2, hpow3, hpow4, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, zero_add, sub_zero, neg_zero,
    sub_self]
  module

set_option maxHeartbeats 64000000 in
theorem muQuarticNoAD2_B0810_natDegree_eq_zero
    (gamma epsilon eta : k) {C D E F G : k[X]}
    (hC : C.natDegree = 0) (hD : D.natDegree = 0)
    (hE : E.natDegree = 0) (hF : F.natDegree = 0)
    (hG : G.natDegree = 0) :
    (muQuarticNoAD2_B0810 gamma epsilon eta C D E F G).natDegree = 0 := by
  have hle : (muQuarticNoAD2_B0810 gamma epsilon eta C D E F G).natDegree ≤
      0 := by
    simp only [muQuarticNoAD2_B0810]
    compute_degree
    omega
  exact natDegree_eq_zero_of_le_zero hle

set_option maxHeartbeats 64000000 in
theorem quarticConstantCorner_D_eq_zero
    (gamma epsilon eta theta : k) (A C D E F G : k[X])
    (hApos : 0 < A.natDegree)
    (hC : C.natDegree = 0) (hD : D.natDegree = 0)
    (hE : E.natDegree = 0) (hF : F.natDegree = 0)
    (hG : G.natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 0 0 gamma 0 epsilon 0 eta theta
          A 0 C D E F G).natDegree = 0) :
    D = 0 := by
  by_contra hDne
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (5 / 128 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hD2 : D ^ 2 ≠ 0 := pow_ne_zero 2 hDne
  have hface : (muQuarticAD2Face810 A D).natDegree = A.natDegree := by
    simp only [muQuarticAD2Face810]
    have hsm : ((-(5 / 128 : k)) • (A * D ^ 2)).natDegree =
        (A * D ^ 2).natDegree :=
      natDegree_smul _ (neg_ne_zero.mpr hc)
    rw [hsm, natDegree_mul hAne hD2, natDegree_pow, hD]
    simp
  have hrest :
      (muQuarticNoAD2_B0810 gamma epsilon eta C D E F G).natDegree <
        A.natDegree := by
    have := muQuarticNoAD2_B0810_natDegree_eq_zero gamma epsilon eta
      hC hD hE hF hG
    omega
  rw [degreeZeroMuQuartic810_eq_AD2_of_B_zero,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hface]), hface] at hmu
  omega

/-! ## `π` after `B = D = θ = 0`: the `A F²` column -/

def piQuarticAF2Face810 (A F : k[X]) : k[X] :=
  (-(5 / 16 : k)) • (A * F ^ 2)

def piQuarticNoAF2_B0D0theta0810 (gamma epsilon eta : k)
    (C E F G : k[X]) : k[X] :=
  (15 / 256 : k) • C ^ 4
  + (1 / 8 * gamma : k) • C ^ 3
  - (5 / 16 : k) • (C ^ 2 * G)
  - (1 / 4 * eta : k) • C ^ 2
  - (5 / 8 : k) • (C * E ^ 2)
  - (1 * epsilon : k) • (C * E)
  - (3 / 4 * gamma : k) • E ^ 2
  + (5 / 4 : k) • G ^ 2
  + (2 * eta : k) • G

set_option maxHeartbeats 64000000 in
theorem degreeZeroPiQuartic810_eq_AF2_of_B_D_theta_zero
    (gamma epsilon eta : k) (A C E F G : k[X]) :
    degreeZeroPiQuartic810 0 0 gamma 0 epsilon 0 eta 0
        A 0 C 0 E F G =
      piQuarticAF2Face810 A F +
        piQuarticNoAF2_B0D0theta0810 gamma epsilon eta C E F G := by
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  simp only [degreeZeroPiQuartic810, piBaseGroupQuartic810,
    piBetaGroupQuartic810, piGammaGroupQuartic810, piDeltaGroupQuartic810,
    piEpsilonGroupQuartic810, piZetaGroupQuartic810, piEtaGroupQuartic810,
    piThetaGroupQuartic810, piQuarticAF2Face810,
    piQuarticNoAF2_B0D0theta0810, hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    sub_zero, neg_zero, sub_self]
  module

set_option maxHeartbeats 64000000 in
theorem piQuarticNoAF2_B0D0theta0810_natDegree_eq_zero
    (gamma epsilon eta : k) {C E F G : k[X]}
    (hC : C.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    (piQuarticNoAF2_B0D0theta0810 gamma epsilon eta C E F G).natDegree =
      0 := by
  have hle :
      (piQuarticNoAF2_B0D0theta0810 gamma epsilon eta C E F G).natDegree ≤
        0 := by
    simp only [piQuarticNoAF2_B0D0theta0810]
    compute_degree
    omega
  exact natDegree_eq_zero_of_le_zero hle

set_option maxHeartbeats 64000000 in
theorem quarticConstantCorner_F_eq_zero
    (gamma epsilon eta : k) (A C E F G : k[X])
    (hApos : 0 < A.natDegree)
    (hC : C.natDegree = 0) (hE : E.natDegree = 0)
    (hF : F.natDegree = 0) (hG : G.natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 0 0 gamma 0 epsilon 0 eta 0
          A 0 C 0 E F G).natDegree = 0) :
    F = 0 := by
  by_contra hFne
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hc : (5 / 16 : k) ≠ 0 :=
    div_ne_zero (by norm_num) (by norm_num)
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero 2 hFne
  have hface : (piQuarticAF2Face810 A F).natDegree = A.natDegree := by
    simp only [piQuarticAF2Face810]
    have hsm : ((-(5 / 16 : k)) • (A * F ^ 2)).natDegree =
        (A * F ^ 2).natDegree :=
      natDegree_smul _ (neg_ne_zero.mpr hc)
    rw [hsm, natDegree_mul hAne hF2, natDegree_pow, hF]
    simp
  have hrest :
      (piQuarticNoAF2_B0D0theta0810 gamma epsilon eta C E F G).natDegree <
        A.natDegree := by
    have := piQuarticNoAF2_B0D0theta0810_natDegree_eq_zero gamma epsilon eta
      hC hE hF hG
    omega
  rw [degreeZeroPiQuartic810_eq_AF2_of_B_D_theta_zero,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hface]), hface] at hpi
  omega

/-! ## The corner -/

set_option maxHeartbeats 64000000 in
/-- All-constant corner of cone `A` with `l = β = δ = ζ = 0`.

Binder: `j t gamma epsilon eta theta` and `A B C D E F G`, with the
four odd loads below `θ` already substituted to `0`, plus the six
packet `natDegree = 0` hypotheses the residual carries at the
`hcorner` call site (needed: `Π` alone does not kill the `θ = B³/16`
family).  Plan §2.3 2×2 then §4.3 parity. -/
theorem quarticAllConstantCorner810_impossible
    {j t : k}
    (gamma epsilon eta theta : k) (A B C D E F G : k[X])
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 0 0 gamma 0 epsilon 0 eta theta
          A B C D E F G) =
      Polynomial.C (j / t))
    (hxi : (degreeZeroXiQuartic810 0 0 gamma 0 epsilon 0 eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 0 0 gamma 0 epsilon 0 eta theta
          A B C D E F G).natDegree = 0)
    (homi : (degreeZeroOmicronQuartic810 0 0 gamma 0 epsilon 0 eta theta
          A B C D E F G).natDegree = 0)
    (hkap : (degreeZeroKappaQuartic810 0 0 gamma 0 epsilon 0 eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 0 0 gamma 0 epsilon 0 eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 0 0 gamma 0 epsilon 0 eta theta
          A B C D E F G).natDegree = 0)
    (hcone : QuarticRatioConeA810 A B C D E F G)
    (hB : B.natDegree = 0) (hC : C.natDegree = 0) (hD : D.natDegree = 0)
    (hE : E.natDegree = 0) (hF : F.natDegree = 0) (hG : G.natDegree = 0) :
    False := by
  have hApos : 0 < A.natDegree := hcone.1
  have hK0 :=
    kappaQuarticA1Coeff810_eq_zero_of_natDegree gamma epsilon eta theta
      A B C D E F G hApos hB hC hD hE hF hG hkap
  have hP0 :=
    primitiveQuarticA4Coeff810_eq_zero_of_derivative (j := j) (t := t)
      gamma epsilon eta theta A B C D E F G hApos hB hC hD hE hF hG
      hjdiv hder
  have ⟨ht0, hBz⟩ := quarticConstantCorner_theta_B_eq_zero theta B hK0 hP0
  subst ht0
  subst hBz
  have hDz :=
    quarticConstantCorner_D_eq_zero gamma epsilon eta 0 A C D E F G
      hApos hC hD hE hF hG (by simpa using hmu)
  subst hDz
  have hFz :=
    quarticConstantCorner_F_eq_zero gamma epsilon eta A C E F G
      hApos hC hE hF hG (by simpa using hpi)
  subst hFz
  exact quarticParityCorner_BDF_zero_impossible (j := j) (t := t)
    0 0 gamma 0 epsilon 0 eta 0 A 0 C 0 E 0 G
    rfl rfl rfl rfl rfl rfl rfl rfl hjdiv (by simpa using hder)

#print axioms quarticAllConstantCorner810_impossible

end Max11DegreeRoutes
