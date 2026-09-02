import LowScale68Integrated

/-! # Weight-13 degree-zero primitive for the depressed `(6,8)` leaf

Lane P0 of `Grok68AlignedSquareTowerPlanScratch.md`.  The committed
`(6,8)` local-root data integrated rows `h11` through `h3` of the
differential Jacobian of `depressedSextic68` and `depressedOctic68`, but
not the weight-11 row `h2` nor the last row
`h0 = U * dE - D * dV`.  This file records the missing weight-11 first
integral and the grouped weight-13 primitive produced by
`scripts/derive_68_degree_zero_residual.py`.

CAS job `20260902T110334Z-68-degree-zero-93934`
(command-source SHA256
`3ff4ba1012f52d90c5684545af9742b238dacf6b34fbad7ed02fd0db4a9e76f4`):

* Faber `g = Σ c_i f^{i/6}` matches `integratedP68` through
  `integratedV68`.  `firstIntegralFour68 = 6 * c_{-1}` and
  `firstIntegralThree68 = 6 * c_{-2}`.
* Row `h2` becomes exact after combining with row `h4`:
  `d(firstIntegralTwo68) = row₂ - (A/2) * row₄`.  The `h3` multiplier
  is identically `0`; row `h1` is not needed.
* `d(degreeZeroPrimitive68) = U dE - D dV` modulo rows `h11` through
  `h2` (certificate, not a closure theorem).  The primitive is
  weighted-homogeneous of weight 13.  Grouped integer scale `1119744`.
* Bookkeeping matches the plan: step `5`, weight `13`, clearing
  `5 * 13 = 65`.  Deviations: the alpha and eta groups vanish, so they
  are omitted from the primitive sum; `firstIntegralTwo68` is not a
  pure multiple of `c_{-3}`.

No source clearing, pole order, or chamber closure is claimed.
-/

noncomputable section

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

section DegreeZeroPrimitive68

variable {F : Type*} [Field F] [CharZero F]

/-- Weight-11 first integral of the unused Jacobian row `h2`, after the
row-`h4` correction `-A/2`.  Same residual arguments as
`firstIntegralFour68` / `firstIntegralThree68`. -/
def firstIntegralTwo68
    (L A B C0 D E beta gamma delta epsilon zeta : F) : F :=
  (-77 / 2592 : F) * L * A ^ 5 + (35 / 162 : F) * L * A ^ 3 * C0 +
    (35 / 96 : F) * L * A ^ 2 * B ^ 2 - (7 / 24 : F) * L * A ^ 2 * E -
    (7 / 9 : F) * L * A * B * D - (7 / 18 : F) * L * A * C0 ^ 2 -
    (35 / 72 : F) * L * B ^ 2 * C0 + (7 / 6 : F) * L * C0 * E +
    (7 / 12 : F) * L * D ^ 2 - (20 / 81 : F) * A ^ 4 * B -
    (35 / 576 : F) * A ^ 4 * beta + (28 / 81 : F) * A ^ 3 * D +
    (1 / 4 : F) * A ^ 3 * delta + (32 / 27 : F) * A ^ 2 * B * C0 +
    (2 / 3 : F) * A ^ 2 * B * gamma + (25 / 72 : F) * A ^ 2 * C0 * beta -
    (1 / 4 : F) * A ^ 2 * zeta + (4 / 9 : F) * A * B ^ 3 +
    (5 / 12 : F) * A * B ^ 2 * beta - (4 / 3 : F) * A * B * E -
    A * B * epsilon - (4 / 3 : F) * A * C0 * D - A * C0 * delta -
    (2 / 3 : F) * A * D * gamma - (8 / 9 : F) * B ^ 2 * D -
    (3 / 4 : F) * B ^ 2 * delta - (8 / 9 : F) * B * C0 ^ 2 -
    (4 / 3 : F) * B * C0 * gamma - (5 / 6 : F) * B * D * beta -
    (5 / 12 : F) * C0 ^ 2 * beta + C0 * zeta + (8 / 3 : F) * D * E +
    (2 : F) * D * epsilon + (3 : F) * E * delta

/-- Vanishing weight-11 multiplier of `alphaResidual68`. -/
def degreeZeroAlphaGroup68 : F := 0

def degreeZeroBetaGroup68 (A B C0 D E : F) : F :=
  -(91 * A ^ 5 - 840 * A ^ 3 * C0 - 1260 * A ^ 2 * B ^ 2 +
      2160 * A ^ 2 * E + 2160 * A * C0 ^ 2 + 2160 * B ^ 2 * C0 -
      25920 * C0 * E + 12960 * D ^ 2) / 31104

def degreeZeroGammaGroup68 (A B C0 E : F) : F :=
  B * (4 * A ^ 3 - 18 * A * C0 - 3 * B ^ 2 + 54 * E) / 81

def degreeZeroDeltaGroup68 (A B C0 E : F) : F :=
  (A ^ 4 - 8 * A ^ 2 * C0 - 8 * A * B ^ 2 + 32 * A * E +
      16 * C0 ^ 2) / 64

def degreeZeroEpsilonGroup68 (A B C0 : F) : F :=
  -B * (A ^ 2 - 3 * C0) / 9

def degreeZeroZetaGroup68 (A B C0 E : F) : F :=
  -(5 * A ^ 3 - 36 * A * C0 - 18 * B ^ 2 - 216 * E) / 216

/-- Vanishing weight-5 multiplier of `etaResidual68`. -/
def degreeZeroEtaGroup68 : F := 0

def degreeZeroFourGroup68 (A C0 : F) : F :=
  (A ^ 2 - 12 * C0) / 72

def degreeZeroThreeGroup68 (B : F) : F :=
  -B / 6

def degreeZeroTwoGroup68 (A : F) : F :=
  -A / 6

def degreeZeroBaseGroup68 (L A B C0 D E : F) : F :=
  -(1309 * A ^ 6 * L + 12288 * A ^ 5 * B - 13860 * A ^ 4 * C0 * L -
      27720 * A ^ 3 * B ^ 2 * L - 92160 * A ^ 3 * B * C0 +
      30240 * A ^ 3 * E * L - 46080 * A ^ 2 * B ^ 3 +
      165888 * A ^ 2 * B * E + 45360 * A ^ 2 * C0 ^ 2 * L +
      90720 * A * B ^ 2 * C0 * L + 165888 * A * B * C0 ^ 2 -
      217728 * A * C0 * E * L + 108864 * A * D ^ 2 * L +
      7560 * B ^ 4 * L + 55296 * B ^ 3 * C0 - 108864 * B ^ 2 * E * L -
      497664 * B * C0 * E + 248832 * B * D ^ 2 - 36288 * C0 ^ 3 * L -
      653184 * E ^ 2 * L) / 1119744

/-- The canonical weight-13 primitive after the polynomial-part faces and
the two committed first integrals have been transported back to their
literal residual functions.  The alpha and eta groups are the zero
constants `degreeZeroAlphaGroup68` / `degreeZeroEtaGroup68`. -/
def degreeZeroPrimitive68
    (L A B C0 D E P Q R S T U V : F) : F :=
  degreeZeroBaseGroup68 L A B C0 D E +
    betaResidual68 L A B Q * degreeZeroBetaGroup68 A B C0 D E +
    gammaResidual68 L A B C0 P R * degreeZeroGammaGroup68 A B C0 E +
    deltaResidual68 L A B C0 D P Q S *
      degreeZeroDeltaGroup68 A B C0 E +
    epsilonResidual68 L A B C0 D E P Q R T *
      degreeZeroEpsilonGroup68 A B C0 +
    zetaResidual68 L A B C0 D E P Q R S U *
      degreeZeroZetaGroup68 A B C0 E +
    firstIntegralFour68 L A B C0 D E
      (betaResidual68 L A B Q)
      (gammaResidual68 L A B C0 P R)
      (deltaResidual68 L A B C0 D P Q S)
      (epsilonResidual68 L A B C0 D E P Q R T)
      (zetaResidual68 L A B C0 D E P Q R S U) *
      degreeZeroFourGroup68 A C0 +
    firstIntegralThree68 L A B C0 D E
      (betaResidual68 L A B Q)
      (gammaResidual68 L A B C0 P R)
      (deltaResidual68 L A B C0 D P Q S)
      (epsilonResidual68 L A B C0 D E P Q R T)
      (zetaResidual68 L A B C0 D E P Q R S U) *
      degreeZeroThreeGroup68 B +
    firstIntegralTwo68 L A B C0 D E
      (betaResidual68 L A B Q)
      (gammaResidual68 L A B C0 P R)
      (deltaResidual68 L A B C0 D P Q S)
      (epsilonResidual68 L A B C0 D E P Q R T)
      (zetaResidual68 L A B C0 D E P Q R S U) *
      degreeZeroTwoGroup68 A

section DifferentialFirstIntegralTwo68

variable {k : Type*} [Field k] [Algebra k F]

set_option maxHeartbeats 8000000 in
/-- The unused integrated `z²` Jacobian row becomes exact after the
already-integrated `z⁴` row re-enters with coefficient `-A/2`.  The
`z³` multiplier is `0`, so this identity does not invoke
`lowerRowThree_integrated68_eq_deriv`; that parent remains the CAS
comparison that discarded the `h3` correction.  Expanding the `z⁴` row
through `integratedQ68`–`integratedU68` is the same calculation as
`lowerRowFour_integrated68_eq_deriv`. -/
theorem lowerRowTwo_integrated68_eq_deriv
    (d : Derivation k F F)
    (L A B C0 D E alpha beta gamma delta epsilon zeta eta : F)
    (hL : d L = 0) (halpha : d alpha = 0) (hbeta : d beta = 0)
    (hgamma : d gamma = 0) (hdelta : d delta = 0)
    (hepsilon : d epsilon = 0) (hzeta : d zeta = 0)
    (heta : d eta = 0) :
    let Q := integratedQ68 L A B beta
    let R := integratedR68 L A B C0 alpha gamma
    let S := integratedS68 L A B C0 D alpha beta delta
    let T := integratedT68 L A B C0 D E alpha beta gamma epsilon
    let U := integratedU68 L A B C0 D E alpha beta gamma delta zeta
    let V := integratedV68 L A B C0 D E alpha beta gamma delta epsilon eta
    U * d C0 + 2 * T * d D + 3 * S * d E - 3 * B * d V -
        2 * C0 * d U - D * d T -
      A / 2 * (U * d A + 2 * T * d B + 3 * S * d C0 + 4 * R * d D +
        5 * Q * d E - 4 * A * d U - 3 * B * d T - 2 * C0 * d S -
        D * d R) =
      d (firstIntegralTwo68 L A B C0 D E beta gamma delta epsilon zeta) := by
  dsimp only
  have h1 : d (1 : F) = 0 := by
    simpa only [Nat.cast_one] using d.map_natCast 1
  simp only [integratedQ68, integratedR68, integratedS68, integratedT68,
    integratedU68, integratedV68, firstIntegralTwo68, map_add, map_sub,
    map_neg, Derivation.leibniz, Derivation.leibniz_pow,
    Derivation.leibniz_div, Derivation.leibniz_inv, nsmul_eq_mul,
    smul_eq_mul, hL, halpha, hbeta, hgamma, hdelta, hepsilon, hzeta, heta]
  simp [derivation_ofNat_zero68 d, h1]
  ring

end DifferentialFirstIntegralTwo68

set_option maxHeartbeats 800000000 in
/-- Intrinsic weighted homogeneity of weight 13, with the depressed
`(6,8)` weights `wt(L)=1`, `wt(A)=wt(P)=2`, …, `wt(V)=8`. -/
theorem degreeZeroPrimitive68_weighted_homogeneous
    (t L A B C0 D E P Q R S T U V : F) :
    degreeZeroPrimitive68 (t * L) (t ^ 2 * A) (t ^ 3 * B) (t ^ 4 * C0)
        (t ^ 5 * D) (t ^ 6 * E) (t ^ 2 * P) (t ^ 3 * Q) (t ^ 4 * R)
        (t ^ 5 * S) (t ^ 6 * T) (t ^ 7 * U) (t ^ 8 * V) =
      t ^ 13 * degreeZeroPrimitive68 L A B C0 D E P Q R S T U V := by
  simp only [degreeZeroPrimitive68, degreeZeroBaseGroup68,
    degreeZeroBetaGroup68, degreeZeroGammaGroup68, degreeZeroDeltaGroup68,
    degreeZeroEpsilonGroup68, degreeZeroZetaGroup68,
    degreeZeroFourGroup68, degreeZeroThreeGroup68, degreeZeroTwoGroup68,
    firstIntegralFour68, firstIntegralThree68, firstIntegralTwo68,
    alphaResidual68, betaResidual68, gammaResidual68, deltaResidual68,
    epsilonResidual68, zetaResidual68, etaResidual68]
  ring

#print axioms lowerRowTwo_integrated68_eq_deriv
#print axioms degreeZeroPrimitive68_weighted_homogeneous

end DegreeZeroPrimitive68

end Max11DegreeRoutes
