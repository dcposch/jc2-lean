import Grok68TerminalZeroLargeRemainderScratch
import Grok68ScaleTwoDegreeZeroDifferentialBridgeScratch
import Grok68AlignedNonsquareOdeClosureScratch
import LowScale68ScaleZeroAssembly

/-! # Meeting cell of the `(6,8)` scale-zero terminal-zero packet

Untracked working note. No tracked file was edited.

Parent residual `FiveToSixTerminalZeroMeetingCell68`: a constant-`B`
cusp `t = n/2` with `120 ∣ n`, `n ≥ 240`, `g = 3n`, `zeta = 0`, and
`l = beta = delta = 0` from `fiveToSix_terminalTail_system_faces68`.

CAS `derive_68_terminal_zero_meeting_primitive.py` (job
`20260902T171627Z-68-terminal-zero-meeting-primitive-49241`) confirms
the cubic-coordinate rewrite of `degreeZeroPrimitive68` at
`l = beta = delta = zeta = 0`.  Route (b): `firstIntegralTwo68` is a
ground constant on the integrated lower system, the weight-13 primitive
differentiates to `C terminal`, hence has `natDegree ≤ 1`, and the
degree-`4n` coefficient of the expanded primitive forces `i4 = 0`.
With `i4 = 0` the I3/I2 identities collapse against the cusp to
`d_{n/2} = 0`.

The comparison is a coefficient at a single degree, not an evaluation
at roots of `B`, and not a finite-root shortcut.

Exact gain: meeting cell; terminal-zero packet; thin residual;
`IntegratedPolynomialLowerSystem68Exclusion`;
`PlaneKellerNormalized68LowScaleRoute`.
Next unused row: none (leaf closed).
Residual: none.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixTerminalZeroMeetingCell68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 40000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Polynomial first integral two -/

/-- Polynomial representative of `firstIntegralTwo68`. -/
def firstIntegralTwoPolynomial68
    (l beta gamma delta epsilon zeta : k)
    (A B C0 D E : k[X]) : k[X] :=
  (-77 / 2592 * l : k) • A ^ 5 +
    (35 / 162 * l : k) • (A ^ 3 * C0) +
    (35 / 96 * l : k) • (A ^ 2 * B ^ 2) -
    (7 / 24 * l : k) • (A ^ 2 * E) -
    (7 / 9 * l : k) • (A * B * D) -
    (7 / 18 * l : k) • (A * C0 ^ 2) -
    (35 / 72 * l : k) • (B ^ 2 * C0) +
    (7 / 6 * l : k) • (C0 * E) +
    (7 / 12 * l : k) • D ^ 2 -
    (20 / 81 : k) • (A ^ 4 * B) -
    (35 / 576 * beta : k) • A ^ 4 +
    (28 / 81 : k) • (A ^ 3 * D) +
    (1 / 4 * delta : k) • A ^ 3 +
    (32 / 27 : k) • (A ^ 2 * B * C0) +
    (2 / 3 * gamma : k) • (A ^ 2 * B) +
    (25 / 72 * beta : k) • (A ^ 2 * C0) -
    (1 / 4 * zeta : k) • A ^ 2 +
    (4 / 9 : k) • (A * B ^ 3) +
    (5 / 12 * beta : k) • (A * B ^ 2) -
    (4 / 3 : k) • (A * B * E) -
    epsilon • (A * B) -
    (4 / 3 : k) • (A * C0 * D) -
    delta • (A * C0) -
    (2 / 3 * gamma : k) • (A * D) -
    (8 / 9 : k) • (B ^ 2 * D) -
    (3 / 4 * delta : k) • B ^ 2 -
    (8 / 9 : k) • (B * C0 ^ 2) -
    (4 / 3 * gamma : k) • (B * C0) -
    (5 / 6 * beta : k) • (B * D) -
    (5 / 12 * beta : k) • C0 ^ 2 +
    zeta • C0 +
    (8 / 3 : k) • (D * E) +
    (2 * epsilon : k) • D +
    (3 * delta : k) • E

set_option maxHeartbeats 8000000 in
theorem algebraMap_firstIntegralTwoPolynomial68
    (l beta gamma delta epsilon zeta : k) (A B C0 D E : k[X]) :
    algebraMap k[X] (RatFunc k)
        (firstIntegralTwoPolynomial68 l beta gamma delta epsilon zeta
          A B C0 D E) =
      firstIntegralTwo68 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D)
        (algebraMap k[X] (RatFunc k) E)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) := by
  simp only [firstIntegralTwoPolynomial68, firstIntegralTwo68, map_add,
    map_sub, Polynomial.smul_eq_C_mul, map_mul, map_pow,
    RatFunc.algebraMap_C]
  simp only [map_neg, map_div₀, map_ofNat, map_one]
  ring

theorem expand_firstIntegralTwoPolynomial68
    (m : ℕ) (l beta gamma delta epsilon zeta : k) (A B C0 D E : k[X]) :
    expand k m (firstIntegralTwoPolynomial68 l beta gamma delta epsilon
        zeta A B C0 D E) =
      firstIntegralTwoPolynomial68 l beta gamma delta epsilon zeta
        (expand k m A) (expand k m B) (expand k m C0)
        (expand k m D) (expand k m E) := by
  simp [firstIntegralTwoPolynomial68]

theorem expand_firstIntegralTwoPolynomial68_of_eq
    (l beta gamma delta epsilon zeta i2 : k) (A B C0 D E : k[X])
    (hI2 : firstIntegralTwoPolynomial68 l beta gamma delta epsilon zeta
      A B C0 D E = C i2) :
    firstIntegralTwoPolynomial68 l beta gamma delta epsilon zeta
      (expand k 60 A) (expand k 60 B) (expand k 60 C0) (expand k 60 D)
      (expand k 60 E) = C i2 := by
  have h := congrArg (expand k 60) hI2
  simpa [expand_firstIntegralTwoPolynomial68] using h

/-! ## Polynomial groups of the weight-13 primitive -/

def degreeZeroBaseGroupPolynomial68
    (l : k) (A B C0 D E : k[X]) : k[X] :=
  (-(1 / 1119744 : k)) •
    ((1309 * l : k) • A ^ 6 + (12288 : k) • (A ^ 5 * B) -
      (13860 * l : k) • (A ^ 4 * C0) -
      (27720 * l : k) • (A ^ 3 * B ^ 2) -
      (92160 : k) • (A ^ 3 * B * C0) +
      (30240 * l : k) • (A ^ 3 * E) -
      (46080 : k) • (A ^ 2 * B ^ 3) +
      (165888 : k) • (A ^ 2 * B * E) +
      (45360 * l : k) • (A ^ 2 * C0 ^ 2) +
      (90720 * l : k) • (A * B ^ 2 * C0) +
      (165888 : k) • (A * B * C0 ^ 2) -
      (217728 * l : k) • (A * C0 * E) +
      (108864 * l : k) • (A * D ^ 2) +
      (7560 * l : k) • B ^ 4 +
      (55296 : k) • (B ^ 3 * C0) -
      (108864 * l : k) • (B ^ 2 * E) -
      (497664 : k) • (B * C0 * E) +
      (248832 : k) • (B * D ^ 2) -
      (36288 * l : k) • C0 ^ 3 -
      (653184 * l : k) • E ^ 2)

def degreeZeroBetaGroupPolynomial68 (A B C0 D E : k[X]) : k[X] :=
  (-(1 / 31104 : k)) •
    ((91 : k) • A ^ 5 - (840 : k) • (A ^ 3 * C0) -
      (1260 : k) • (A ^ 2 * B ^ 2) + (2160 : k) • (A ^ 2 * E) +
      (2160 : k) • (A * C0 ^ 2) + (2160 : k) • (B ^ 2 * C0) -
      (25920 : k) • (C0 * E) + (12960 : k) • D ^ 2)

def degreeZeroGammaGroupPolynomial68 (A B C0 E : k[X]) : k[X] :=
  (1 / 81 : k) •
    (B * ((4 : k) • A ^ 3 - (18 : k) • (A * C0) - (3 : k) • B ^ 2 +
      (54 : k) • E))

def degreeZeroDeltaGroupPolynomial68 (A B C0 E : k[X]) : k[X] :=
  (1 / 64 : k) •
    (A ^ 4 - (8 : k) • (A ^ 2 * C0) - (8 : k) • (A * B ^ 2) +
      (32 : k) • (A * E) + (16 : k) • C0 ^ 2)

def degreeZeroEpsilonGroupPolynomial68 (A B C0 : k[X]) : k[X] :=
  (-(1 / 9 : k)) • (B * (A ^ 2 - (3 : k) • C0))

def degreeZeroZetaGroupPolynomial68 (A B C0 E : k[X]) : k[X] :=
  (-(1 / 216 : k)) •
    ((5 : k) • A ^ 3 - (36 : k) • (A * C0) - (18 : k) • B ^ 2 -
      (216 : k) • E)

def degreeZeroFourGroupPolynomial68 (A C0 : k[X]) : k[X] :=
  (1 / 72 : k) • (A ^ 2 - (12 : k) • C0)

def degreeZeroThreeGroupPolynomial68 (B : k[X]) : k[X] :=
  (-(1 / 6 : k)) • B

def degreeZeroTwoGroupPolynomial68 (A : k[X]) : k[X] :=
  (-(1 / 6 : k)) • A

/-- Integrated field primitive after triangular residuals are the load
constants. -/
def degreeZeroIntegratedPrimitive68
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D E beta gamma delta epsilon zeta : F) : F :=
  degreeZeroBaseGroup68 L A B C0 D E +
    beta * degreeZeroBetaGroup68 A B C0 D E +
    gamma * degreeZeroGammaGroup68 A B C0 E +
    delta * degreeZeroDeltaGroup68 A B C0 E +
    epsilon * degreeZeroEpsilonGroup68 A B C0 +
    zeta * degreeZeroZetaGroup68 A B C0 E +
    firstIntegralFour68 L A B C0 D E beta gamma delta epsilon zeta *
      degreeZeroFourGroup68 A C0 +
    firstIntegralThree68 L A B C0 D E beta gamma delta epsilon zeta *
      degreeZeroThreeGroup68 B +
    firstIntegralTwo68 L A B C0 D E beta gamma delta epsilon zeta *
      degreeZeroTwoGroup68 A

/-- Polynomial representative of the integrated primitive. -/
def degreeZeroPrimitivePolynomial68
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B C0 D E : k[X]) : k[X] :=
  degreeZeroBaseGroupPolynomial68 l A B C0 D E +
    beta • degreeZeroBetaGroupPolynomial68 A B C0 D E +
    gamma • degreeZeroGammaGroupPolynomial68 A B C0 E +
    delta • degreeZeroDeltaGroupPolynomial68 A B C0 E +
    epsilon • degreeZeroEpsilonGroupPolynomial68 A B C0 +
    zeta • degreeZeroZetaGroupPolynomial68 A B C0 E +
    firstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        A B C0 D E *
      degreeZeroFourGroupPolynomial68 A C0 +
    firstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
        A B C0 D E *
      degreeZeroThreeGroupPolynomial68 B +
    firstIntegralTwoPolynomial68 l beta gamma delta epsilon zeta
        A B C0 D E *
      degreeZeroTwoGroupPolynomial68 A

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitive68_eq_integrated
    {F : Type*} [Field F] [CharZero F]
    (L A B C0 D E alpha beta gamma delta epsilon zeta eta : F) :
    degreeZeroPrimitive68 L A B C0 D E
        (integratedP68 A alpha)
        (integratedQ68 L A B beta)
        (integratedR68 L A B C0 alpha gamma)
        (integratedS68 L A B C0 D alpha beta delta)
        (integratedT68 L A B C0 D E alpha beta gamma epsilon)
        (integratedU68 L A B C0 D E alpha beta gamma delta zeta)
        (integratedV68 L A B C0 D E alpha beta gamma delta epsilon eta) =
      degreeZeroIntegratedPrimitive68 L A B C0 D E beta gamma delta
        epsilon zeta := by
  obtain ⟨_, hbeta, hgamma, hdelta, hepsilon, hzeta, _⟩ :=
    integratedResiduals68 L A B C0 D E alpha beta gamma delta epsilon
      zeta eta
  simp only [degreeZeroPrimitive68, degreeZeroIntegratedPrimitive68]
  rw [hbeta, hgamma, hdelta, hepsilon, hzeta]

set_option maxHeartbeats 16000000 in
theorem algebraMap_degreeZeroBaseGroupPolynomial68
    (l : k) (A B C0 D E : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroBaseGroupPolynomial68 l A B C0 D E) =
      degreeZeroBaseGroup68 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D)
        (algebraMap k[X] (RatFunc k) E) := by
  simp only [degreeZeroBaseGroupPolynomial68, degreeZeroBaseGroup68,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 8000000 in
theorem algebraMap_degreeZeroBetaGroupPolynomial68
    (A B C0 D E : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroBetaGroupPolynomial68 A B C0 D E) =
      degreeZeroBetaGroup68
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D)
        (algebraMap k[X] (RatFunc k) E) := by
  simp only [degreeZeroBetaGroupPolynomial68, degreeZeroBetaGroup68,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 4000000 in
theorem algebraMap_degreeZeroGammaGroupPolynomial68
    (A B C0 E : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroGammaGroupPolynomial68 A B C0 E) =
      degreeZeroGammaGroup68
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) E) := by
  simp only [degreeZeroGammaGroupPolynomial68, degreeZeroGammaGroup68,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 4000000 in
theorem algebraMap_degreeZeroDeltaGroupPolynomial68
    (A B C0 E : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroDeltaGroupPolynomial68 A B C0 E) =
      degreeZeroDeltaGroup68
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) E) := by
  simp only [degreeZeroDeltaGroupPolynomial68, degreeZeroDeltaGroup68,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 2000000 in
theorem algebraMap_degreeZeroEpsilonGroupPolynomial68
    (A B C0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroEpsilonGroupPolynomial68 A B C0) =
      degreeZeroEpsilonGroup68
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0) := by
  simp only [degreeZeroEpsilonGroupPolynomial68, degreeZeroEpsilonGroup68,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 2000000 in
theorem algebraMap_degreeZeroZetaGroupPolynomial68
    (A B C0 E : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroZetaGroupPolynomial68 A B C0 E) =
      degreeZeroZetaGroup68
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) E) := by
  simp only [degreeZeroZetaGroupPolynomial68, degreeZeroZetaGroup68,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

theorem algebraMap_degreeZeroFourGroupPolynomial68 (A C0 : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroFourGroupPolynomial68 A C0) =
      degreeZeroFourGroup68
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) C0) := by
  simp only [degreeZeroFourGroupPolynomial68, degreeZeroFourGroup68,
    map_add, map_sub, map_neg, map_mul, map_pow, Polynomial.smul_eq_C_mul,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

theorem algebraMap_degreeZeroThreeGroupPolynomial68 (B : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroThreeGroupPolynomial68 B) =
      degreeZeroThreeGroup68 (algebraMap k[X] (RatFunc k) B) := by
  simp only [degreeZeroThreeGroupPolynomial68, degreeZeroThreeGroup68,
    map_neg, map_mul, Polynomial.smul_eq_C_mul, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_one]
  ring

theorem algebraMap_degreeZeroTwoGroupPolynomial68 (A : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroTwoGroupPolynomial68 A) =
      degreeZeroTwoGroup68 (algebraMap k[X] (RatFunc k) A) := by
  simp only [degreeZeroTwoGroupPolynomial68, degreeZeroTwoGroup68,
    map_neg, map_mul, Polynomial.smul_eq_C_mul, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 16000000 in
theorem algebraMap_degreeZeroPrimitivePolynomial68
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B C0 D E : k[X]) :
    algebraMap k[X] (RatFunc k)
        (degreeZeroPrimitivePolynomial68 l alpha beta gamma delta epsilon
          zeta eta A B C0 D E) =
      degreeZeroIntegratedPrimitive68 (RatFunc.C l)
        (algebraMap k[X] (RatFunc k) A)
        (algebraMap k[X] (RatFunc k) B)
        (algebraMap k[X] (RatFunc k) C0)
        (algebraMap k[X] (RatFunc k) D)
        (algebraMap k[X] (RatFunc k) E)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C zeta) := by
  simp only [degreeZeroPrimitivePolynomial68,
    degreeZeroIntegratedPrimitive68, map_add, map_mul,
    Polynomial.smul_eq_C_mul, RatFunc.algebraMap_C,
    algebraMap_degreeZeroBaseGroupPolynomial68,
    algebraMap_degreeZeroBetaGroupPolynomial68,
    algebraMap_degreeZeroGammaGroupPolynomial68,
    algebraMap_degreeZeroDeltaGroupPolynomial68,
    algebraMap_degreeZeroEpsilonGroupPolynomial68,
    algebraMap_degreeZeroZetaGroupPolynomial68,
    algebraMap_degreeZeroFourGroupPolynomial68,
    algebraMap_degreeZeroThreeGroupPolynomial68,
    algebraMap_degreeZeroTwoGroupPolynomial68,
    algebraMap_firstIntegralFourPolynomial68,
    algebraMap_firstIntegralThreePolynomial68,
    algebraMap_firstIntegralTwoPolynomial68]

theorem expand_degreeZeroPrimitivePolynomial68
    (m : ℕ) (l alpha beta gamma delta epsilon zeta eta : k)
    (A B C0 D E : k[X]) :
    expand k m (degreeZeroPrimitivePolynomial68 l alpha beta gamma delta
        epsilon zeta eta A B C0 D E) =
      degreeZeroPrimitivePolynomial68 l alpha beta gamma delta epsilon
        zeta eta (expand k m A) (expand k m B) (expand k m C0)
        (expand k m D) (expand k m E) := by
  simp [degreeZeroPrimitivePolynomial68, degreeZeroBaseGroupPolynomial68,
    degreeZeroBetaGroupPolynomial68, degreeZeroGammaGroupPolynomial68,
    degreeZeroDeltaGroupPolynomial68, degreeZeroEpsilonGroupPolynomial68,
    degreeZeroZetaGroupPolynomial68, degreeZeroFourGroupPolynomial68,
    degreeZeroThreeGroupPolynomial68, degreeZeroTwoGroupPolynomial68,
    expand_firstIntegralFourPolynomial68, expand_firstIntegralThreePolynomial68,
    expand_firstIntegralTwoPolynomial68]

/-! ## Ground constants and the primitive derivative -/

theorem ratFuncDerivation68_C (x : k) :
    ratFuncDerivation68 (RatFunc.C x) = 0 := by
  have hp := ratFuncDerivation46_polynomial (C x : k[X])
  simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hp

theorem polynomial_eq_C_of_ratFuncDeriv68 (I : k[X])
    (hderiv :
      ratFuncDerivation68 (algebraMap k[X] (RatFunc k) I) = 0) :
    ∃ c : k, I = C c := by
  have hdmap : algebraMap k[X] (RatFunc k) I.derivative = 0 := by
    rw [show ratFuncDerivation68 = ratFuncDerivation46 from rfl] at hderiv
    rw [← ratFuncDerivation46_polynomial]
    exact hderiv
  have hd : I.derivative = 0 :=
    (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
      (by simpa using hdmap)
  exact ⟨I.coeff 0, Polynomial.eq_C_of_derivative_eq_zero hd⟩

theorem natDegree_eq_one_of_derivative_eq_nonzero_C68
    (P : k[X]) (j : k) (hj : j ≠ 0) (h : derivative P = C j) :
    P.natDegree = 1 := by
  have hder : derivative P ≠ 0 := by
    intro hz
    rw [hz] at h
    exact hj (C_eq_zero.mp h.symm)
  have hdegder : (derivative P).natDegree = 0 := by
    rw [h, natDegree_C]
  have hpositive : 0 < P.natDegree :=
    Nat.pos_of_ne_zero (derivative_ne_zero.mp hder)
  rw [natDegree_derivative] at hdegder
  omega

set_option maxHeartbeats 25000000 in
theorem integratedPolynomialLowerSystem68_firstIntegralTwo_const68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X])
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    ∃ i2 : k,
      firstIntegralTwoPolynomial68 l beta gamma delta epsilon zeta
        A B C0 D E = C i2 := by
  let AR := algebraMap k[X] (RatFunc k) A
  let BR := algebraMap k[X] (RatFunc k) B
  let CR := algebraMap k[X] (RatFunc k) C0
  let DR := algebraMap k[X] (RatFunc k) D
  let ER := algebraMap k[X] (RatFunc k) E
  let S0 := integratedSPolynomial68 l alpha beta delta A B C0 D
  let T0 := integratedTPolynomial68 l alpha beta gamma epsilon A B C0 D E
  let U0 := integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E
  let V0 := integratedVPolynomial68 l alpha beta gamma delta epsilon eta
    A B C0 D E
  have hSmap : algebraMap k[X] (RatFunc k) S0 =
      integratedS68 (RatFunc.C l) AR BR CR DR (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C delta) := by
    simpa [S0, AR, BR, CR, DR] using
      algebraMap_integratedSPolynomial68 l alpha beta delta A B C0 D
  have hTmap : algebraMap k[X] (RatFunc k) T0 =
      integratedT68 (RatFunc.C l) AR BR CR DR ER (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C epsilon) := by
    simpa [T0, AR, BR, CR, DR, ER] using
      algebraMap_integratedTPolynomial68 l alpha beta gamma epsilon
        A B C0 D E
  have hUmap : algebraMap k[X] (RatFunc k) U0 =
      integratedU68 (RatFunc.C l) AR BR CR DR ER (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C zeta) := by
    simpa [U0, AR, BR, CR, DR, ER] using
      algebraMap_integratedUPolynomial68 l alpha beta gamma delta zeta
        A B C0 D E
  have hVmap : algebraMap k[X] (RatFunc k) V0 =
      integratedV68 (RatFunc.C l) AR BR CR DR ER (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C eta) := by
    simpa [V0, AR, BR, CR, DR, ER] using
      algebraMap_integratedVPolynomial68 l alpha beta gamma delta epsilon
        eta A B C0 D E
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  have hI4map :
      firstIntegralFour68 (RatFunc.C l) AR BR CR DR ER (RatFunc.C beta)
          (RatFunc.C gamma) (RatFunc.C delta) (RatFunc.C epsilon)
          (RatFunc.C zeta) =
        RatFunc.C i4 := by
    have := congrArg (algebraMap k[X] (RatFunc k)) hi4
    simpa [AR, BR, CR, DR, ER, algebraMap_firstIntegralFourPolynomial68,
      RatFunc.algebraMap_C] using this
  have hrow4 :=
    lowerRowFour_integrated68_eq_deriv ratFuncDerivation68 (RatFunc.C l)
      AR BR CR DR ER (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
      (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
      (ratFuncDerivation68_C l) (ratFuncDerivation68_C alpha)
      (ratFuncDerivation68_C beta) (ratFuncDerivation68_C gamma)
      (ratFuncDerivation68_C delta) (ratFuncDerivation68_C epsilon)
      (ratFuncDerivation68_C zeta)
  have hrow4z :
      let Q := integratedQ68 (RatFunc.C l) AR BR (RatFunc.C beta)
      let R := integratedR68 (RatFunc.C l) AR BR CR (RatFunc.C alpha)
        (RatFunc.C gamma)
      let S := integratedS68 (RatFunc.C l) AR BR CR DR (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C delta)
      let T := integratedT68 (RatFunc.C l) AR BR CR DR ER (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C epsilon)
      let U := integratedU68 (RatFunc.C l) AR BR CR DR ER (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C zeta)
      U * ratFuncDerivation68 AR + 2 * T * ratFuncDerivation68 BR +
          3 * S * ratFuncDerivation68 CR + 4 * R * ratFuncDerivation68 DR +
          5 * Q * ratFuncDerivation68 ER - 4 * AR * ratFuncDerivation68 U -
          3 * BR * ratFuncDerivation68 T - 2 * CR * ratFuncDerivation68 S -
          DR * ratFuncDerivation68 R =
        0 := by
    simpa [hI4map, ratFuncDerivation68_C i4] using hrow4
  have hrow2map :
      algebraMap k[X] (RatFunc k)
          (lowerRowTwoPolynomial68 S0 T0 U0 V0 B C0 D E) =
        algebraMap k[X] (RatFunc k) U0 *
            ratFuncDerivation68 CR +
          2 * algebraMap k[X] (RatFunc k) T0 *
            ratFuncDerivation68 DR +
          3 * algebraMap k[X] (RatFunc k) S0 *
            ratFuncDerivation68 ER -
          3 * BR * ratFuncDerivation68 (algebraMap k[X] (RatFunc k) V0) -
          2 * CR * ratFuncDerivation68 (algebraMap k[X] (RatFunc k) U0) -
          DR * ratFuncDerivation68 (algebraMap k[X] (RatFunc k) T0) := by
    simpa [AR, BR, CR, DR, ER] using
      algebraMap_lowerRowTwoPolynomial68 S0 T0 U0 V0 B C0 D E
  have hrow2z :
      let S := integratedS68 (RatFunc.C l) AR BR CR DR (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C delta)
      let T := integratedT68 (RatFunc.C l) AR BR CR DR ER (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C epsilon)
      let U := integratedU68 (RatFunc.C l) AR BR CR DR ER (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C zeta)
      let V := integratedV68 (RatFunc.C l) AR BR CR DR ER (RatFunc.C alpha)
        (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
        (RatFunc.C epsilon) (RatFunc.C eta)
      U * ratFuncDerivation68 CR + 2 * T * ratFuncDerivation68 DR +
          3 * S * ratFuncDerivation68 ER - 3 * BR * ratFuncDerivation68 V -
          2 * CR * ratFuncDerivation68 U - DR * ratFuncDerivation68 T =
        0 := by
    have hpoly : lowerRowTwoPolynomial68 S0 T0 U0 V0 B C0 D E = 0 :=
      hsys.rowTwo
    have := congrArg (algebraMap k[X] (RatFunc k)) hpoly
    rw [map_zero] at this
    rw [hrow2map] at this
    simpa [hSmap, hTmap, hUmap, hVmap] using this
  have hI2eq :=
    lowerRowTwo_integrated68_eq_deriv ratFuncDerivation68 (RatFunc.C l)
      AR BR CR DR ER (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
      (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
      (RatFunc.C eta) (ratFuncDerivation68_C l)
      (ratFuncDerivation68_C alpha) (ratFuncDerivation68_C beta)
      (ratFuncDerivation68_C gamma) (ratFuncDerivation68_C delta)
      (ratFuncDerivation68_C epsilon) (ratFuncDerivation68_C zeta)
      (ratFuncDerivation68_C eta)
  have hI2deriv :
      ratFuncDerivation68
          (firstIntegralTwo68 (RatFunc.C l) AR BR CR DR ER
            (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
            (RatFunc.C epsilon) (RatFunc.C zeta)) =
        0 := by
    have h := hI2eq
    dsimp only at h hrow2z hrow4z
    rw [hrow2z, hrow4z] at h
    simpa using h.symm
  have hI2map :
      algebraMap k[X] (RatFunc k)
          (firstIntegralTwoPolynomial68 l beta gamma delta epsilon zeta
            A B C0 D E) =
        firstIntegralTwo68 (RatFunc.C l) AR BR CR DR ER (RatFunc.C beta)
          (RatFunc.C gamma) (RatFunc.C delta) (RatFunc.C epsilon)
          (RatFunc.C zeta) := by
    simpa [AR, BR, CR, DR, ER] using
      algebraMap_firstIntegralTwoPolynomial68 l beta gamma delta epsilon
        zeta A B C0 D E
  have hderiv :
      ratFuncDerivation68
          (algebraMap k[X] (RatFunc k)
            (firstIntegralTwoPolynomial68 l beta gamma delta epsilon zeta
              A B C0 D E)) =
        0 := by
    simpa [hI2map] using hI2deriv
  exact polynomial_eq_C_of_ratFuncDeriv68 _ hderiv

set_option maxHeartbeats 25000000 in
theorem integratedPolynomialLowerSystem68_degreeZeroPrimitive_deriv68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    derivative
        (degreeZeroPrimitivePolynomial68 l alpha beta gamma delta epsilon
          zeta eta A B C0 D E) =
      C terminal := by
  let AR := algebraMap k[X] (RatFunc k) A
  let BR := algebraMap k[X] (RatFunc k) B
  let CR := algebraMap k[X] (RatFunc k) C0
  let DR := algebraMap k[X] (RatFunc k) D
  let ER := algebraMap k[X] (RatFunc k) E
  let PR := integratedP68 AR (RatFunc.C alpha)
  let QR := integratedQ68 (RatFunc.C l) AR BR (RatFunc.C beta)
  let RR := integratedR68 (RatFunc.C l) AR BR CR (RatFunc.C alpha)
    (RatFunc.C gamma)
  let SR := integratedS68 (RatFunc.C l) AR BR CR DR (RatFunc.C alpha)
    (RatFunc.C beta) (RatFunc.C delta)
  let TR := integratedT68 (RatFunc.C l) AR BR CR DR ER (RatFunc.C alpha)
    (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C epsilon)
  let UR := integratedU68 (RatFunc.C l) AR BR CR DR ER (RatFunc.C alpha)
    (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
    (RatFunc.C zeta)
  let VR := integratedV68 (RatFunc.C l) AR BR CR DR ER (RatFunc.C alpha)
    (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
    (RatFunc.C epsilon) (RatFunc.C eta)
  obtain ⟨halphaR, hbetaR, hgammaR, hdeltaR, hepsilonR, hzetaR, hetaR⟩ :=
    integratedResiduals68 (RatFunc.C l) AR BR CR DR ER (RatFunc.C alpha)
      (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
      (RatFunc.C epsilon) (RatFunc.C zeta) (RatFunc.C eta)
  obtain ⟨i4, hi4⟩ := hsys.firstFour
  obtain ⟨i3, hi3⟩ := hsys.firstThree
  obtain ⟨i2, hi2⟩ :=
    integratedPolynomialLowerSystem68_firstIntegralTwo_const68 l alpha
      beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have hI4map :
      firstIntegralFour68 (RatFunc.C l) AR BR CR DR ER (RatFunc.C beta)
          (RatFunc.C gamma) (RatFunc.C delta) (RatFunc.C epsilon)
          (RatFunc.C zeta) =
        RatFunc.C i4 := by
    have := congrArg (algebraMap k[X] (RatFunc k)) hi4
    simpa [AR, BR, CR, DR, ER, algebraMap_firstIntegralFourPolynomial68,
      RatFunc.algebraMap_C] using this
  have hI3map :
      firstIntegralThree68 (RatFunc.C l) AR BR CR DR ER (RatFunc.C beta)
          (RatFunc.C gamma) (RatFunc.C delta) (RatFunc.C epsilon)
          (RatFunc.C zeta) =
        RatFunc.C i3 := by
    have := congrArg (algebraMap k[X] (RatFunc k)) hi3
    simpa [AR, BR, CR, DR, ER, algebraMap_firstIntegralThreePolynomial68,
      RatFunc.algebraMap_C] using this
  have hI2map :
      firstIntegralTwo68 (RatFunc.C l) AR BR CR DR ER (RatFunc.C beta)
          (RatFunc.C gamma) (RatFunc.C delta) (RatFunc.C epsilon)
          (RatFunc.C zeta) =
        RatFunc.C i2 := by
    have := congrArg (algebraMap k[X] (RatFunc k)) hi2
    simpa [AR, BR, CR, DR, ER, algebraMap_firstIntegralTwoPolynomial68,
      RatFunc.algebraMap_C] using this
  have hrow :=
    degreeZeroPrimitive68_deriv_eq_row ratFuncDerivation68 (RatFunc.C l)
      AR BR CR DR ER PR QR RR SR TR UR VR (ratFuncDerivation68_C l)
      (by
        simp only [PR]
        rw [halphaR]
        exact ratFuncDerivation68_C alpha)
      (by
        simp only [QR]
        rw [hbetaR]
        exact ratFuncDerivation68_C beta)
      (by
        simp only [PR, RR]
        rw [hgammaR]
        exact ratFuncDerivation68_C gamma)
      (by
        simp only [PR, QR, SR]
        rw [hdeltaR]
        exact ratFuncDerivation68_C delta)
      (by
        simp only [PR, QR, RR, TR]
        rw [hepsilonR]
        exact ratFuncDerivation68_C epsilon)
      (by
        simp only [PR, QR, RR, SR, UR]
        rw [hzetaR]
        exact ratFuncDerivation68_C zeta)
      (by
        simp only [PR, QR, RR, SR, TR, VR]
        rw [hetaR]
        exact ratFuncDerivation68_C eta)
      (by
        simp only [PR, QR, RR, SR, TR, UR]
        rw [hbetaR, hgammaR, hdeltaR, hepsilonR, hzetaR, hI4map]
        exact ratFuncDerivation68_C i4)
      (by
        simp only [PR, QR, RR, SR, TR, UR]
        rw [hbetaR, hgammaR, hdeltaR, hepsilonR, hzetaR, hI3map]
        exact ratFuncDerivation68_C i3)
      (by
        simp only [PR, QR, RR, SR, TR, UR]
        rw [hbetaR, hgammaR, hdeltaR, hepsilonR, hzetaR, hI2map]
        exact ratFuncDerivation68_C i2)
  have hprimRF :
      degreeZeroPrimitive68 (RatFunc.C l) AR BR CR DR ER PR QR RR SR TR
          UR VR =
        degreeZeroIntegratedPrimitive68 (RatFunc.C l) AR BR CR DR ER
          (RatFunc.C beta) (RatFunc.C gamma) (RatFunc.C delta)
          (RatFunc.C epsilon) (RatFunc.C zeta) := by
    simpa [PR, QR, RR, SR, TR, UR, VR] using
      degreeZeroPrimitive68_eq_integrated (RatFunc.C l) AR BR CR DR ER
        (RatFunc.C alpha) (RatFunc.C beta) (RatFunc.C gamma)
        (RatFunc.C delta) (RatFunc.C epsilon) (RatFunc.C zeta)
        (RatFunc.C eta)
  have hUmap : algebraMap k[X] (RatFunc k)
        (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E) =
      UR := by
    simpa [UR, AR, BR, CR, DR, ER] using
      algebraMap_integratedUPolynomial68 l alpha beta gamma delta zeta
        A B C0 D E
  have hVmap : algebraMap k[X] (RatFunc k)
        (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
          A B C0 D E) =
      VR := by
    simpa [VR, AR, BR, CR, DR, ER] using
      algebraMap_integratedVPolynomial68 l alpha beta gamma delta epsilon
        eta A B C0 D E
  have hrow0map :
      algebraMap k[X] (RatFunc k)
          (lowerRowZeroPolynomial68
            (integratedUPolynomial68 l alpha beta gamma delta zeta
              A B C0 D E)
            (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
              A B C0 D E)
            D E) =
        UR * ratFuncDerivation68 ER - DR * ratFuncDerivation68 VR := by
    have h := algebraMap_lowerRowZeroPolynomial68
      (integratedUPolynomial68 l alpha beta gamma delta zeta A B C0 D E)
      (integratedVPolynomial68 l alpha beta gamma delta epsilon eta
        A B C0 D E)
      D E
    simpa [UR, VR, DR, ER, hUmap, hVmap] using h
  have hrow0z :
      UR * ratFuncDerivation68 ER - DR * ratFuncDerivation68 VR =
        RatFunc.C terminal := by
    have := congrArg (algebraMap k[X] (RatFunc k)) hsys.rowZero
    simpa [hrow0map, RatFunc.algebraMap_C] using this
  have hmap_prim :
      algebraMap k[X] (RatFunc k)
          (degreeZeroPrimitivePolynomial68 l alpha beta gamma delta
            epsilon zeta eta A B C0 D E) =
        degreeZeroPrimitive68 (RatFunc.C l) AR BR CR DR ER PR QR RR SR TR
          UR VR := by
    rw [algebraMap_degreeZeroPrimitivePolynomial68, hprimRF.symm]
  have hder_prim :
      algebraMap k[X] (RatFunc k)
          (derivative
            (degreeZeroPrimitivePolynomial68 l alpha beta gamma delta
              epsilon zeta eta A B C0 D E)) =
        algebraMap k[X] (RatFunc k) (C terminal) := by
    rw [← ratFuncDerivation46_polynomial]
    have hderiv' :
        ratFuncDerivation68
            (algebraMap k[X] (RatFunc k)
              (degreeZeroPrimitivePolynomial68 l alpha beta gamma delta
                epsilon zeta eta A B C0 D E)) =
          RatFunc.C terminal := by
      rw [hmap_prim, hrow, hrow0z]
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hderiv'
  exact (FaithfulSMul.algebraMap_injective k[X] (RatFunc k)) hder_prim

theorem integratedPolynomialLowerSystem68_degreeZeroPrimitive_natDegree68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E) :
    (degreeZeroPrimitivePolynomial68 l alpha beta gamma delta epsilon
        zeta eta A B C0 D E).natDegree =
      1 :=
  natDegree_eq_one_of_derivative_eq_nonzero_C68 _
    terminal hterminal
    (integratedPolynomialLowerSystem68_degreeZeroPrimitive_deriv68 l
      alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys)

/-! ## Cubic-coordinate group identities -/

/-- Compact cubic form of `firstIntegralTwo68` at `l = beta = delta = zeta = 0`. -/
def cubicFirstIntegralTwoPolynomial68
    (gamma epsilon : k) (A B c d e : k[X]) : k[X] :=
  (4 / 27 : k) • (A * B ^ 3) - (4 / 9 : k) • (A * B * e) -
    (1 / 3 * epsilon : k) • (A * B) - (4 / 9 : k) • (A * c * d) -
    (2 / 3 * gamma : k) • (A * d) - (8 / 9 : k) • (B ^ 2 * d) -
    (8 / 9 : k) • (B * c ^ 2) - (4 / 3 * gamma : k) • (B * c) +
    (8 / 3 : k) • (d * e) + (2 * epsilon : k) • d

set_option maxHeartbeats 8000000 in
theorem firstIntegralTwo68_cubicCoordinates
    {F : Type*} [Field F] [CharZero F]
    (gamma epsilon A B c d e : F) :
    firstIntegralTwo68 0 A B (A ^ 2 / 3 + c) (A * B / 3 + d)
        (A ^ 3 / 27 + A * c / 3 + e) 0 gamma 0 epsilon 0 =
      (4 / 27 : F) * A * B ^ 3 - (4 / 9 : F) * A * B * e -
        (1 / 3 : F) * epsilon * A * B - (4 / 9 : F) * A * c * d -
        (2 / 3 : F) * gamma * A * d - (8 / 9 : F) * B ^ 2 * d -
        (8 / 9 : F) * B * c ^ 2 - (4 / 3 : F) * gamma * B * c +
        (8 / 3 : F) * d * e + (2 : F) * epsilon * d := by
  simp only [firstIntegralTwo68]
  ring

theorem degreeZeroFourGroup68_cubic
    {F : Type*} [Field F] [CharZero F] (A c : F) :
    degreeZeroFourGroup68 A (A ^ 2 / 3 + c) = -A ^ 2 / 24 - c / 6 := by
  simp only [degreeZeroFourGroup68]
  ring

theorem degreeZeroEpsilonGroup68_cubic
    {F : Type*} [Field F] [CharZero F] (A B c : F) :
    degreeZeroEpsilonGroup68 A B (A ^ 2 / 3 + c) = B * c / 3 := by
  simp only [degreeZeroEpsilonGroup68]
  ring

theorem degreeZeroGammaGroup68_cubic
    {F : Type*} [Field F] [CharZero F] (A B c e : F) :
    degreeZeroGammaGroup68 A B (A ^ 2 / 3 + c)
        (A ^ 3 / 27 + A * c / 3 + e) =
      -B ^ 3 / 27 + (2 / 3 : F) * B * e := by
  simp only [degreeZeroGammaGroup68]
  ring

set_option maxHeartbeats 16000000 in
theorem degreeZeroBaseGroup68_cubic
    {F : Type*} [Field F] [CharZero F] (A B c d e : F) :
    degreeZeroBaseGroup68 0 A B (A ^ 2 / 3 + c) (A * B / 3 + d)
        (A ^ 3 / 27 + A * c / 3 + e) =
      B * ((-4 / 81 : F) * B ^ 2 * c + (4 / 9 : F) * c * e -
        (4 / 27 : F) * A * B * d - (2 / 9 : F) * d ^ 2) := by
  simp only [degreeZeroBaseGroup68]
  ring

theorem algebraMap_cubicC (A c : k[X]) :
    algebraMap k[X] (RatFunc k) ((1 / 3 : k) • A ^ 2 + c) =
      algebraMap k[X] (RatFunc k) A ^ 2 / 3 +
        algebraMap k[X] (RatFunc k) c := by
  simp only [Polynomial.smul_eq_C_mul, map_add, map_mul, map_pow,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

theorem algebraMap_cubicD (A B d : k[X]) :
    algebraMap k[X] (RatFunc k) ((1 / 3 : k) • (A * B) + d) =
      algebraMap k[X] (RatFunc k) A * algebraMap k[X] (RatFunc k) B / 3 +
        algebraMap k[X] (RatFunc k) d := by
  simp only [Polynomial.smul_eq_C_mul, map_add, map_mul, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_one]
  ring

theorem algebraMap_cubicE (A c e : k[X]) :
    algebraMap k[X] (RatFunc k)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) =
      algebraMap k[X] (RatFunc k) A ^ 3 / 27 +
        algebraMap k[X] (RatFunc k) A * algebraMap k[X] (RatFunc k) c / 3 +
        algebraMap k[X] (RatFunc k) e := by
  simp only [Polynomial.smul_eq_C_mul, map_add, map_mul, map_pow,
    RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

set_option maxHeartbeats 8000000 in
theorem firstIntegralTwoPolynomial68_cubicCoordinates
    (gamma epsilon : k) (A B c d e : k[X]) :
    firstIntegralTwoPolynomial68 0 0 gamma 0 epsilon 0 A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) =
      cubicFirstIntegralTwoPolynomial68 gamma epsilon A B c d e := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  rw [algebraMap_firstIntegralTwoPolynomial68, algebraMap_cubicC,
    algebraMap_cubicD, algebraMap_cubicE]
  simp only [map_zero]
  rw [firstIntegralTwo68_cubicCoordinates]
  simp only [cubicFirstIntegralTwoPolynomial68, map_add, map_sub, map_mul,
    map_pow, map_neg, Polynomial.smul_eq_C_mul, RatFunc.algebraMap_C]
  simp only [map_div₀, map_ofNat, map_one]
  ring

theorem degreeZeroFourGroupPolynomial68_cubic (A c : k[X]) :
    degreeZeroFourGroupPolynomial68 A ((1 / 3 : k) • A ^ 2 + c) =
      (-(1 / 24 : k)) • A ^ 2 - (1 / 6 : k) • c := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  rw [algebraMap_degreeZeroFourGroupPolynomial68, algebraMap_cubicC,
    degreeZeroFourGroup68_cubic]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg,
    Polynomial.smul_eq_C_mul, RatFunc.algebraMap_C, map_div₀, map_ofNat,
    map_one]
  ring

theorem degreeZeroEpsilonGroupPolynomial68_cubic (A B c : k[X]) :
    degreeZeroEpsilonGroupPolynomial68 A B ((1 / 3 : k) • A ^ 2 + c) =
      (1 / 3 : k) • (B * c) := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  rw [algebraMap_degreeZeroEpsilonGroupPolynomial68, algebraMap_cubicC,
    degreeZeroEpsilonGroup68_cubic]
  simp only [map_mul, Polynomial.smul_eq_C_mul, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_one]
  ring

theorem degreeZeroGammaGroupPolynomial68_cubic (A B c e : k[X]) :
    degreeZeroGammaGroupPolynomial68 A B ((1 / 3 : k) • A ^ 2 + c)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) =
      (-(1 / 27 : k)) • B ^ 3 + (2 / 3 : k) • (B * e) := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  rw [algebraMap_degreeZeroGammaGroupPolynomial68, algebraMap_cubicC,
    algebraMap_cubicE, degreeZeroGammaGroup68_cubic]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg,
    Polynomial.smul_eq_C_mul, RatFunc.algebraMap_C, map_div₀, map_ofNat,
    map_one]
  ring

set_option maxHeartbeats 8000000 in
theorem degreeZeroBaseGroupPolynomial68_cubic (A B c d e : k[X]) :
    degreeZeroBaseGroupPolynomial68 0 A B ((1 / 3 : k) • A ^ 2 + c)
        ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) =
      B * ((-(4 / 81 : k)) • (B ^ 2 * c) + (4 / 9 : k) • (c * e) -
        (4 / 27 : k) • (A * B * d) - (2 / 9 : k) • d ^ 2) := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  rw [algebraMap_degreeZeroBaseGroupPolynomial68, algebraMap_cubicC,
    algebraMap_cubicD, algebraMap_cubicE]
  simp only [map_zero]
  rw [degreeZeroBaseGroup68_cubic]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg,
    Polynomial.smul_eq_C_mul, RatFunc.algebraMap_C, map_div₀, map_ofNat,
    map_one]
  ring

set_option maxHeartbeats 16000000 in
theorem degreeZeroPrimitivePolynomial68_cubic_zeroLoads
    (alpha gamma epsilon eta : k) (A B c d e : k[X]) :
    degreeZeroPrimitivePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) =
      B * ((-(4 / 81 : k)) • (B ^ 2 * c) + (4 / 9 : k) • (c * e) -
          (4 / 27 : k) • (A * B * d) - (2 / 9 : k) • d ^ 2) +
        (2 / 3 * gamma : k) • (B * e) -
        (1 / 27 * gamma : k) • B ^ 3 +
        (1 / 3 * epsilon : k) • (B * c) +
        firstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0 A B
            ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
            ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) *
          ((-(1 / 24 : k)) • A ^ 2 - (1 / 6 : k) • c) +
        firstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0 A B
            ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
            ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) *
          ((-(1 / 6 : k)) • B) +
        firstIntegralTwoPolynomial68 0 0 gamma 0 epsilon 0 A B
            ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
            ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) *
          ((-(1 / 6 : k)) • A) := by
  simp only [degreeZeroPrimitivePolynomial68, zero_smul, add_zero]
  rw [degreeZeroBaseGroupPolynomial68_cubic,
    degreeZeroGammaGroupPolynomial68_cubic,
    degreeZeroEpsilonGroupPolynomial68_cubic,
    degreeZeroFourGroupPolynomial68_cubic]
  simp only [degreeZeroThreeGroupPolynomial68, degreeZeroTwoGroupPolynomial68,
    smul_add, smul_sub]
  module

theorem natDegree_mul_le_add68 {p q : k[X]} {n m : ℕ}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ m) :
    (p * q).natDegree ≤ n + m :=
  natDegree_mul_le.trans (Nat.add_le_add hp hq)

theorem natDegree_smul_le68 (c : k) (p : k[X]) :
    (c • p).natDegree ≤ p.natDegree := by
  by_cases hc : c = 0
  · rw [hc, zero_smul, natDegree_zero]
    exact Nat.zero_le _
  · rw [natDegree_smul _ hc]

theorem natDegree_C_mul_le68 (c : k) (p : k[X]) :
    (C c * p).natDegree ≤ p.natDegree := by
  simpa [smul_eq_C_mul] using natDegree_smul_le68 c p

set_option maxHeartbeats 8000000 in
theorem degreeZeroPrimitivePolynomial68_cubic_of_integrals_const
    (alpha gamma epsilon eta i4 i3 i2 : k) (A B c d e : k[X])
    (hI4 : firstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0 A B
      ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) = C i4)
    (hI3 : firstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0 A B
      ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) = C i3)
    (hI2 : firstIntegralTwoPolynomial68 0 0 gamma 0 epsilon 0 A B
      ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) = C i2) :
    degreeZeroPrimitivePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta A B
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * B) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) =
      B * ((-(4 / 81 : k)) • (B ^ 2 * c) + (4 / 9 : k) • (c * e) -
          (4 / 27 : k) • (A * B * d) - (2 / 9 : k) • d ^ 2) +
        (2 / 3 * gamma : k) • (B * e) -
        (1 / 27 * gamma : k) • B ^ 3 +
        (1 / 3 * epsilon : k) • (B * c) +
        i4 • ((-(1 / 24 : k)) • A ^ 2 - (1 / 6 : k) • c) +
        i3 • ((-(1 / 6 : k)) • B) +
        i2 • ((-(1 / 6 : k)) • A) := by
  rw [degreeZeroPrimitivePolynomial68_cubic_zeroLoads, hI4, hI3, hI2]
  simp only [smul_eq_C_mul]
  try ring

set_option maxHeartbeats 8000000 in
theorem firstIntegralTwo68_elim_e
    {F : Type*} [Field F] [CharZero F]
    (gamma epsilon b A c d : F) (hb : b ≠ 0) :
    let e := b ^ 2 / 9 - (3 / 4 : F) * epsilon - b⁻¹ * (c * d) -
      ((3 / 2 : F) * gamma * b⁻¹) * d
    (4 / 27 : F) * A * b ^ 3 - (4 / 9 : F) * A * b * e -
        (1 / 3 : F) * epsilon * A * b - (4 / 9 : F) * A * c * d -
        (2 / 3 : F) * gamma * A * d - (8 / 9 : F) * b ^ 2 * d -
        (8 / 9 : F) * b * c ^ 2 - (4 / 3 : F) * gamma * b * c +
        (8 / 3 : F) * d * e + (2 : F) * epsilon * d =
      (8 / 81 : F) * b ^ 3 * A - (16 / 27 : F) * b ^ 2 * d -
        (8 / 9 : F) * b * c ^ 2 - (4 / 3 : F) * b * gamma * c -
        (8 / (3 * b) : F) * c * d ^ 2 - (4 * gamma / b : F) * d ^ 2 := by
  intro e
  simp only [e]
  field_simp [hb]
  ring

theorem meeting_e_of_I4_zero68
    (gamma epsilon : k) (A c d e : k[X]) (b : k) (hb : b ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A (C b) c ((1 / 3 : k) • (A * C b) + d) e = 0) :
    e = C (b ^ 2 / 9 - (3 / 4 : k) * epsilon) -
      C b⁻¹ * (c * d) - C ((3 / 2 : k) * gamma * b⁻¹) * d := by
  have hid := fiveToSix_terminalTail_I4_F_identity68 gamma epsilon A (C b) c d e
  have hI4 :
      (8 / 3 : k) • ((C b) * e + c * d - (1 / 9 : k) • (C b) ^ 3) +
        (2 * epsilon : k) • C b + (4 * gamma : k) • d = 0 := by
    have h := hid.symm.trans hi4
    simpa using h
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  have hI4m := congrArg (algebraMap k[X] (RatFunc k)) hI4
  simp only [map_add, map_sub, map_mul, map_pow, map_neg,
    Polynomial.smul_eq_C_mul, RatFunc.algebraMap_C, map_div₀, map_ofNat,
    map_one, map_zero] at hI4m ⊢
  field_simp [hb] at hI4m ⊢
  have hb0 : RatFunc.C b ≠ 0 := by simp [hb]
  have hinv : RatFunc.C (1 / b) = (RatFunc.C b)⁻¹ := by
    rw [one_div]
    exact map_inv₀ (f := RatFunc.C) (a := b)
  try simp only [hinv] at hI4m ⊢
  apply (mul_left_injective₀ hb0).eq_iff.mp
  field_simp [hb0]
  linear_combination hI4m

set_option maxHeartbeats 8000000 in
theorem cubicFirstIntegralTwoPolynomial68_elim_e
    (gamma epsilon b : k) (A c d : k[X]) (hb : b ≠ 0) :
    cubicFirstIntegralTwoPolynomial68 gamma epsilon A (C b) c d
        (C (b ^ 2 / 9 - (3 / 4 : k) * epsilon) - C b⁻¹ * (c * d) -
          C ((3 / 2 : k) * gamma * b⁻¹) * d) =
      (8 / 81 * b ^ 3 : k) • A - (16 / 27 * b ^ 2 : k) • d -
        (8 / 9 * b : k) • c ^ 2 - (4 / 3 * b * gamma : k) • c -
        (8 / (3 * b) : k) • (c * d ^ 2) -
        (4 * gamma / b : k) • d ^ 2 := by
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [cubicFirstIntegralTwoPolynomial68, map_add, map_sub, map_mul,
    map_pow, map_neg, Polynomial.smul_eq_C_mul, RatFunc.algebraMap_C,
    map_div₀, map_ofNat, map_one, map_zero]
  convert (firstIntegralTwo68_elim_e (RatFunc.C gamma) (RatFunc.C epsilon)
      (RatFunc.C b) (algebraMap k[X] (RatFunc k) A)
      (algebraMap k[X] (RatFunc k) c) (algebraMap k[X] (RatFunc k) d)
      (by simp [hb])).symm using 1
  · have hb0 : RatFunc.C b ≠ 0 := by simp [hb]
    simp [map_inv₀ (f := RatFunc.C)]
    field_simp [hb0]
    ring
  · have hb0 : RatFunc.C b ≠ 0 := by simp [hb]
    simp [map_inv₀ (f := RatFunc.C)]
    field_simp [hb0]
    ring

theorem fiveToSix_meeting_i4_zero_impossible68
    (gamma epsilon i2 : k) (A c d e : k[X]) (b : k) (n : ℕ)
    (h2 : 2 * (n / 2) = n) (hnpos : 0 < n) (hb : b ≠ 0)
    (hA : A.natDegree ≤ 2 * n)
    (hc : c.natDegree ≤ n) (hc0 : c.coeff n ≠ 0)
    (hd : d.natDegree ≤ n / 2) (hd0 : d.coeff (n / 2) ≠ 0)
    (he : e.natDegree ≤ 3 * n / 2)
    (hcusp : A.coeff (2 * n) * b ^ 2 + (3 : k) * c.coeff n ^ 2 = 0)
    (hH : b * e.coeff (3 * n / 2) + c.coeff n * d.coeff (n / 2) = 0)
    (hY :
      ((-(2 : k)) • (A * C b ^ 2 * c) + (3 : k) • (A * d ^ 2) +
          (2 : k) • c ^ 3 - (9 : k) • e ^ 2).coeff (3 * n) = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A (C b) c ((1 / 3 : k) • (A * C b) + d) e = 0)
    (hi2 : cubicFirstIntegralTwoPolynomial68 gamma epsilon A (C b) c d e =
      C i2) :
    False := by
  have heq := meeting_e_of_I4_zero68 gamma epsilon A c d e b hb hi4
  have hI2elim :=
    cubicFirstIntegralTwoPolynomial68_elim_e gamma epsilon b A c d hb
  rw [← heq] at hI2elim
  have h2n : (2 * n : ℕ) ≠ 0 := by omega
  have hI2c :
      ((8 / 81 * b ^ 3 : k) • A - (16 / 27 * b ^ 2 : k) • d -
          (8 / 9 * b : k) • c ^ 2 - (4 / 3 * b * gamma : k) • c -
          (8 / (3 * b) : k) • (c * d ^ 2) -
          (4 * gamma / b : k) • d ^ 2).coeff (2 * n) = 0 := by
    have h := congrArg (fun p : k[X] => p.coeff (2 * n))
      (hI2elim.symm.trans hi2)
    simpa [coeff_C, h2n] using h
  have hc2 : (c ^ 2).coeff (2 * n) = c.coeff n ^ 2 :=
    coeff_pow_of_natDegree_le (m := 2) hc
  have hd2n : (d ^ 2).natDegree ≤ n := by
    have := (natDegree_pow_le (p := d) (n := 2)).trans
      (Nat.mul_le_mul_left 2 hd)
    simpa [h2] using this
  have hcd2 : (c * d ^ 2).coeff (2 * n) =
      c.coeff n * (d.coeff (n / 2)) ^ 2 := by
    have hd2 : (d ^ 2).coeff n = d.coeff (n / 2) ^ 2 := by
      have h := coeff_pow_of_natDegree_le (p := d) (n := n / 2) (m := 2) hd
      simpa [h2] using h
    have hmul := coeff_mul_add_eq_of_natDegree_le hc hd2n
    have hidx : n + n = 2 * n := by omega
    simpa [hidx, hd2] using hmul
  have hdlt : d.coeff (2 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by omega))
  have hclt : c.coeff (2 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.trans_lt (by omega))
  have hd2lt : (d ^ 2).coeff (2 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd2n.trans_lt (by omega))
  simp only [coeff_sub, coeff_smul, smul_eq_mul, hdlt, hclt, hd2lt,
    mul_zero, sub_zero, hc2, hcd2] at hI2c
  set a := A.coeff (2 * n)
  set cn := c.coeff n
  set dn := d.coeff (n / 2)
  set en := e.coeff (3 * n / 2)
  have hI2sc :
      (8 / 81 : k) * b ^ 3 * a - (8 / 9 : k) * b * cn ^ 2 -
        (8 / (3 * b) : k) * cn * dn ^ 2 = 0 := by
    convert hI2c using 1
    simp [a, cn, dn]
    ring
  have hcuspsc : a * b ^ 2 + (3 : k) * cn ^ 2 = 0 := hcusp
  have h32 : 3 * n / 2 = 3 * (n / 2) := by
    have h2dvd : 2 ∣ n := ⟨n / 2, by omega⟩
    rw [Nat.mul_div_assoc 3 h2dvd]
  have he2 : (e ^ 2).coeff (3 * n) = en ^ 2 := by
    have h := coeff_pow_of_natDegree_le (p := e) (n := 3 * n / 2) (m := 2) he
    have hidx : 2 * (3 * n / 2) = 3 * n := by omega
    simpa [hidx, en] using h
  have hAd2 : (A * d ^ 2).coeff (3 * n) = a * dn ^ 2 := by
    have hmul := coeff_mul_add_eq_of_natDegree_le hA hd2n
    have hidx : 2 * n + n = 3 * n := by omega
    have hd2 : (d ^ 2).coeff n = dn ^ 2 := by
      have h := coeff_pow_of_natDegree_le (p := d) (n := n / 2) (m := 2) hd
      simpa [h2, dn] using h
    simpa [hidx, a, hd2] using hmul
  have hAbc : (A * C b ^ 2 * c).coeff (3 * n) = a * b ^ 2 * cn := by
    have h1 : A * C b ^ 2 * c = C (b ^ 2) * (A * c) := by
      simp [C_pow]
      ring
    have hAc : (A * c).coeff (3 * n) = a * cn := by
      have hmul := coeff_mul_add_eq_of_natDegree_le hA hc
      have hidx : 2 * n + n = 3 * n := by omega
      simpa [hidx, a, cn] using hmul
    rw [h1, coeff_C_mul, hAc]
    ring
  have hc3 : (c ^ 3).coeff (3 * n) = cn ^ 3 :=
    coeff_pow_of_natDegree_le (m := 3) hc
  have hYsc :
      -(2 : k) * a * b ^ 2 * cn + (3 : k) * a * dn ^ 2 +
        (2 : k) * cn ^ 3 - (9 : k) * en ^ 2 = 0 := by
    simp only [coeff_add, coeff_sub, coeff_smul, smul_eq_mul, hAbc, hAd2,
      hc3, he2] at hY
    simpa [a, cn, dn, en, mul_assoc, mul_left_comm, mul_comm] using hY
  have hHsc : b * en + cn * dn = 0 := hH
  have hb2ne : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
  have haeq : a = -(3 : k) * cn ^ 2 * (b ^ 2)⁻¹ := by
    field_simp [hb2ne] at hcuspsc ⊢
    linear_combination hcuspsc
  have hrel : (4 : k) * b ^ 2 * cn + (9 : k) * dn ^ 2 = 0 := by
    have h := hI2sc
    simp only [haeq] at h
    have hcn : cn ≠ 0 := hc0
    field_simp [hb, hb2ne, hcn] at h
    have hprod : cn * (4 * b ^ 2 * cn + 9 * dn ^ 2) = 0 := by
      have hneg :
          (2592 : k) * b ^ 2 * cn ^ 2 + (5832 : k) * cn * dn ^ 2 = 0 := by
        linear_combination -h
      have hscale :
          (648 : k) * (cn * (4 * b ^ 2 * cn + 9 * dn ^ 2)) =
            (2592 : k) * b ^ 2 * cn ^ 2 + (5832 : k) * cn * dn ^ 2 := by
        ring
      have hx := hscale.trans hneg
      exact (mul_eq_zero.mp hx).resolve_left (by norm_num)
    exact (mul_eq_zero.mp hprod).resolve_left hcn
  have hen : en = -cn * dn * b⁻¹ := by
    field_simp [hb] at hHsc ⊢
    linear_combination hHsc
  have hrelY : (4 : k) * b ^ 2 * cn - (9 : k) * dn ^ 2 = 0 := by
    have hy := hYsc
    have hcn : cn ≠ 0 := hc0
    simp only [haeq, hen] at hy
    field_simp [hb, hb2ne, hcn] at hy
    have hprod : cn ^ 2 * (4 * b ^ 2 * cn - 9 * dn ^ 2) = 0 := by
      have hscale :
          (2 : k) * (cn ^ 2 * (4 * b ^ 2 * cn - 9 * dn ^ 2)) =
            (8 : k) * b ^ 2 * cn ^ 3 - (18 : k) * cn ^ 2 * dn ^ 2 := by
        ring
      have hy' :
          (8 : k) * b ^ 2 * cn ^ 3 - (18 : k) * cn ^ 2 * dn ^ 2 = 0 := by
        linear_combination hy
      have hx := hscale.trans hy'
      exact (mul_eq_zero.mp hx).resolve_left (by norm_num)
    have hcn2 : cn ^ 2 ≠ 0 := pow_ne_zero 2 hcn
    exact (mul_eq_zero.mp hprod).resolve_left hcn2
  have hdn0 : (18 : k) * dn ^ 2 = 0 := by
    linear_combination hrel - hrelY
  have h18 : (18 : k) ≠ 0 := by norm_num
  have hdn2 : dn ^ 2 = 0 :=
    (mul_eq_zero.mp hdn0).resolve_left h18
  exact hd0 (eq_zero_of_pow_eq_zero hdn2)

theorem natDegree_add_le_of_le68 {p q : k[X]} {N : ℕ}
    (hp : p.natDegree ≤ N) (hq : q.natDegree ≤ N) :
    (p + q).natDegree ≤ N :=
  (natDegree_add_le p q).trans (max_le hp hq)

theorem natDegree_sub_le_of_le68 {p q : k[X]} {N : ℕ}
    (hp : p.natDegree ≤ N) (hq : q.natDegree ≤ N) :
    (p - q).natDegree ≤ N :=
  (natDegree_sub_le p q).trans (max_le hp hq)

theorem meeting_fiveHalves_arith68 (n : ℕ) (h2 : 2 * (n / 2) = n) :
    n + 3 * n / 2 = 5 * n / 2 ∧
      2 * n + n / 2 = 5 * n / 2 ∧
      3 * n / 2 = 3 * (n / 2) ∧
      5 * n / 2 = 5 * (n / 2) := by
  have h2dvd : 2 ∣ n := ⟨n / 2, by omega⟩
  have h32 : 3 * n / 2 = 3 * (n / 2) := by rw [Nat.mul_div_assoc 3 h2dvd]
  have h52 : 5 * n / 2 = 5 * (n / 2) := by rw [Nat.mul_div_assoc 5 h2dvd]
  refine ⟨?_, ?_, h32, h52⟩
  · have : n + 3 * (n / 2) = 5 * (n / 2) := by omega
    rw [h32, h52, this]
  · have : 2 * n + n / 2 = 5 * (n / 2) := by omega
    rw [h52, this]

theorem meeting_primitive_low_natDegree_le68
    (gamma epsilon i3 i2 b : k) (A c d e : k[X]) (n : ℕ)
    (h2 : 2 * (n / 2) = n) (hn : 0 < n)
    (hA : A.natDegree ≤ 2 * n) (hc : c.natDegree ≤ n)
    (hd : d.natDegree ≤ n / 2) (he : e.natDegree ≤ 3 * n / 2) :
    (C b *
          ((-(4 / 81 : k)) • ((C b) ^ 2 * c) + (4 / 9 : k) • (c * e) -
            (4 / 27 : k) • (A * C b * d) - (2 / 9 : k) • d ^ 2) +
        (2 / 3 * gamma : k) • (C b * e) -
        (1 / 27 * gamma : k) • (C b) ^ 3 +
        (1 / 3 * epsilon : k) • (C b * c) +
        i3 • ((-(1 / 6 : k)) • C b) +
        i2 • ((-(1 / 6 : k)) • A)).natDegree ≤
      5 * n / 2 := by
  obtain ⟨_, _, _, h52⟩ := meeting_fiveHalves_arith68 n h2
  have hN0 : 0 ≤ 5 * n / 2 := Nat.zero_le _
  have hNn : n ≤ 5 * n / 2 := by
    have : n = 2 * (n / 2) := h2.symm
    omega
  have hN2 : 2 * n ≤ 5 * n / 2 := by
    have : 2 * n = 4 * (n / 2) := by omega
    omega
  have hN32 : 3 * n / 2 ≤ 5 * n / 2 := by omega
  have hCb : (C b).natDegree ≤ 0 := by simp [natDegree_C]
  have hB2 : ((C b) ^ 2).natDegree ≤ 0 := by
    simp [C_pow, natDegree_C]
  have hB3 : ((C b) ^ 3).natDegree ≤ 0 := by
    simp [C_pow, natDegree_C]
  have hB2c : ((C b) ^ 2 * c).natDegree ≤ n :=
    (natDegree_mul_le_add68 hB2 hc).trans (by omega)
  have hce : (c * e).natDegree ≤ 5 * n / 2 :=
    (natDegree_mul_le_add68 hc he).trans (by omega)
  have hACb : (A * C b).natDegree ≤ 2 * n :=
    (natDegree_mul_le_add68 hA hCb).trans (by omega)
  have hAd : (A * C b * d).natDegree ≤ 5 * n / 2 :=
    (natDegree_mul_le_add68 hACb hd).trans (by omega)
  have hd2 : (d ^ 2).natDegree ≤ n := by
    have := (natDegree_pow_le (p := d) (n := 2)).trans
      (Nat.mul_le_mul_left 2 hd)
    simpa [h2] using this
  have hBe : (C b * e).natDegree ≤ 3 * n / 2 :=
    (natDegree_mul_le_add68 hCb he).trans (by omega)
  have hBc : (C b * c).natDegree ≤ n :=
    (natDegree_mul_le_add68 hCb hc).trans (by omega)
  have hinner :
      ((-(4 / 81 : k)) • ((C b) ^ 2 * c) + (4 / 9 : k) • (c * e) -
          (4 / 27 : k) • (A * C b * d) - (2 / 9 : k) • d ^ 2).natDegree ≤
        5 * n / 2 := by
    refine natDegree_sub_le_of_le68
      (natDegree_sub_le_of_le68
        (natDegree_add_le_of_le68
          ((natDegree_smul_le68 _ _).trans (hB2c.trans hNn))
          ((natDegree_smul_le68 _ _).trans hce))
        ((natDegree_smul_le68 _ _).trans hAd))
      ((natDegree_smul_le68 _ _).trans (hd2.trans hNn))
  have hmain :
      (C b *
          ((-(4 / 81 : k)) • ((C b) ^ 2 * c) + (4 / 9 : k) • (c * e) -
            (4 / 27 : k) • (A * C b * d) - (2 / 9 : k) • d ^ 2)).natDegree ≤
        5 * n / 2 :=
    (natDegree_mul_le_add68 hCb hinner).trans (by omega)
  have hge : ((2 / 3 * gamma : k) • (C b * e)).natDegree ≤ 5 * n / 2 :=
    (natDegree_smul_le68 _ _).trans (hBe.trans hN32)
  have hgB : ((1 / 27 * gamma : k) • (C b) ^ 3).natDegree ≤ 5 * n / 2 :=
    (natDegree_smul_le68 _ _).trans (hB3.trans hN0)
  have hec : ((1 / 3 * epsilon : k) • (C b * c)).natDegree ≤ 5 * n / 2 :=
    (natDegree_smul_le68 _ _).trans (hBc.trans hNn)
  have hB3g : (i3 • ((-(1 / 6 : k)) • C b)).natDegree ≤ 5 * n / 2 :=
    (natDegree_smul_le68 _ _).trans
      ((natDegree_smul_le68 _ _).trans (hCb.trans hN0))
  have hA2g : (i2 • ((-(1 / 6 : k)) • A)).natDegree ≤ 5 * n / 2 :=
    (natDegree_smul_le68 _ _).trans
      ((natDegree_smul_le68 _ _).trans (hA.trans hN2))
  refine natDegree_add_le_of_le68 ?_ hA2g
  refine natDegree_add_le_of_le68 ?_ hB3g
  refine natDegree_add_le_of_le68 ?_ hec
  refine natDegree_sub_le_of_le68 ?_ hgB
  exact natDegree_add_le_of_le68 hmain hge

theorem degreeZeroPrimitivePolynomial68_cubic_low_add_i4
    (alpha gamma epsilon eta i4 i3 i2 b : k) (A c d e : k[X])
    (hI4 : firstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0 A (C b)
      ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * C b) + d)
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) = C i4)
    (hI3 : firstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0 A (C b)
      ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * C b) + d)
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) = C i3)
    (hI2 : firstIntegralTwoPolynomial68 0 0 gamma 0 epsilon 0 A (C b)
      ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * C b) + d)
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) = C i2) :
    degreeZeroPrimitivePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta A (C b)
        ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * C b) + d)
        ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) =
      (C b *
            ((-(4 / 81 : k)) • ((C b) ^ 2 * c) + (4 / 9 : k) • (c * e) -
              (4 / 27 : k) • (A * C b * d) - (2 / 9 : k) • d ^ 2) +
          (2 / 3 * gamma : k) • (C b * e) -
          (1 / 27 * gamma : k) • (C b) ^ 3 +
          (1 / 3 * epsilon : k) • (C b * c) +
          i3 • ((-(1 / 6 : k)) • C b) +
          i2 • ((-(1 / 6 : k)) • A)) +
        i4 • ((-(1 / 24 : k)) • A ^ 2 - (1 / 6 : k) • c) := by
  rw [degreeZeroPrimitivePolynomial68_cubic_of_integrals_const
    alpha gamma epsilon eta i4 i3 i2 A (C b) c d e hI4 hI3 hI2]
  simp only [smul_eq_C_mul]
  ring

theorem meeting_i4_of_primitive_coeff_fourN68
    (alpha gamma epsilon eta i4 i3 i2 b : k) (A c d e : k[X]) (n : ℕ)
    (h2 : 2 * (n / 2) = n) (hn : 0 < n) (hn4 : 60 < 4 * n)
    (hA : A.natDegree ≤ 2 * n) (ha : A.coeff (2 * n) ≠ 0)
    (hc : c.natDegree ≤ n) (hd : d.natDegree ≤ n / 2)
    (he : e.natDegree ≤ 3 * n / 2)
    (hI4 : firstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0 A (C b)
      ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * C b) + d)
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) = C i4)
    (hI3 : firstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0 A (C b)
      ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * C b) + d)
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) = C i3)
    (hI2 : firstIntegralTwoPolynomial68 0 0 gamma 0 epsilon 0 A (C b)
      ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * C b) + d)
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) = C i2)
    (hdeg :
      (degreeZeroPrimitivePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A (C b) ((1 / 3 : k) • A ^ 2 + c)
          ((1 / 3 : k) • (A * C b) + d)
          ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).natDegree ≤
        60) :
    i4 = 0 := by
  set rho :=
    degreeZeroPrimitivePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta A
      (C b) ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * C b) + d)
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
  set low :=
    C b *
        ((-(4 / 81 : k)) • ((C b) ^ 2 * c) + (4 / 9 : k) • (c * e) -
          (4 / 27 : k) • (A * C b * d) - (2 / 9 : k) • d ^ 2) +
      (2 / 3 * gamma : k) • (C b * e) -
      (1 / 27 * gamma : k) • (C b) ^ 3 +
      (1 / 3 * epsilon : k) • (C b * c) +
      i3 • ((-(1 / 6 : k)) • C b) +
      i2 • ((-(1 / 6 : k)) • A)
  have hsplit :=
    degreeZeroPrimitivePolynomial68_cubic_low_add_i4 alpha gamma
      epsilon eta i4 i3 i2 b A c d e hI4 hI3 hI2
  have hlow :
      low.natDegree ≤ 5 * n / 2 :=
    meeting_primitive_low_natDegree_le68 gamma epsilon i3 i2 b A c d e
      n h2 hn hA hc hd he
  have h52lt : 5 * n / 2 < 4 * n := by
    obtain ⟨_, _, _, h52⟩ := meeting_fiveHalves_arith68 n h2
    have : 5 * (n / 2) < 4 * n := by omega
    omega
  have hrho4 : rho.coeff (4 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hn4)
  have hlow4 : low.coeff (4 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hlow.trans_lt h52lt)
  have hc4 : c.coeff (4 * n) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.trans_lt (by omega))
  have hA2 : (A ^ 2).coeff (4 * n) = A.coeff (2 * n) ^ 2 := by
    have h := coeff_pow_of_natDegree_le (p := A) (n := 2 * n) (m := 2) hA
    have hidx : 2 * (2 * n) = 4 * n := by omega
    simpa [hidx] using h
  have hcoeff : i4 * (-(1 / 24 : k)) * A.coeff (2 * n) ^ 2 = 0 := by
    have h := congrArg (fun p : k[X] => p.coeff (4 * n)) hsplit
    change rho.coeff (4 * n) =
        (low + i4 • ((-(1 / 24 : k)) • A ^ 2 - (1 / 6 : k) • c)).coeff
          (4 * n) at h
    simp only [hrho4, hlow4, coeff_add, coeff_smul, coeff_sub, smul_eq_mul,
      hA2, hc4, mul_zero, sub_zero, zero_add] at h
    convert h.symm using 1
    ring
  have h24 : (-(1 / 24 : k)) ≠ 0 := by norm_num
  have ha2 : A.coeff (2 * n) ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have hprod : i4 * ((-(1 / 24 : k)) * A.coeff (2 * n) ^ 2) = 0 := by
    convert hcoeff using 1
    ring
  exact (mul_eq_zero.mp hprod).resolve_right (mul_ne_zero h24 ha2)

/-! ## Meeting-cell index, degree, and coordinate transport -/

theorem meeting_cell_B_natDegree_le_zero68
    (B : k[X]) (n g : ℕ) (hD0 : g = 3 * n)
    (hB : B.natDegree ≤ 3 * n - g) :
    B.natDegree ≤ 0 := by
  have hidx : 3 * n - g = 0 := by omega
  rwa [hidx] at hB

theorem meeting_cell_c_natDegree_le_n68
    (c : k[X]) (n g : ℕ) (hD0 : g = 3 * n)
    (hc : c.natDegree ≤ 4 * n - g) :
    c.natDegree ≤ n := by
  have hsub : 4 * n - 3 * n = n := by omega
  have hidx : 4 * n - g = n := by
    rw [hD0]
    exact hsub
  rwa [hidx] at hc

theorem meeting_cell_d_natDegree_le_half68
    (d : k[X]) (n g t : ℕ) (hD0 : g = 3 * n) (hnt : n = 2 * t)
    (hd : d.natDegree ≤ g - 2 * n - t) :
    d.natDegree ≤ n / 2 := by
  have hidx : g - 2 * n - t = n / 2 := by omega
  rwa [hidx] at hd

theorem meeting_cell_e_natDegree_le_threeHalves68
    (e : k[X]) (n g t : ℕ) (hD0 : g = 3 * n) (hnt : n = 2 * t)
    (h2 : 2 * (n / 2) = n) (he : e.natDegree ≤ g - n - t) :
    e.natDegree ≤ 3 * n / 2 := by
  have h32 : 3 * n / 2 = 3 * (n / 2) :=
    (meeting_fiveHalves_arith68 n h2).2.2.1
  have hidx : g - n - t = 3 * n / 2 := by omega
  rwa [hidx] at he

theorem meeting_cell_B_coeff_zero68
    (B : k[X]) (n g : ℕ) (hD0 : g = 3 * n)
    (h : B.coeff (3 * n - g) ≠ 0) :
    B.coeff 0 ≠ 0 := by
  have hidx : 3 * n - g = 0 := by omega
  rwa [hidx] at h

theorem meeting_cell_c_coeff_n68
    (c : k[X]) (n g : ℕ) (hD0 : g = 3 * n)
    (h : c.coeff (4 * n - g) ≠ 0) :
    c.coeff n ≠ 0 := by
  have hsub : 4 * n - 3 * n = n := by omega
  have hidx : 4 * n - g = n := by
    rw [hD0]
    exact hsub
  rwa [hidx] at h

theorem meeting_cell_d_coeff_half68
    (d : k[X]) (n g t : ℕ) (hD0 : g = 3 * n) (hnt : n = 2 * t)
    (h : d.coeff (5 * n - g - (7 * n - 2 * g + t)) ≠ 0) :
    d.coeff (n / 2) ≠ 0 := by
  have hidx : 5 * n - g - (7 * n - 2 * g + t) = n / 2 := by omega
  rwa [hidx] at h

theorem meeting_cell_cusp_scalar68
    (A B c : k[X]) (n g : ℕ) (b : k)
    (hD0 : g = 3 * n) (hb : b = B.coeff 0)
    (h : A.coeff (2 * n) * B.coeff (3 * n - g) ^ 2 +
      (3 : k) * c.coeff (4 * n - g) ^ 2 = 0) :
    A.coeff (2 * n) * b ^ 2 + (3 : k) * c.coeff n ^ 2 = 0 := by
  have hsub : 4 * n - 3 * n = n := by omega
  rw [hD0] at h
  rw [hsub] at h
  have hB0 : 3 * n - 3 * n = 0 := by omega
  rw [hB0, ← hb] at h
  exact h

theorem degreeZeroPrimitivePolynomial68_of_zeroLoads
    (alpha gamma epsilon eta l beta delta zeta : k) (A B C0 D E : k[X])
    (hl : l = 0) (hbeta : beta = 0) (hdelta : delta = 0)
    (hzeta : zeta = 0) :
    degreeZeroPrimitivePolynomial68 l alpha beta gamma delta epsilon zeta
        eta A B C0 D E =
      degreeZeroPrimitivePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B C0 D E := by
  rw [hl, hbeta, hdelta, hzeta]

theorem expand60_degreeZeroPrimitivePolynomial68_natDegree
    (l alpha beta gamma delta epsilon zeta eta : k)
    (A B C0 D E : k[X])
    (hsrc : (degreeZeroPrimitivePolynomial68 l alpha beta gamma delta
        epsilon zeta eta A B C0 D E).natDegree = 1) :
    (degreeZeroPrimitivePolynomial68 l alpha beta gamma delta epsilon
        zeta eta (expand k 60 A) (expand k 60 B) (expand k 60 C0)
        (expand k 60 D) (expand k 60 E)).natDegree = 60 := by
  rw [← expand_degreeZeroPrimitivePolynomial68, natDegree_expand, hsrc]

theorem degreeZeroPrimitivePolynomial68_cubic_constB_natDegree_le68
    (alpha gamma epsilon eta : k) (A B C0 D E c d e : k[X]) (b : k)
    (hCrec : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hDrec : D = (1 / 3 : k) • (A * B) + d)
    (hErec : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hBeC : B = C b)
    (hdeg : (degreeZeroPrimitivePolynomial68 0 alpha 0 gamma 0 epsilon 0
      eta A B C0 D E).natDegree ≤ 60) :
    (degreeZeroPrimitivePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta A
      (C b) ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * C b) + d)
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)).natDegree ≤
      60 := by
  rw [← hBeC, ← hCrec, ← hDrec, ← hErec]
  exact hdeg

theorem firstIntegralTwoPolynomial68_cubic_constB68
    (gamma epsilon i2 : k) (A B C0 D E c d e : k[X]) (b : k)
    (hCrec : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hDrec : D = (1 / 3 : k) • (A * B) + d)
    (hErec : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hBeC : B = C b)
    (hI2 : firstIntegralTwoPolynomial68 0 0 gamma 0 epsilon 0 A B C0 D E =
      C i2) :
    firstIntegralTwoPolynomial68 0 0 gamma 0 epsilon 0 A (C b)
      ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * C b) + d)
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) = C i2 := by
  rw [← hBeC, ← hCrec, ← hDrec, ← hErec]
  exact hI2

theorem firstIntegralFourPolynomial68_cubic_constB68
    (gamma epsilon i4 : k) (A B c d e : k[X]) (b : k)
    (hBeC : B = C b)
    (hI4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i4) :
    firstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0 A (C b)
      ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * C b) + d)
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) = C i4 := by
  rw [firstIntegralFourPolynomial68_cubicCoordinates, ← hBeC]
  exact hI4

theorem firstIntegralThreePolynomial68_cubic_constB68
    (gamma epsilon i3 : k) (A B c d e : k[X]) (b : k)
    (hBeC : B = C b)
    (hI3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3) :
    firstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0 A (C b)
      ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * C b) + d)
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) = C i3 := by
  rw [firstIntegralThreePolynomial68_cubicCoordinates, ← hBeC]
  exact hI3

theorem cubicFirstIntegralFourPolynomial68_constB_i4_zero68
    (gamma epsilon i4 : k) (A B c d e : k[X]) (b : k)
    (hBeC : B = C b) (hi4z : i4 = 0)
    (hI4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i4) :
    cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A (C b) c ((1 / 3 : k) • (A * C b) + d) e = 0 := by
  rw [← hBeC, hI4, hi4z, C_0]

theorem meeting_cell_H_constB68
    (B c d e : k[X]) (n g t : ℕ) (b : k)
    (hD0 : g = 3 * n) (hnt : n = 2 * t) (h2 : 2 * (n / 2) = n)
    (hb : b = B.coeff 0)
    (hH : B.coeff (3 * n - g) * e.coeff (g - n - t) +
      c.coeff (4 * n - g) * d.coeff (g - 2 * n - t) = 0) :
    b * e.coeff (3 * n / 2) + c.coeff n * d.coeff (n / 2) = 0 := by
  have hBidx : 3 * n - g = 0 := by omega
  have hsub : 4 * n - 3 * n = n := by omega
  have hCidx : 4 * n - g = n := by
    rw [hD0]
    exact hsub
  have h32 : 3 * n / 2 = 3 * (n / 2) :=
    (meeting_fiveHalves_arith68 n h2).2.2.1
  have hidxe : g - n - t = 3 * n / 2 := by omega
  have hidxd : g - 2 * n - t = n / 2 := by omega
  rw [hBidx, hCidx, hidxe, hidxd, ← hb] at hH
  exact hH

theorem meeting_cell_Y_constB68
    (A B c d e : k[X]) (n : ℕ) (b : k) (hBeC : B = C b)
    (hY : ((-(2 : k)) • (A * B ^ 2 * c) + (3 : k) • (A * d ^ 2) +
        (2 : k) • c ^ 3 - (9 : k) • e ^ 2).coeff (3 * n) = 0) :
    ((-(2 : k)) • (A * C b ^ 2 * c) + (3 : k) • (A * d ^ 2) +
        (2 : k) • c ^ 3 - (9 : k) • e ^ 2).coeff (3 * n) = 0 := by
  rw [← hBeC]
  exact hY

theorem firstIntegralTwoPolynomial68_to_cubic_constB68
    (gamma epsilon i2 : k) (A c d e : k[X]) (b : k)
    (hI2b : firstIntegralTwoPolynomial68 0 0 gamma 0 epsilon 0 A (C b)
      ((1 / 3 : k) • A ^ 2 + c) ((1 / 3 : k) • (A * C b) + d)
      ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e) = C i2) :
    cubicFirstIntegralTwoPolynomial68 gamma epsilon A (C b) c d e =
      C i2 := by
  rw [← firstIntegralTwoPolynomial68_cubicCoordinates]
  exact hI2b

theorem fiveToSix_meetingCell_kill68
    (alpha gamma epsilon eta i4 i3 i2 : k)
    (A B C0 D E c d e : k[X]) (n g t : ℕ) (b : k)
    (h2 : 2 * (n / 2) = n) (hn : 0 < n) (hn4 : 60 < 4 * n)
    (hD0 : g = 3 * n) (hnt : n = 2 * t)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (htle : t ≤ g - 2 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc_raw : c.natDegree ≤ 4 * n - g)
    (hc : c.natDegree ≤ n)
    (hd : d.natDegree ≤ g - 2 * n - t)
    (hd' : d.natDegree ≤ n / 2)
    (he : e.natDegree ≤ g - n - t)
    (he' : e.natDegree ≤ 3 * n / 2)
    (hBeC : B = C b) (hb : b ≠ 0) (hbdef : b = B.coeff 0)
    (ha : A.coeff (2 * n) ≠ 0)
    (hc0 : c.coeff n ≠ 0)
    (hd0 : d.coeff (n / 2) ≠ 0)
    (hcuspsc : A.coeff (2 * n) * b ^ 2 + (3 : k) * c.coeff n ^ 2 = 0)
    (hCrec : C0 = (1 / 3 : k) • A ^ 2 + c)
    (hDrec : D = (1 / 3 : k) • (A * B) + d)
    (hErec : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (hI4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hI3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow1 : secondaryResidualRowOnePolynomial68 A B c d e +
        cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e = 0)
    (hI2 : firstIntegralTwoPolynomial68 0 0 gamma 0 epsilon 0 A B C0 D E =
      C i2)
    (hprimdeg : (degreeZeroPrimitivePolynomial68 0 alpha 0 gamma 0
        epsilon 0 eta A B C0 D E).natDegree = 60) :
    False := by
  have hI2b :=
    firstIntegralTwoPolynomial68_cubic_constB68 gamma epsilon i2 A B C0 D
      E c d e b hCrec hDrec hErec hBeC hI2
  have hI4b :=
    firstIntegralFourPolynomial68_cubic_constB68 gamma epsilon i4 A B c d
      e b hBeC hI4
  have hI3b :=
    firstIntegralThreePolynomial68_cubic_constB68 gamma epsilon i3 A B c d
      e b hBeC hI3
  have hprimdeg' :=
    degreeZeroPrimitivePolynomial68_cubic_constB_natDegree_le68 alpha
      gamma epsilon eta A B C0 D E c d e b hCrec hDrec hErec hBeC
      hprimdeg.le
  have hi4z : i4 = 0 :=
    meeting_i4_of_primitive_coeff_fourN68 alpha gamma epsilon eta i4 i3
      i2 b A c d e n h2 hn hn4 hA ha hc hd' he' hI4b hI3b hI2b hprimdeg'
  have hge : n ≤ 2 * t := by omega
  have hY :=
    fiveToSix_terminalTail_Y_coeff_constantB68 alpha gamma epsilon eta i3
      A B c d e n g t hn hwindow htle hD0 hge hA hB hc_raw hd he hI3
      hrow1
  have hH :=
    fiveToSix_terminalTail_H_face68 gamma epsilon i4 A B c d e n g t hn
      hwindow htle hB hc_raw hd he hI4
  have hYb := meeting_cell_Y_constB68 A B c d e n b hBeC hY
  have hHb := meeting_cell_H_constB68 B c d e n g t b hD0 hnt h2 hbdef hH
  have hi4poly :=
    cubicFirstIntegralFourPolynomial68_constB_i4_zero68 gamma epsilon i4
      A B c d e b hBeC hi4z hI4
  have hi2poly :=
    firstIntegralTwoPolynomial68_to_cubic_constB68 gamma epsilon i2 A c d
      e b hI2b
  exact fiveToSix_meeting_i4_zero_impossible68 gamma epsilon i2 A c d e b
    n h2 hn hb hA hc hc0 hd' hd0 he' hcuspsc hHb hYb hi4poly hi2poly

set_option maxHeartbeats 25000000 in
theorem fiveToSix_terminalZero_meetingCell_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (t : ℕ) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hzeta : zeta = 0)
    (htle :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      t ≤ g - 2 * n)
    (hd :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      d.natDegree ≤ g - 2 * n - t)
    (he :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      ee.natDegree ≤ g - n - t)
    (hcusp :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g + t))
    (hmeet :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      g = 3 * n ∧ n = 2 * t) :
    False := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  change t ≤ g - 2 * n at htle
  change d.natDegree ≤ g - 2 * n - t at hd
  change ee.natDegree ≤ g - n - t at he
  change FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g + t) at hcusp
  change g = 3 * n ∧ n = 2 * t at hmeet
  obtain ⟨hD0, hnt⟩ := hmeet
  have hfaces :=
    fiveToSix_terminalTail_system_faces68 l alpha beta gamma delta epsilon
      zeta eta terminal A B C0 D E hterminal hsys hzeta
  rcases hfaces with ⟨hl, hbeta, hdelta, ⟨i4, hi4⟩, ⟨i3, hi3⟩, _, hrow1⟩
  have data :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
  change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
    n g Ae Be ce De ee at data
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n :=
    ⟨hglobal.1, hglobal.2.1⟩
  have hn30 : 30 < n := hglobal.2.2.2.2.2.2.1
  have hn : 0 < n := Nat.zero_lt_of_lt hn30
  have h2 : 2 * (n / 2) = n := by omega
  have hn4 : 60 < 4 * n := by omega
  have hA : Ae.natDegree ≤ 2 * n := data.hA
  have hB0 : Be.natDegree ≤ 0 :=
    meeting_cell_B_natDegree_le_zero68 Be n g hD0 data.hB
  have hc : ce.natDegree ≤ n :=
    meeting_cell_c_natDegree_le_n68 ce n g hD0 data.hc
  have hd' : d.natDegree ≤ n / 2 :=
    meeting_cell_d_natDegree_le_half68 d n g t hD0 hnt hd
  have he' : ee.natDegree ≤ 3 * n / 2 :=
    meeting_cell_e_natDegree_le_threeHalves68 ee n g t hD0 hnt h2 he
  have hBeC : Be = C (Be.coeff 0) := eq_C_of_natDegree_le_zero hB0
  set b := Be.coeff 0
  have hb : b ≠ 0 :=
    meeting_cell_B_coeff_zero68 Be n g hD0 hcusp.1
  have hc0 : ce.coeff n ≠ 0 :=
    meeting_cell_c_coeff_n68 ce n g hD0 hcusp.2.1
  have hd0 : d.coeff (n / 2) ≠ 0 :=
    meeting_cell_d_coeff_half68 d n g t hD0 hnt hcusp.2.2.1
  have ha : Ae.coeff (2 * n) ≠ 0 :=
    fiveToSix_terminalTail_cusp_A_top68 Ae Be ce d ee n g
      (7 * n - 2 * g + t) hcusp
  have hcuspsc :
      Ae.coeff (2 * n) * b ^ 2 + (3 : k) * ce.coeff n ^ 2 = 0 :=
    meeting_cell_cusp_scalar68 Ae Be ce n g b hD0 rfl hcusp.2.2.2.2
  have hCrec : Ce = (1 / 3 : k) • Ae ^ 2 + ce :=
    cubicCDefectPolynomial68_reconstruct Ae Ce
  have hDrec : De = (1 / 3 : k) • (Ae * Be) + d :=
    secondaryDDefectPolynomial68_reconstruct Ae Be De
  have hErec : Ee =
      (1 / 27 : k) • Ae ^ 3 + (1 / 3 : k) • (Ae * ce) + ee :=
    cubicEDefectPolynomial68_eq_cubicCoordinates Ae Ce Ee
  have ⟨i2, hi2raw⟩ :=
    integratedPolynomialLowerSystem68_firstIntegralTwo_const68 l alpha
      beta gamma delta epsilon zeta eta terminal A B C0 D E hsys
  have hi2e :
      firstIntegralTwoPolynomial68 l beta gamma delta epsilon zeta
        Ae Be Ce De Ee = C i2 :=
    expand_firstIntegralTwoPolynomial68_of_eq l beta gamma delta epsilon
      zeta i2 A B C0 D E hi2raw
  have hI2 :
      firstIntegralTwoPolynomial68 0 0 gamma 0 epsilon 0 Ae Be Ce De Ee =
        C i2 := by
    rw [hl, hbeta, hdelta, hzeta] at hi2e
    exact hi2e
  have hprimdeg :
      (degreeZeroPrimitivePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          Ae Be Ce De Ee).natDegree = 60 := by
    have hsrc :=
      integratedPolynomialLowerSystem68_degreeZeroPrimitive_natDegree68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys
    have hnat :
        (degreeZeroPrimitivePolynomial68 l alpha beta gamma delta epsilon
            zeta eta Ae Be Ce De Ee).natDegree = 60 :=
      expand60_degreeZeroPrimitivePolynomial68_natDegree l alpha beta
        gamma delta epsilon zeta eta A B C0 D E hsrc
    rw [degreeZeroPrimitivePolynomial68_of_zeroLoads alpha gamma epsilon
      eta l beta delta zeta Ae Be Ce De Ee hl hbeta hdelta hzeta] at hnat
    exact hnat
  exact fiveToSix_meetingCell_kill68 alpha gamma epsilon eta i4 i3 i2
    Ae Be Ce De Ee ce d ee n g t b h2 hn hn4 hD0 hnt hwindow htle hA
    data.hB data.hc hc hd hd' he he' hBeC hb rfl ha hc0 hd0 hcuspsc
    hCrec hDrec hErec hi4 hi3 hrow1 hI2 hprimdeg

set_option maxHeartbeats 25000000 in
theorem fiveToSix_terminalZero_aligned_cusp_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (t : ℕ) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hzeta : zeta = 0)
    (htle :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      t ≤ g - 2 * n)
    (hd :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      d.natDegree ≤ g - 2 * n - t)
    (he :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      ee.natDegree ≤ g - n - t)
    (hcusp :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      FiveToSixCuspEdge68 Ae Be ce d ee n g (7 * n - 2 * g + t)) :
    False := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  change t ≤ g - 2 * n at htle
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n :=
    ⟨hglobal.1, hglobal.2.1⟩
  by_cases hD : g < 3 * n
  · exact fiveToSix_terminalZero_aligned_cusp_closable_of68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E t
      hterminal hsys hzeta htle hd he hcusp (Or.inl hD)
  · have hD0 : g = 3 * n := by omega
    by_cases hde : 2 * t < n
    · have hclosable : 14 * n + 2 * t < 5 * g := by
        rw [hD0]
        omega
      exact fiveToSix_terminalZero_aligned_cusp_closable_of68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E t
        hterminal hsys hzeta htle hd he hcusp (Or.inr hclosable)
    · by_cases hnt : n = 2 * t
      · exact fiveToSix_terminalZero_meetingCell_impossible68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E t
          hterminal hsys hzeta htle hd he hcusp ⟨hD0, hnt⟩
      · have hQ : n < 2 * t := by omega
        exact fiveToSix_terminalTail_cusp_impossible_of_constantB_Qhigher68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E t
          hterminal hsys hzeta htle hd he hcusp hD0 hQ

set_option maxHeartbeats 40000000 in
theorem fiveToSix_terminalZero_aligned_big_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hpacket :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      FiveToSixTerminalZeroPacket68 zeta d ee n g)
    (hnbig : 120 < weightedRadius68 A B C0 D E)
    (hn60 : 60 ∣ weightedRadius68 A B C0 D E)
    (hg60 :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      60 ∣ g) :
    False := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  change FiveToSixTerminalZeroPacket68 zeta d ee n g at hpacket
  change 120 < n at hnbig
  change 60 ∣ n at hn60
  change 60 ∣ g at hg60
  have hzeta : zeta = 0 := hpacket.2.2.1
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n :=
    ⟨hglobal.1, hglobal.2.1⟩
  have h2n : 2 * n ≤ g := by
    obtain ⟨hw5, _⟩ := hwindow
    omega
  have hdexpand : d = expand k 60 (secondaryDDefectPolynomial68 A B D) := by
    simpa only [d, Ae, Be, De] using
      secondaryDDefectPolynomial68_expand 60 A B D
  have heexpand : ee = expand k 60 (cubicEDefectPolynomial68 A C0 E) := by
    simpa only [ee, Ae, Ce, Ee] using
      expand_cubicEDefectPolynomial68 60 A C0 E
  have hgapd : 60 ∣ g - 2 * n :=
    fiveToSix_sixty_dvd_gap_sub_two_n68 n g hn60 hg60 h2n
  have hidx := fiveToSix_terminal_index_d68 n g hwindow
  have hdiv := fiveToSix_terminal_index_d_dvd68 n g hn60 hg60 hwindow
  have hsteps : ∀ r : ℕ,
      60 * r ≤ g - 2 * n →
      d.natDegree ≤ g - 2 * n - 60 * r ∧
        ee.natDegree ≤ g - n - 60 * r := by
    intro r
    induction r with
    | zero =>
        intro _
        exact ⟨hpacket.1, hpacket.2.1⟩
    | succ r ih =>
        intro hroomr
        have hprev := ih (by omega)
        by_cases hr0 : r = 0
        · subst r
          constructor
          · rw [hdexpand, ← hidx.2.2.1]
            refine natDegree_expand_le_sub_next_sixty68
              (secondaryDDefectPolynomial68 A B D) (5 * n - g)
              (7 * n - 2 * g) hdiv.1 (by
                have := hwindow.1
                have := hwindow.2
                omega) ?_ ?_
            · rw [hidx.1, ← hdexpand]
              exact hpacket.1
            · rw [hidx.1, ← hdexpand]
              exact hpacket.2.2.2.1
          · rw [heexpand, ← hidx.2.2.2]
            refine natDegree_expand_le_sub_next_sixty68
              (cubicEDefectPolynomial68 A C0 E) (6 * n - g)
              (7 * n - 2 * g) hdiv.2 (by
                have := hwindow.1
                have := hwindow.2
                omega) ?_ ?_
            · rw [hidx.2.1, ← heexpand]
              exact hpacket.2.1
            · rw [hidx.2.1, ← heexpand]
              exact hpacket.2.2.2.2
        · have htpos : 0 < 60 * r := by omega
          have htle : 60 * r ≤ g - 2 * n := by omega
          have hedge :=
            maximalExpandedIntegratedPolynomialLowerSystem_fiveToSix_beyondWallEdge_offset68
              l alpha beta gamma delta epsilon zeta eta terminal
              A B C0 D E (60 * r) hterminal hsys htpos hwindow hzeta htle
              hprev
          rcases hedge with hvan | hcusp
          · obtain ⟨N, hN⟩ := hn60
            obtain ⟨G, hG⟩ := hg60
            have hnext_d : 60 * r + 60 ≤ g - 2 * n := by
              have : 60 * Nat.succ r = 60 * r + 60 := by
                rw [Nat.succ_eq_add_one, mul_add, mul_one]
              rwa [← this]
            have hnext_e : 60 * r + 60 ≤ g - n :=
              hnext_d.trans
                (Nat.sub_le_sub_left
                  (Nat.le_mul_of_pos_left n (by omega : 0 < 2)) g)
            have hleG : 2 * N + r ≤ G := by
              refine fiveToSix_room_implies_G68 N G r ?_ ?_
              · simpa [hN, hG] using hnext_d
              · simpa [hN, hG] using h2n
            have hdphase : 60 ∣ g - 2 * n - 60 * r :=
              ⟨G - 2 * N - r, by
                rw [hN, hG, fiveToSix_sixty_mul_sub_sub68 N G r hleG]⟩
            have hephase : 60 ∣ g - n - 60 * r :=
              ⟨G - N - r, by
                have hle : N + r ≤ G := by omega
                rw [hN, hG, fiveToSix_sixty_mul_sub_sub_one68 N G r hle]⟩
            constructor
            · rw [hdexpand]
              exact natDegree_expand_le_sub_next_sixty68
                (secondaryDDefectPolynomial68 A B D) (g - 2 * n)
                (60 * r) hdphase hnext_d
                (by simpa only [hdexpand] using hprev.1)
                (by
                  have : d.coeff (g - 2 * n - 60 * r) = 0 := hvan.1
                  simpa [hdexpand] using this)
            · rw [heexpand]
              exact natDegree_expand_le_sub_next_sixty68
                (cubicEDefectPolynomial68 A C0 E) (g - n)
                (60 * r) hephase hnext_e
                (by simpa only [heexpand] using hprev.2)
                (by
                  have : ee.coeff (g - n - 60 * r) = 0 := hvan.2
                  simpa [heexpand] using this)
          · exact False.elim
              (fiveToSix_terminalZero_aligned_cusp_impossible68
                l alpha beta gamma delta epsilon zeta eta terminal
                A B C0 D E (60 * r) hterminal hsys hzeta htle hprev.1
                hprev.2 hcusp)
  have hleft := hsteps ((g - 2 * n) / 60) (Nat.mul_div_le (g - 2 * n) 60)
  have hm : 60 * ((g - 2 * n) / 60) = g - 2 * n :=
    Nat.mul_div_cancel' hgapd
  have hdle : d.natDegree ≤ 0 := by
    have h := hleft.1
    rw [hm] at h
    have : g - 2 * n - (g - 2 * n) = 0 := Nat.sub_self _
    rwa [this] at h
  have hele : ee.natDegree ≤ n := by
    have h := hleft.2
    rw [hm] at h
    have hrew : g - (g - 2 * n) = 2 * n := Nat.sub_sub_self h2n
    have hidx : g - n - (g - 2 * n) = n := by
      have : g - n - (g - 2 * n) = 2 * n - n := by
        rw [Nat.sub_right_comm, hrew]
      rw [this]
      omega
    rwa [hidx] at h
  exact fiveToSix_terminalZero_leftover_constant_d_impossible68
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys hzeta hdle hele

set_option maxHeartbeats 25000000 in
theorem fiveToSix_terminalZero_unconditional_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hpacket :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      let d := secondaryDDefectPolynomial68 Ae Be De
      FiveToSixTerminalZeroPacket68 zeta d ee n g) : False := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  change FiveToSixTerminalZeroPacket68 zeta d ee n g at hpacket
  have hglobal := integratedPolynomialLowerSystem68_global_fiveToSix_residual
    l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  rcases hglobal with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, holdCases⟩
  rcases holdCases with hn60g | hn90 | hn120 | hbig
  · exact fiveToSix_terminalZero_n60_impossible68 l alpha beta gamma delta
      epsilon zeta eta terminal A B C0 D E hterminal hsys hn60g.1 hpacket
  · exact fiveToSix_terminalZero_n90_impossible68 l alpha beta gamma delta
      epsilon zeta eta terminal A B C0 D E hterminal hsys hn90.1
  · exact fiveToSix_terminalZero_n120_impossible68 l alpha beta gamma delta
      epsilon zeta eta terminal A B C0 D E hterminal hsys hn120.1 hpacket
  · have hnbig : 120 < n := hbig
    by_cases hn60 : 60 ∣ n
    · by_cases hg60 : 60 ∣ g
      · exact fiveToSix_terminalZero_aligned_big_impossible68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
          hterminal hsys hpacket hnbig hn60 hg60
      · exact fiveToSix_terminalZero_unaligned_big_impossible68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
          hterminal hsys hpacket hnbig (Or.inr hg60)
    · exact fiveToSix_terminalZero_unaligned_big_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys hpacket hnbig (Or.inl hn60)

set_option maxHeartbeats 25000000 in
theorem integratedPolynomialLowerSystem68_thinResidual_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hres : IntegratedPolynomialLowerSystem68ThinResidual alpha gamma
      epsilon zeta eta terminal A B C0 D E) : False := by
  dsimp only [IntegratedPolynomialLowerSystem68ThinResidual] at hres
  rcases hres with hzero | hvan | hterm
  · exact fiveToSix_terminalZero_unconditional_impossible68 l alpha beta gamma
      delta epsilon zeta eta terminal A B C0 D E hterminal hsys hzero
  · obtain ⟨N, G, S, _, _, hvan'⟩ := hvan
    exact fiveToSix_zetaFirst_B3_equality_support_qZero_vanishingA_open_impossible68
      alpha gamma epsilon zeta eta terminal A B
      (cubicCDefectPolynomial68 A C0)
      (secondaryDDefectPolynomial68 A B D)
      (cubicEDefectPolynomial68 A C0 E) N G S hterminal hvan'
  · exact fiveToSix_largeTerminal_allNonzero_cusp_impossible68 l alpha beta
      gamma delta epsilon zeta eta terminal A B C0 D E hterminal hsys
      hterm

theorem integratedPolynomialLowerSystem68Exclusion_closed :
    IntegratedPolynomialLowerSystem68Exclusion (k := k) := by
  intro l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
    hterminal hsys
  have hopen :=
    integratedPolynomialLowerSystem68_openResidual l alpha beta gamma delta
      epsilon zeta eta terminal A B C0 D E hterminal hsys
  have hthin :=
    integratedPolynomialLowerSystem68OpenResidual_thin alpha gamma epsilon
      zeta eta terminal A B C0 D E hopen
  exact integratedPolynomialLowerSystem68_thinResidual_impossible68 l alpha
    beta gamma delta epsilon zeta eta terminal A B C0 D E hterminal hsys
    hthin

/-- **LEAF CLOSED.** The normalized `(6,8)` low-scale route. -/
theorem proved_planeKellerNormalized68LowScaleRoute :
    PlaneKellerNormalized68LowScaleRoute (K := k) :=
  planeKellerNormalized68LowScaleRoute_of_scaleZeroExclusion_scaleTwo
    integratedPolynomialLowerSystem68Exclusion_closed
    planeKellerNormalized68ScaleTwoRoute_closed

end FiveToSixTerminalZeroMeetingCell68

#print axioms fiveToSix_terminalZero_meetingCell_impossible68
#print axioms fiveToSix_terminalZero_aligned_cusp_impossible68
#print axioms integratedPolynomialLowerSystem68Exclusion_closed
#print axioms proved_planeKellerNormalized68LowScaleRoute

end Max11DegreeRoutes
