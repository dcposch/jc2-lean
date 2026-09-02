import Grok68ScaleTwoDegreeZeroDifferentialBridgeScratch
import LowScale68ScaleTwoAlignedNonsquareEndgame

/-! # Degree-zero primitive on the `(6,8)` aligned-nonsquare quadratic packet

Untracked working note. No tracked file was edited.

Target Prop: `PlaneKeller68AlignedNonsquareQuadraticPacketExclusion`
(`LowScale68ScaleTwoAlignedNonsquareBridge.lean:934`).  Lane item 4 of
`Grok68AlignedSquareTowerPlanScratch.md`.  Parents (tracked, green):
`Grok68ScaleTwoDegreeZeroPrimitiveScratch` (`degreeZeroPrimitive68`,
weight 13) and
`Grok68ScaleTwoDegreeZeroDifferentialBridgeScratch`
(`degreeZeroPrimitive68_deriv_eq_row_of_depressed_rows` and
`degreeZeroPrimitive68_deriv_eq_constant_of_monic_differentialJacobian`
for an arbitrary `Derivation k F F`).

## Step 1 (lands unconditionally)

`NonsquareAlignedSourceCurveData68` carries the same monic depressed
bracket as the square case, with Jacobian
`C (algebraMap j / AdjoinRoot.root (alignedQuadraticPolynomial46 H))`
over `F68 = k(x)(√H)` and `quadraticDerivation46 H`.  Instantiating the
P1 monic bridge on those structure fields gives
`d ρ = j / √H`.

## Step 2 (valuation at infinity)

The linear-root pole tower does not apply: `√H` is ramified at the
roots of `H`, where `(j/√H) dx` is holomorphic.  CAS job
`20260902T123231Z-68-aligned-nonsquare-degree-zero-618409`
(`scripts/derive_68_aligned_nonsquare_degree_zero.py`, command-source
SHA256
`aa17ed3d71c360470b12327c3253e4541c3a60e7b5637bc7a98d14a39c2812ac`):

* After completing the square, `u = y/t` realises
  `(j/y) dx = -du/(u²-c)`; the conventional 2-scaling recovers
  `-2j du/(u²-c)` with residues `±j/√c ≠ 0`.
* Deck-oddness of the weight-13 primitive writes `ρ = Q · √H` with
  `Q ∈ k(x)`, and `dρ = j/√H` is the rational ODE
  `2 H Q' + Q H' = 2j`.
* For `natDegree H = 2` that ODE has no rational solution unless
  `j = 0`: writing `Q = n/d` yields the polynomial identity
  `2 H W + n H' d = 2j d²` with `W = n'd - n d'`, and every degree
  class of `(n,d)` mismatches.

Landed: `d ρ = j/√H` on the packet, deck-oddness of `ρ`, unique
odd descent `ρ = Q · √H`, and `d(√H) = H'/(2 √H)`.  The missing
valuation datum is the transport `d(Q · √H) = j/√H` into the
rational ODE `2 H Q' + Q H' = 2j` and the polynomial degree
comparison of that ODE on quadratic cores (`2 H (n'd - nd') +
n H' d = 2j d²` has no solution for `j ≠ 0` when
`natDegree H = 2`; CAS as above).  The named packet Prop is not
claimed.

No `sorry`, no new axioms, no finite-root shortcut, no closure
overclaim.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

/-! ## Simplified primitive after `L = beta = delta = zeta = 0` -/

section AlignedNonsquarePrimitiveAlgebra68

variable {F : Type*} [Field F] [CharZero F]

/-- The weight-13 primitive on the aligned nonsquare residual tower
(`L = 0`, odd Faber constants already zero). -/
def alignedNonsquareDegreeZeroPrimitive68
    (A B C0 D E alpha gamma epsilon eta : F) : F :=
  degreeZeroPrimitive68 0 A B C0 D E
    (integratedP68 A alpha)
    (integratedQ68 0 A B 0)
    (integratedR68 0 A B C0 alpha gamma)
    (integratedS68 0 A B C0 D alpha 0 0)
    (integratedT68 0 A B C0 D E alpha 0 gamma epsilon)
    (integratedU68 0 A B C0 D E alpha 0 gamma 0 0)
    (integratedV68 0 A B C0 D E alpha 0 gamma 0 epsilon eta)

/-- After the triangular reconstruction, the primitive depends only on
the even/odd sextic letters and the even ground constants
`gamma, epsilon`. -/
theorem alignedNonsquareDegreeZeroPrimitive68_eq_core
    (A B C0 D E alpha gamma epsilon eta : F) :
    alignedNonsquareDegreeZeroPrimitive68 A B C0 D E alpha gamma
        epsilon eta =
      degreeZeroBaseGroup68 0 A B C0 D E +
        gamma * degreeZeroGammaGroup68 A B C0 E +
        epsilon * degreeZeroEpsilonGroup68 A B C0 +
        firstIntegralFour68 0 A B C0 D E 0 gamma 0 epsilon 0 *
          degreeZeroFourGroup68 A C0 +
        firstIntegralThree68 0 A B C0 D E 0 gamma 0 epsilon 0 *
          degreeZeroThreeGroup68 B +
        firstIntegralTwo68 0 A B C0 D E 0 gamma 0 epsilon 0 *
          degreeZeroTwoGroup68 A := by
  have hres := integratedResiduals68 0 A B C0 D E alpha 0 gamma 0
    epsilon 0 eta
  rcases hres with ⟨_hα, hβ, hγ, hδ, hε, hζ, _hη⟩
  simp only [alignedNonsquareDegreeZeroPrimitive68, degreeZeroPrimitive68]
  rw [hβ, hγ, hδ, hε, hζ]
  simp [zero_mul, add_zero]

set_option maxHeartbeats 4000000 in
/-- The unused `z²` first integral is deck-odd on the aligned
nonsquare parity locus. -/
theorem firstIntegralTwo68_alignedDeckOdd
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (H : k[X]) [NonsquarePolynomial46 H]
    (A B C0 D E gamma epsilon :
      AdjoinRoot (alignedQuadraticPolynomial46 H))
    (hA : alignedQuadraticDeck46 H A = A)
    (hB : alignedQuadraticDeck46 H B = -B)
    (hC : alignedQuadraticDeck46 H C0 = C0)
    (hD : alignedQuadraticDeck46 H D = -D)
    (hE : alignedQuadraticDeck46 H E = E)
    (hgamma : alignedQuadraticDeck46 H gamma = gamma)
    (hepsilon : alignedQuadraticDeck46 H epsilon = epsilon) :
    alignedQuadraticDeck46 H
        (firstIntegralTwo68 0 A B C0 D E 0 gamma 0 epsilon 0) =
      - firstIntegralTwo68 0 A B C0 D E 0 gamma 0 epsilon 0 := by
  simp only [firstIntegralTwo68, map_add, map_sub, map_neg, map_mul,
    map_pow, map_div₀, map_ofNat, map_zero, hA, hB, hC, hD, hE,
    hgamma, hepsilon]
  ring

set_option maxHeartbeats 4000000 in
/-- The `z³` first integral is deck-even on the same locus (weight 10). -/
theorem firstIntegralThree68_alignedDeckEven
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (H : k[X]) [NonsquarePolynomial46 H]
    (A B C0 D E gamma epsilon :
      AdjoinRoot (alignedQuadraticPolynomial46 H))
    (hA : alignedQuadraticDeck46 H A = A)
    (hB : alignedQuadraticDeck46 H B = -B)
    (hC : alignedQuadraticDeck46 H C0 = C0)
    (hD : alignedQuadraticDeck46 H D = -D)
    (hE : alignedQuadraticDeck46 H E = E)
    (hgamma : alignedQuadraticDeck46 H gamma = gamma)
    (hepsilon : alignedQuadraticDeck46 H epsilon = epsilon) :
    alignedQuadraticDeck46 H
        (firstIntegralThree68 0 A B C0 D E 0 gamma 0 epsilon 0) =
      firstIntegralThree68 0 A B C0 D E 0 gamma 0 epsilon 0 := by
  simp only [firstIntegralThree68, map_add, map_sub, map_neg, map_mul,
    map_pow, map_div₀, map_ofNat, map_zero, hA, hB, hC, hD, hE,
    hgamma, hepsilon]
  ring

set_option maxHeartbeats 4000000 in
/-- The weight-13 base group is deck-odd after `L = 0`. -/
theorem degreeZeroBaseGroup68_alignedDeckOdd
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (H : k[X]) [NonsquarePolynomial46 H]
    (A B C0 D E : AdjoinRoot (alignedQuadraticPolynomial46 H))
    (hA : alignedQuadraticDeck46 H A = A)
    (hB : alignedQuadraticDeck46 H B = -B)
    (hC : alignedQuadraticDeck46 H C0 = C0)
    (hD : alignedQuadraticDeck46 H D = -D)
    (hE : alignedQuadraticDeck46 H E = E) :
    alignedQuadraticDeck46 H (degreeZeroBaseGroup68 0 A B C0 D E) =
      - degreeZeroBaseGroup68 0 A B C0 D E := by
  simp only [degreeZeroBaseGroup68, map_add, map_sub, map_neg, map_mul,
    map_pow, map_div₀, map_ofNat, map_zero, hA, hB, hC, hD, hE]
  ring

theorem degreeZeroGammaGroup68_alignedDeckOdd
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (H : k[X]) [NonsquarePolynomial46 H]
    (A B C0 E : AdjoinRoot (alignedQuadraticPolynomial46 H))
    (hA : alignedQuadraticDeck46 H A = A)
    (hB : alignedQuadraticDeck46 H B = -B)
    (hC : alignedQuadraticDeck46 H C0 = C0)
    (hE : alignedQuadraticDeck46 H E = E) :
    alignedQuadraticDeck46 H (degreeZeroGammaGroup68 A B C0 E) =
      - degreeZeroGammaGroup68 A B C0 E := by
  simp only [degreeZeroGammaGroup68, map_add, map_sub, map_neg, map_mul,
    map_pow, map_div₀, map_ofNat, hA, hB, hC, hE]
  ring

theorem degreeZeroEpsilonGroup68_alignedDeckOdd
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (H : k[X]) [NonsquarePolynomial46 H]
    (A B C0 : AdjoinRoot (alignedQuadraticPolynomial46 H))
    (hA : alignedQuadraticDeck46 H A = A)
    (hB : alignedQuadraticDeck46 H B = -B)
    (hC : alignedQuadraticDeck46 H C0 = C0) :
    alignedQuadraticDeck46 H (degreeZeroEpsilonGroup68 A B C0) =
      - degreeZeroEpsilonGroup68 A B C0 := by
  simp only [degreeZeroEpsilonGroup68, map_add, map_sub, map_neg, map_mul,
    map_pow, map_div₀, map_ofNat, hA, hB, hC]
  ring

theorem degreeZeroFourGroup68_alignedDeckEven
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (H : k[X]) [NonsquarePolynomial46 H]
    (A C0 : AdjoinRoot (alignedQuadraticPolynomial46 H))
    (hA : alignedQuadraticDeck46 H A = A)
    (hC : alignedQuadraticDeck46 H C0 = C0) :
    alignedQuadraticDeck46 H (degreeZeroFourGroup68 A C0) =
      degreeZeroFourGroup68 A C0 := by
  simp only [degreeZeroFourGroup68, map_add, map_sub, map_mul, map_pow,
    map_div₀, map_ofNat, hA, hC]

theorem degreeZeroThreeGroup68_alignedDeckOdd
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (H : k[X]) [NonsquarePolynomial46 H]
    (B : AdjoinRoot (alignedQuadraticPolynomial46 H))
    (hB : alignedQuadraticDeck46 H B = -B) :
    alignedQuadraticDeck46 H (degreeZeroThreeGroup68 B) =
      - degreeZeroThreeGroup68 B := by
  simp only [degreeZeroThreeGroup68, map_neg, map_div₀, map_ofNat, hB]
  ring

theorem degreeZeroTwoGroup68_alignedDeckEven
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (H : k[X]) [NonsquarePolynomial46 H]
    (A : AdjoinRoot (alignedQuadraticPolynomial46 H))
    (hA : alignedQuadraticDeck46 H A = A) :
    alignedQuadraticDeck46 H (degreeZeroTwoGroup68 A) =
      degreeZeroTwoGroup68 A := by
  simp only [degreeZeroTwoGroup68, map_neg, map_div₀, map_ofNat, hA]

end AlignedNonsquarePrimitiveAlgebra68

/-! ## Quadratic field: derivative, odd descent, ODE -/

section AlignedNonsquarePrimitiveField68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

local notation "F68" => AdjoinRoot (alignedQuadraticPolynomial46 H)

local instance quadraticPrimitiveCharZero68 : CharZero F68 :=
  charZero_of_injective_ringHom (algebraMap (RatFunc k) F68).injective

/-- Source-facing weight-13 primitive of an aligned nonsquare packet. -/
def NonsquareAlignedSourceCurveData68.degreeZeroPrimitive
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) : F68 :=
  alignedNonsquareDegreeZeroPrimitive68 S.A S.B S.C0 S.D S.E
    (algebraMap k F68 S.alpha) (algebraMap k F68 S.gamma)
    (algebraMap k F68 S.epsilon) (algebraMap k F68 S.eta)

/-- Step 1: the P1 monic bridge realises `d ρ = j / √H`. -/
theorem NonsquareAlignedSourceCurveData68.degreeZeroPrimitive_deriv
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    quadraticDerivation46 H S.degreeZeroPrimitive =
      algebraMap k F68 j /
        AdjoinRoot.root (alignedQuadraticPolynomial46 H) := by
  have hL : quadraticDerivation46 H (0 : F68) = 0 := by
    simp [quadraticDerivation46_apply]
  simpa [NonsquareAlignedSourceCurveData68.degreeZeroPrimitive,
    alignedNonsquareDegreeZeroPrimitive68] using
    degreeZeroPrimitive68_deriv_eq_constant_of_monic_differentialJacobian
      (quadraticDerivation46 H) 0 S.A S.B S.C0 S.D S.E
      (integratedP68 S.A (algebraMap k F68 S.alpha))
      (integratedQ68 0 S.A S.B 0)
      (integratedR68 0 S.A S.B S.C0 (algebraMap k F68 S.alpha)
        (algebraMap k F68 S.gamma))
      (integratedS68 0 S.A S.B S.C0 S.D (algebraMap k F68 S.alpha) 0 0)
      (integratedT68 0 S.A S.B S.C0 S.D S.E (algebraMap k F68 S.alpha) 0
        (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon))
      (integratedU68 0 S.A S.B S.C0 S.D S.E (algebraMap k F68 S.alpha) 0
        (algebraMap k F68 S.gamma) 0 0)
      (integratedV68 0 S.A S.B S.C0 S.D S.E (algebraMap k F68 S.alpha) 0
        (algebraMap k F68 S.gamma) 0 (algebraMap k F68 S.epsilon)
        (algebraMap k F68 S.eta))
      (algebraMap k F68 j /
        AdjoinRoot.root (alignedQuadraticPolynomial46 H))
      hL S.bracket_eq

/-- A nonsquare polynomial is nonzero. -/
theorem H_ne_zero_of_nonsquare_core68 : H ≠ 0 := by
  intro hzero
  exact NonsquarePolynomial46.not_sq (H := H) (0 : k[X]) (by simp [hzero])

/-- The adjoined square root is nonzero. -/
theorem alignedQuadraticRoot_ne_zero68 :
    AdjoinRoot.root (alignedQuadraticPolynomial46 H) ≠ 0 := by
  intro hz
  have hsq := alignedQuadraticRoot_sq46 H
  have hH : algebraMap k[X] F68 H = 0 := by
    rw [IsScalarTower.algebraMap_apply k[X] (RatFunc k) F68, ← hsq, hz]
    simp
  have hphi : Function.Injective (algebraMap k[X] F68) :=
    alignedQuadraticPolynomialMap_injective46 H
      NonsquarePolynomial46.not_sq
  exact H_ne_zero_of_nonsquare_core68 (H := H)
    (hphi (hH.trans (map_zero _).symm))

/-- Every quadratic-field element is `c₀ + c₁ √H` with `cᵢ ∈ k(x)`. -/
theorem alignedQuadratic_eq_add_mul_root68 (z : F68) :
    ∃ c0 c1 : RatFunc k,
      z = algebraMap (RatFunc k) F68 c0 +
        algebraMap (RatFunc k) F68 c1 *
          AdjoinRoot.root (alignedQuadraticPolynomial46 H) := by
  let pb := AdjoinRoot.powerBasis'
    (alignedQuadraticPolynomial46_monic H)
  have hdim : pb.dim = 2 := by
    change (alignedQuadraticPolynomial46 H).natDegree = 2
    exact alignedQuadraticPolynomial46_natDegree H
  let B : Module.Basis (Fin 2) (RatFunc k) F68 :=
    pb.basis.reindex (finCongr hdim)
  let c0 : RatFunc k := B.repr z 0
  let c1 : RatFunc k := B.repr z 1
  have hB0 : B (0 : Fin 2) = 1 := by
    simp [B, pb]
  have hB1 : B (1 : Fin 2) =
      AdjoinRoot.root (alignedQuadraticPolynomial46 H) := by
    simp [B, pb]
  refine ⟨c0, c1, ?_⟩
  have hsum := B.sum_repr z
  rw [Fin.sum_univ_two, hB0, hB1] at hsum
  simpa [c0, c1, Algebra.smul_def] using hsum.symm

/-- Deck-odd elements are purely odd: `z = c √H`. -/
theorem alignedQuadratic_odd_eq_mul_root68 (z : F68)
    (hz : alignedQuadraticDeck46 H z = -z) :
    ∃ c : RatFunc k,
      z = algebraMap (RatFunc k) F68 c *
        AdjoinRoot.root (alignedQuadraticPolynomial46 H) := by
  obtain ⟨c0, c1, hrep⟩ := alignedQuadratic_eq_add_mul_root68 (H := H) z
  have hdeck := congrArg (alignedQuadraticDeck46 H) hrep
  simp only [map_add, map_mul, alignedQuadraticDeck46_base,
    alignedQuadraticDeck46_root] at hdeck
  rw [hz] at hdeck
  have hdeck' : -z =
      algebraMap (RatFunc k) F68 c0 -
        algebraMap (RatFunc k) F68 c1 *
          AdjoinRoot.root (alignedQuadraticPolynomial46 H) := by
    linear_combination hdeck
  have h2 : (2 : F68) * algebraMap (RatFunc k) F68 c0 = 0 := by
    have hsum := congrArg₂ HAdd.hAdd hrep hdeck'
    ring_nf at hsum
    simpa [mul_comm] using hsum.symm
  have hc0F : algebraMap (RatFunc k) F68 c0 = 0 :=
    (mul_eq_zero.mp h2).resolve_left (by norm_num)
  have hc0 : c0 = 0 :=
    (algebraMap (RatFunc k) F68).injective
      (hc0F.trans (map_zero _).symm)
  refine ⟨c1, ?_⟩
  simp [hrep, hc0]

/-- Ordinary derivative of the adjoined square root. -/
theorem quadraticDerivation46_root68 :
    quadraticDerivation46 H
        (AdjoinRoot.root (alignedQuadraticPolynomial46 H)) =
      algebraMap (RatFunc k) F68
          (algebraMap k[X] (RatFunc k) H.derivative) /
        (2 * AdjoinRoot.root (alignedQuadraticPolynomial46 H)) := by
  set rt := AdjoinRoot.root (alignedQuadraticPolynomial46 H)
  have hrt : rt ≠ 0 := alignedQuadraticRoot_ne_zero68 (H := H)
  have hsq := alignedQuadraticRoot_sq46 H
  have hleft :
      quadraticDerivation46 H (rt ^ 2) =
        (2 : F68) * rt * quadraticDerivation46 H rt := by
    simp only [quadraticDerivation46_apply, pow_two, Derivation.leibniz,
      smul_eq_mul]
    ring
  have hright :
      quadraticDerivation46 H
          (algebraMap (RatFunc k) F68
            (algebraMap k[X] (RatFunc k) H)) =
        algebraMap (RatFunc k) F68
          (algebraMap k[X] (RatFunc k) H.derivative) := by
    rw [quadraticDerivation46_algebraMap_ratFunc68, GCD369RatFuncDerivative]
  have hmul :
      (2 : F68) * rt * quadraticDerivation46 H rt =
        algebraMap (RatFunc k) F68
          (algebraMap k[X] (RatFunc k) H.derivative) := by
    rw [← hleft, hsq, hright]
  have hne : (2 : F68) * rt ≠ 0 :=
    mul_ne_zero (by norm_num) hrt
  field_simp [hne]
  linear_combination hmul

set_option maxHeartbeats 8000000 in
/-- The aligned nonsquare primitive is deck-odd. -/
theorem NonsquareAlignedSourceCurveData68.degreeZeroPrimitive_odd
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    alignedQuadraticDeck46 H S.degreeZeroPrimitive =
      - S.degreeZeroPrimitive := by
  have hγ : alignedQuadraticDeck46 H (algebraMap k F68 S.gamma) =
      algebraMap k F68 S.gamma := alignedQuadraticDeck46_ground H S.gamma
  have hε : alignedQuadraticDeck46 H (algebraMap k F68 S.epsilon) =
      algebraMap k F68 S.epsilon :=
    alignedQuadraticDeck46_ground H S.epsilon
  have hcore := alignedNonsquareDegreeZeroPrimitive68_eq_core S.A S.B
    S.C0 S.D S.E (algebraMap k F68 S.alpha)
    (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon)
    (algebraMap k F68 S.eta)
  have hbase := degreeZeroBaseGroup68_alignedDeckOdd H S.A S.B S.C0 S.D
    S.E S.A_even S.B_odd S.C_even S.D_odd S.E_even
  have hg := degreeZeroGammaGroup68_alignedDeckOdd H S.A S.B S.C0 S.E
    S.A_even S.B_odd S.C_even S.E_even
  have he := degreeZeroEpsilonGroup68_alignedDeckOdd H S.A S.B S.C0
    S.A_even S.B_odd S.C_even
  have h4 := degreeZeroFourGroup68_alignedDeckEven H S.A S.C0 S.A_even
    S.C_even
  have h3 := degreeZeroThreeGroup68_alignedDeckOdd H S.B S.B_odd
  have h2 := degreeZeroTwoGroup68_alignedDeckEven H S.A S.A_even
  have hI4 := firstIntegralFour68_alignedDeckOdd H S.A S.B S.C0 S.D S.E
    (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon)
    S.A_even S.B_odd S.C_even S.D_odd S.E_even hγ hε
  have hI3 := firstIntegralThree68_alignedDeckEven H S.A S.B S.C0 S.D S.E
    (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon)
    S.A_even S.B_odd S.C_even S.D_odd S.E_even hγ hε
  have hI2 := firstIntegralTwo68_alignedDeckOdd H S.A S.B S.C0 S.D S.E
    (algebraMap k F68 S.gamma) (algebraMap k F68 S.epsilon)
    S.A_even S.B_odd S.C_even S.D_odd S.E_even hγ hε
  simp only [NonsquareAlignedSourceCurveData68.degreeZeroPrimitive]
  rw [hcore, map_add, map_add, map_add, map_add, map_add, map_mul,
    map_mul, map_mul, map_mul, map_mul, hbase, hg, he, h4, h3, h2, hI4,
    hI3, hI2, hγ, hε]
  ring

/-- Odd descent: `ρ = Q · √H` for a unique `Q ∈ k(x)`. -/
theorem NonsquareAlignedSourceCurveData68.degreeZeroPrimitive_eq_mul_root
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j) :
    ∃ Q : RatFunc k,
      S.degreeZeroPrimitive =
        algebraMap (RatFunc k) F68 Q *
          AdjoinRoot.root (alignedQuadraticPolynomial46 H) :=
  alignedQuadratic_odd_eq_mul_root68 (H := H) S.degreeZeroPrimitive
    (S.degreeZeroPrimitive_odd (H := H))

end AlignedNonsquarePrimitiveField68

/-! ## Residual

Landed: `d ρ = j/√H`, deck-oddness of the weight-13 primitive, and
unique odd descent `ρ = Q · √H` with `Q ∈ k(x)`.  Also landed:
`d(√H) = H'/(2 √H)`.

The missing valuation datum is the transport of `d(Q · √H) = j/√H`
into the rational ODE `2 H Q' + Q H' = 2j` and the polynomial
degree comparison of that ODE on quadratic cores.  CAS job
`20260902T123231Z-68-aligned-nonsquare-degree-zero-618409` shows
that writing `Q = n/d` yields
`2 H (n'd - n d') + n H' d = 2 j d²`, which has no solution for
`j ≠ 0` when `natDegree H = 2`.  The named packet Prop is not
claimed.
-/

#print axioms NonsquareAlignedSourceCurveData68.degreeZeroPrimitive_deriv
#print axioms NonsquareAlignedSourceCurveData68.degreeZeroPrimitive_odd
#print axioms NonsquareAlignedSourceCurveData68.degreeZeroPrimitive_eq_mul_root
#print axioms quadraticDerivation46_root68
#print axioms alignedQuadratic_odd_eq_mul_root68

end Max11DegreeRoutes
