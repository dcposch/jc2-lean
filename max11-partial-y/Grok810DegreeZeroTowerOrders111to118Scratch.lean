import Grok810DegreeZeroTowerOrders103to110Scratch

/-! # Orders `111` through `118` and the ceiling of the `(8,10)` degree-zero
bounded tower

Untracked working note.  No tracked file was edited.

`Grok810DegreeZeroTowerOrders103to110Scratch` peeled orders `103`–`110`
on the order-`102` quotient `Head + h · Plus`, leaving remaining pole
`9 = 119 - 110`.  The clearing identity `hclear` and the simple-pole
derivative `hderiv` remain hypotheses; a parallel lane
(`Grok810DegreeZeroClearingDischargeScratch`) discharges the remaining-`17`
clearing.  This file keeps those hypotheses exactly as the parent does.

Each order `k ∈ {111,…,118}` is the `h^{k-102}` coefficient of the
cleared numerator quotient, equivalently the `h^{k-111}` coefficient
of `degreeZeroOrder110Plus810`.  Vanishing of a remaining numerator
that evaluates to that named coefficient is recorded by
`degreeZeroOrder{k}810_zero_of_remaining_pole`.  The batch
`h₀`-divisibility
`degreeZero_orders111to118_remaining_dvd810` peels eight remaining
numerators from the pole-`9` quotient, leaving remaining pole `1`.

At the ceiling the last linear factor cancels: `h₀^{17}` divides the
specialised jet and the leftover numerator *is* `rho`.  Cancel-and-expose
with the simple pole `rho' = C j / h₀` and `j ≠ 0` is False, recorded by
`degreeZeroFace810_linearRoot_order118Ceiling` on the parent
`hclear` / `hderiv` / `hj` hypotheses.  The generic induction
`degreeZero_pow_dvd_of_remaining_pole810` is the same holomorphic
remainder used by `alignedSquareFace610_order75Grandchildren`.  The
source-facing identity identifying the jet with a clearing of the
grouped primitive is not re-proved here, so the chamber is not closed
on the raw source hypotheses.  There is no unused compact-numerator
order after `118`.  The jet has a single specialised limb.

CAS: `derive_810_degree_zero_tower_orders111to118.py` /
`emit_810_degree_zero_tower_orders111to118_lean.py`.  No `sorry`, no new
axioms, no finite-root shortcut, no closure overclaim.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option maxHeartbeats 1600000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Bookkeeping: ceiling order `118`, remaining pole `0` -/

/-- Last compact-numerator order of the `(8,10)` degree-zero tower. -/
def degreeZeroTowerCeilingLastOrder810 : ℕ := 118

/-- Vanishing multiplicity of the specialised jet through the ceiling:
orders `102` through `117` plus the holomorphic remainder, i.e. `h₀^{17}`. -/
def degreeZeroTowerCeilingDivisibility810 : ℕ := 17

/-- Remaining pole of the order-`102` quotient after orders `111`–`118`:
`9 - 8 = 1`, equivalently `119 - 118`. -/
def degreeZeroRemainingPoleAfter118810 : ℕ := 1

/-- Remaining pole after the ceiling order. -/
def degreeZeroRemainingPoleAfterCeiling810 : ℕ := 0

/-- Vanishing multiplicity recorded by this batch on the order-`110`
remaining numerator: eight remaining-numerator peels. -/
def degreeZeroTowerBatch111to118Divisibility810 : ℕ := 8

/-- Cumulative `h₀`-divisibility of the order-`102` quotient through
order `118`, before the holomorphic remainder. -/
def degreeZeroTowerDivisibilityAfter118810 : ℕ := 16

theorem degreeZeroTowerCeilingLastOrder810_eq :
    degreeZeroTowerCeilingLastOrder810 = 118 :=
  rfl

theorem degreeZeroTowerCeilingDivisibility810_eq :
    degreeZeroTowerCeilingDivisibility810 = 17 :=
  rfl

theorem degreeZeroRemainingPoleAfter118810_eq :
    degreeZeroRemainingPoleAfter118810 = 1 :=
  rfl

theorem degreeZeroRemainingPoleAfterCeiling810_eq :
    degreeZeroRemainingPoleAfterCeiling810 = 0 :=
  rfl

theorem degreeZeroTowerBatch111to118Divisibility810_eq :
    degreeZeroTowerBatch111to118Divisibility810 = 8 :=
  rfl

theorem degreeZeroTowerDivisibilityAfter118810_eq :
    degreeZeroTowerDivisibilityAfter118810 = 16 :=
  rfl

theorem degreeZeroTowerCeilingLastOrder810_eq_ceiling :
    degreeZeroTowerCeilingLastOrder810 = degreeZeroTowerCeiling810 :=
  rfl

theorem degreeZeroTowerCeilingDivisibility810_eq_length :
    degreeZeroTowerCeilingDivisibility810 =
      degreeZeroEffectiveTowerLength810 :=
  rfl

theorem degreeZeroRemainingPoleAfter118810_eq_sub_clearing :
    degreeZeroRemainingPoleAfter118810 =
      degreeZeroSourceClearingPower810 -
        degreeZeroTowerCeilingLastOrder810 :=
  rfl

theorem degreeZeroRemainingPoleAfter118810_eq_one :
    degreeZeroRemainingPoleAfter118810 = degreeZeroPoleOrder810 :=
  rfl

theorem degreeZeroTowerDivisibilityAfter118810_eq_add :
    degreeZeroTowerDivisibilityAfter118810 =
      degreeZeroTowerBatchDivisibility810 +
        degreeZeroTowerBatch111to118Divisibility810 :=
  rfl

theorem degreeZeroTowerCeilingDivisibility810_eq_succ :
    degreeZeroTowerCeilingDivisibility810 =
      degreeZeroTowerDivisibilityAfter118810 +
        degreeZeroRemainingPoleAfter118810 :=
  rfl

#print axioms degreeZeroTowerCeilingLastOrder810_eq_ceiling
#print axioms degreeZeroTowerCeilingDivisibility810_eq_length
#print axioms degreeZeroRemainingPoleAfter118810_eq_sub_clearing

/-! ## Holomorphic remainder (remaining pole `0`) -/

section DegreeZeroPoleZero810

variable {k : Type*} [Field k] [CharZero k]

/-- Cancel every polynomial power from a pole-`n` clearing.  The
remaining factor *is* `rho`. -/
theorem degreeZero_algebraMap_cancel_all_clearing810
    (h0 Q : k[X]) (rho : RatFunc k) (n : ℕ) (hh0 : h0 ≠ 0)
    (hquot :
      algebraMap k[X] (RatFunc k) (h0 ^ n * Q) =
        (algebraMap k[X] (RatFunc k) h0) ^ n * rho) :
    algebraMap k[X] (RatFunc k) Q = rho := by
  simpa [pow_zero, one_mul] using
    degreeZero_algebraMap_cancel_pow810 h0 Q rho n 0 hh0
      (by simpa [add_zero] using hquot)

/-- Cancel-and-expose: if `h0^n` divides the cleared numerator, the
remaining factor *is* `rho`, so the simple-pole equation forces `j = 0`. -/
theorem degreeZero_of_pow_dvd_simplePole_eval810
    (a j : k) (h0 A0 Q : k[X]) (rho : RatFunc k) (n : ℕ)
    (hh0 : h0 ≠ 0) (hroot : h0.eval a = 0) (hA : A0 = h0 ^ n * Q)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ n * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    j = 0 :=
  localLinearPoleZero_C_eq_zero_of_deriv_eq_simplePole810 a j h0 Q rho
    hh0 hroot
    (degreeZero_algebraMap_cancel_all_clearing810 h0 Q rho n hh0
      (by simpa [hA] using hclear))
    hderiv

/-- Same holomorphic remainder, with `j ≠ 0`, is False. -/
theorem degreeZero_of_pow_dvd_simplePole_ne_zero810
    (a j : k) (h0 A0 Q : k[X]) (rho : RatFunc k) (n : ℕ)
    (hh0 : h0 ≠ 0) (hroot : h0.eval a = 0) (hA : A0 = h0 ^ n * Q)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ n * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) : False :=
  hj (degreeZero_of_pow_dvd_simplePole_eval810 a j h0 A0 Q rho n hh0
    hroot hA hclear hderiv)

/-- Successive remaining-numerator peels: a pole-`n` numerator of a
simple-pole rational function is divisible by `h₀^n`.  Each successor
step is the parent head obstruction plus one linear cancellation; the
`n = 0` remainder is the holomorphic case. -/
theorem degreeZero_pow_dvd_of_remaining_pole810
    (h0 Q : k[X]) (rho : RatFunc k) (j a : k) (n : ℕ)
    (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) Q =
      (algebraMap k[X] (RatFunc k) h0) ^ n * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    h0 ^ n ∣ Q := by
  induction n generalizing Q with
  | zero =>
    refine ⟨Q, ?_⟩
    simp
  | succ n ih =>
    have hQ0 : Q.eval a = 0 :=
      localLinearPole_head_eval_zero_of_deriv_eq_simplePole810 (n + 1)
        (Nat.succ_ne_zero n) a j h0 Q rho hdegree hroot
        (by simpa [Nat.succ_eq_add_one] using hclear) hderiv
    obtain ⟨Qnew, hfact⟩ :=
      degreeZero_linearPolynomial_dvd_of_eval_eq_zero810 h0 Q a
        hdegree hroot hQ0
    have hclear' :
        algebraMap k[X] (RatFunc k) Qnew =
          (algebraMap k[X] (RatFunc k) h0) ^ n * rho :=
      degreeZero_algebraMap_cancel_one_clearing810 h0 Q Qnew rho n
        hh0 hfact
        (by simpa [Nat.succ_eq_add_one, add_comm n 1] using hclear)
    obtain ⟨R, hR⟩ := ih Qnew hclear'
    refine ⟨R, ?_⟩
    calc
      Q = h0 * Qnew := hfact
      _ = h0 * (h0 ^ n * R) := by rw [hR]
      _ = h0 ^ (n + 1) * R := by ring

#print axioms degreeZero_algebraMap_cancel_all_clearing810
#print axioms degreeZero_of_pow_dvd_simplePole_eval810
#print axioms degreeZero_of_pow_dvd_simplePole_ne_zero810
#print axioms degreeZero_pow_dvd_of_remaining_pole810

end DegreeZeroPoleZero810

/-! ## Order `111` (quotient `h^9`, order-`110` Plus `h^0`) -/

/-- Order-`111` contribution of order-`110` Plus block `0`. -/
def degreeZeroOrder111Block0_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (729583139634020352 : R) * a4 ^ 2 * a0 * lambda
    - (1459166279268040704 : R) * a4 * a3 * a1 * lambda
    - (729583139634020352 : R) * a4 * a2 ^ 2 * lambda
    - (729583139634020352 : R) * a3 ^ 2 * a2 * lambda

/-- Order-`111` contribution of order-`110` Plus block `1`. -/
def degreeZeroOrder111Block1_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (3100728343444586496 : R) * t0 * u1 * a4 * a0 * lambda
    + (3100728343444586496 : R) * t0 * u1 * a3 * a1 * lambda
    + (1550364171722293248 : R) * t0 * u1 * a2 ^ 2 * lambda
    + (1550364171722293248 : R) * v1 ^ 2 * a4 * a0 * lambda
    + (1550364171722293248 : R) * v1 ^ 2 * a3 * a1 * lambda
    + (775182085861146624 : R) * v1 ^ 2 * a2 ^ 2 * lambda
    + (1550364171722293248 : R) * v1 * u1 ^ 2 * a0 * lambda

/-- Order-`111` contribution of order-`110` Plus block `2`. -/
def degreeZeroOrder111Block2_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`111` contribution of order-`110` Plus block `3`. -/
def degreeZeroOrder111Block3_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`111` contribution of order-`110` Plus block `4`. -/
def degreeZeroOrder111Block4_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (4844888036632166400 : R) * t0 ^ 2 * v1 * a4 * a0 * lambda
    - (4844888036632166400 : R) * t0 ^ 2 * v1 * a3 * a1 * lambda
    - (2422444018316083200 : R) * t0 ^ 2 * v1 * a2 ^ 2 * lambda
    - (2422444018316083200 : R) * t0 ^ 2 * u1 ^ 2 * a0 * lambda

/-- Order-`111` contribution of order-`110` Plus block `5`. -/
def degreeZeroOrder111Block5_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (4844888036632166400 : R) * t0 * v1 ^ 2 * u1 * a0 * lambda
    - (403740669719347200 : R) * v1 ^ 4 * a0 * lambda

/-- Order-`111` contribution of order-`110` Plus block `6`. -/
def degreeZeroOrder111Block6_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`111` contribution of order-`110` Plus block `7`. -/
def degreeZeroOrder111Block7_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`111` contribution of order-`110` Plus block `8`. -/
def degreeZeroOrder111Block8_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (1665430262592307200 : R) * t0 ^ 4 * a4 * a0 * lambda
    + (1665430262592307200 : R) * t0 ^ 4 * a3 * a1 * lambda

/-- Order-`111` contribution of order-`110` Plus block `9`. -/
def degreeZeroOrder111Block9_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (832715131296153600 : R) * t0 ^ 4 * a2 ^ 2 * lambda
    + (6661721050369228800 : R) * t0 ^ 3 * v1 * u1 * a0 * lambda
    + (3330860525184614400 : R) * t0 ^ 2 * v1 ^ 3 * a0 * lambda

/-- Order-`111` contribution of order-`110` Plus block `10`. -/
def degreeZeroOrder111Block10_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`111` contribution of order-`110` Plus block `11`. -/
def degreeZeroOrder111Block11_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`111` contribution of order-`110` Plus block `12`. -/
def degreeZeroOrder111Block12_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`111` contribution of order-`110` Plus block `13`. -/
def degreeZeroOrder111Block13_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1707066019157114880 : R) * t0 ^ 5 * u1 * a0 * lambda
    - (4267665047892787200 : R) * t0 ^ 4 * v1 ^ 2 * a0 * lambda

/-- Order-`111` contribution of order-`110` Plus block `14`. -/
def degreeZeroOrder111Block14_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`111` contribution of order-`110` Plus block `15`. -/
def degreeZeroOrder111Block15_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`111` contribution of order-`110` Plus block `16`. -/
def degreeZeroOrder111Block16_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (1742629894556221440 : R) * t0 ^ 6 * v1 * a0 * lambda

/-- Order-`111` contribution of order-`110` Plus block `17`. -/
def degreeZeroOrder111Block17_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`111` contribution of order-`110` Plus block `18`. -/
def degreeZeroOrder111Block18_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`111` contribution of order-`110` Plus block `19`. -/
def degreeZeroOrder111Block19_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (221718535691304960 : R) * t0 ^ 8 * a0 * lambda

/-- Order-`111` contribution of order-`110` Plus block `20`. -/
def degreeZeroOrder111Block20_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`111` contribution of order-`110` Plus block `21`. -/
def degreeZeroOrder111Block21_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`111` contribution of order-`110` Plus block `22`. -/
def degreeZeroOrder111Block22_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`111` contribution of order-`110` Plus block `23`. -/
def degreeZeroOrder111Block23_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`111` contribution of order-`110` Plus block `24`. -/
def degreeZeroOrder111Block24_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Frozen order-`111` coefficient of the cleared numerator
quotient (`h^9` of `degreeZeroSourceJetQuotient810`,
`h^0` of `degreeZeroOrder110Plus810`). -/
def degreeZeroOrder111810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
  degreeZeroOrder111Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder111Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder111Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder111Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder111Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder111Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder111Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder111Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder111Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder111Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder111Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder111Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder111Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder111Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder111Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder111Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder111Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder111Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder111Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder111Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder111Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder111Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder111Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder111Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder111Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda

/-! ## Order `112` (quotient `h^10`, order-`110` Plus `h^1`) -/

set_option maxHeartbeats 200000000 in
/-- Order-`112` contribution of order-`110` Plus block `0`. -/
def degreeZeroOrder112Block0_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (576460752303423488 : R) * u1 * a3 * b1
    - (1152921504606846976 : R) * u1 * a2 * b2
    - (1729382256910270464 : R) * u1 * a1 * b3
    - (2305843009213693952 : R) * u1 * a0 * b4
    + (6485183463413514240 : R) * a4 * a3 * a0
    + (6485183463413514240 : R) * a4 * a2 * a1
    + (3242591731706757120 : R) * a3 ^ 2 * a1
    + (3242591731706757120 : R) * a3 * a2 ^ 2
    - (3458764513820540928 : R) * a3 * a0 * b62
    - (3458764513820540928 : R) * a2 * a1 * b62

/-- Order-`112` contribution of order-`110` Plus block `1`. -/
def degreeZeroOrder112Block1_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (6485183463413514240 : R) * t0 * u1 * a3 * a0
    - (6485183463413514240 : R) * t0 * u1 * a2 * a1
    - (6890507429876858880 : R) * v1 ^ 2 * a3 * a0
    - (6890507429876858880 : R) * v1 ^ 2 * a2 * a1

/-- Order-`112` contribution of order-`110` Plus block `2`. -/
def degreeZeroOrder112Block2_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (648518346341351424 : R) * t0 * v1 * a3 * b1
    + (1297036692682702848 : R) * t0 * v1 * a2 * b2
    + (1945555039024054272 : R) * t0 * v1 * a1 * b3
    + (2594073385365405696 : R) * t0 * v1 * a0 * b4
    + (4539628424389459968 : R) * t0 * a3 * a0 * w1
    + (4539628424389459968 : R) * t0 * a2 * a1 * w1

/-- Order-`112` contribution of order-`110` Plus block `3`. -/
def degreeZeroOrder112Block3_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (6029194001142251520 : R) * t0 ^ 2 * v1 * a3 * a0
    + (6029194001142251520 : R) * t0 ^ 2 * v1 * a2 * a1
    + (5188146770730811392 : R) * v1 * a3 * a0 * s1
    + (5188146770730811392 : R) * v1 * a2 * a1 * s1

/-- Order-`112` contribution of order-`110` Plus block `4`. -/
def degreeZeroOrder112Block4_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`112` contribution of order-`110` Plus block `5`. -/
def degreeZeroOrder112Block5_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (229683580995895296 : R) * t0 ^ 3 * a3 * b1
    - (459367161991790592 : R) * t0 ^ 3 * a2 * b2
    - (689050742987685888 : R) * t0 ^ 3 * a1 * b3
    - (918734323983581184 : R) * t0 ^ 3 * a0 * b4

/-- Order-`112` contribution of order-`110` Plus block `6`. -/
def degreeZeroOrder112Block6_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (5512405943901487104 : R) * t0 ^ 2 * a3 * a0 * s1
    - (5512405943901487104 : R) * t0 ^ 2 * a2 * a1 * s1

/-- Order-`112` contribution of order-`110` Plus block `7`. -/
def degreeZeroOrder112Block7_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`112` contribution of order-`110` Plus block `8`. -/
def degreeZeroOrder112Block8_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (672901116198912000 : R) * t0 ^ 4 * a3 * a0
    + (672901116198912000 : R) * t0 ^ 4 * a2 * a1

/-- Order-`112` contribution of order-`110` Plus block `9`. -/
def degreeZeroOrder112Block9_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`112` contribution of order-`110` Plus block `10`. -/
def degreeZeroOrder112Block10_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`112` contribution of order-`110` Plus block `11`. -/
def degreeZeroOrder112Block11_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`112` contribution of order-`110` Plus block `12`. -/
def degreeZeroOrder112Block12_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`112` contribution of order-`110` Plus block `13`. -/
def degreeZeroOrder112Block13_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`112` contribution of order-`110` Plus block `14`. -/
def degreeZeroOrder112Block14_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`112` contribution of order-`110` Plus block `15`. -/
def degreeZeroOrder112Block15_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`112` contribution of order-`110` Plus block `16`. -/
def degreeZeroOrder112Block16_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`112` contribution of order-`110` Plus block `17`. -/
def degreeZeroOrder112Block17_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`112` contribution of order-`110` Plus block `18`. -/
def degreeZeroOrder112Block18_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`112` contribution of order-`110` Plus block `19`. -/
def degreeZeroOrder112Block19_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`112` contribution of order-`110` Plus block `20`. -/
def degreeZeroOrder112Block20_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`112` contribution of order-`110` Plus block `21`. -/
def degreeZeroOrder112Block21_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`112` contribution of order-`110` Plus block `22`. -/
def degreeZeroOrder112Block22_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`112` contribution of order-`110` Plus block `23`. -/
def degreeZeroOrder112Block23_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`112` contribution of order-`110` Plus block `24`. -/
def degreeZeroOrder112Block24_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Frozen order-`112` coefficient of the cleared numerator
quotient (`h^10` of `degreeZeroSourceJetQuotient810`,
`h^1` of `degreeZeroOrder110Plus810`). -/
def degreeZeroOrder112810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
  degreeZeroOrder112Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder112Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder112Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder112Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder112Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder112Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder112Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder112Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder112Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder112Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder112Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder112Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder112Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder112Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder112Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder112Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder112Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder112Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder112Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder112Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder112Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder112Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder112Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder112Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder112Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda

/-! ## Order `113` (quotient `h^11`, order-`110` Plus `h^2`) -/

/-- Order-`113` contribution of order-`110` Plus block `0`. -/
def degreeZeroOrder113Block0_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1459166279268040704 : R) * u1 * a3 * a0 * lambda
    - (1459166279268040704 : R) * u1 * a2 * a1 * lambda

/-- Order-`113` contribution of order-`110` Plus block `1`. -/
def degreeZeroOrder113Block1_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (3100728343444586496 : R) * t0 * v1 * a3 * a0 * lambda
    + (3100728343444586496 : R) * t0 * v1 * a2 * a1 * lambda

/-- Order-`113` contribution of order-`110` Plus block `2`. -/
def degreeZeroOrder113Block2_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`113` contribution of order-`110` Plus block `3`. -/
def degreeZeroOrder113Block3_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`113` contribution of order-`110` Plus block `4`. -/
def degreeZeroOrder113Block4_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1614962678877388800 : R) * t0 ^ 3 * a3 * a0 * lambda
    - (1614962678877388800 : R) * t0 ^ 3 * a2 * a1 * lambda

/-- Order-`113` contribution of order-`110` Plus block `5`. -/
def degreeZeroOrder113Block5_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`113` contribution of order-`110` Plus block `6`. -/
def degreeZeroOrder113Block6_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`113` contribution of order-`110` Plus block `7`. -/
def degreeZeroOrder113Block7_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`113` contribution of order-`110` Plus block `8`. -/
def degreeZeroOrder113Block8_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`113` contribution of order-`110` Plus block `9`. -/
def degreeZeroOrder113Block9_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`113` contribution of order-`110` Plus block `10`. -/
def degreeZeroOrder113Block10_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`113` contribution of order-`110` Plus block `11`. -/
def degreeZeroOrder113Block11_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`113` contribution of order-`110` Plus block `12`. -/
def degreeZeroOrder113Block12_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`113` contribution of order-`110` Plus block `13`. -/
def degreeZeroOrder113Block13_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`113` contribution of order-`110` Plus block `14`. -/
def degreeZeroOrder113Block14_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`113` contribution of order-`110` Plus block `15`. -/
def degreeZeroOrder113Block15_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`113` contribution of order-`110` Plus block `16`. -/
def degreeZeroOrder113Block16_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`113` contribution of order-`110` Plus block `17`. -/
def degreeZeroOrder113Block17_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`113` contribution of order-`110` Plus block `18`. -/
def degreeZeroOrder113Block18_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`113` contribution of order-`110` Plus block `19`. -/
def degreeZeroOrder113Block19_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`113` contribution of order-`110` Plus block `20`. -/
def degreeZeroOrder113Block20_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`113` contribution of order-`110` Plus block `21`. -/
def degreeZeroOrder113Block21_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`113` contribution of order-`110` Plus block `22`. -/
def degreeZeroOrder113Block22_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`113` contribution of order-`110` Plus block `23`. -/
def degreeZeroOrder113Block23_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`113` contribution of order-`110` Plus block `24`. -/
def degreeZeroOrder113Block24_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Frozen order-`113` coefficient of the cleared numerator
quotient (`h^11` of `degreeZeroSourceJetQuotient810`,
`h^2` of `degreeZeroOrder110Plus810`). -/
def degreeZeroOrder113810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
  degreeZeroOrder113Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder113Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder113Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder113Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder113Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder113Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder113Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder113Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder113Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder113Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder113Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder113Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder113Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder113Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder113Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder113Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder113Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder113Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder113Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder113Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder113Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder113Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder113Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder113Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder113Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda

/-! ## Order `114` (quotient `h^12`, order-`110` Plus `h^3`) -/

/-- Order-`114` contribution of order-`110` Plus block `0`. -/
def degreeZeroOrder114Block0_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (576460752303423488 : R) * v1 * a2 * b1
    - (1152921504606846976 : R) * v1 * a1 * b2
    - (1729382256910270464 : R) * v1 * a0 * b3
    + (6485183463413514240 : R) * u1 * a2 * a0
    + (3242591731706757120 : R) * u1 * a1 ^ 2
    - (4035225266123964416 : R) * a2 * a0 * w1
    - (2017612633061982208 : R) * a1 ^ 2 * w1

/-- Order-`114` contribution of order-`110` Plus block `1`. -/
def degreeZeroOrder114Block1_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (6485183463413514240 : R) * t0 * v1 * a2 * a0
    - (3242591731706757120 : R) * t0 * v1 * a1 ^ 2

/-- Order-`114` contribution of order-`110` Plus block `2`. -/
def degreeZeroOrder114Block2_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (324259173170675712 : R) * t0 ^ 2 * a2 * b1
    + (648518346341351424 : R) * t0 ^ 2 * a1 * b2
    + (972777519512027136 : R) * t0 ^ 2 * a0 * b3
    + (5188146770730811392 : R) * t0 * a2 * a0 * s1
    + (2594073385365405696 : R) * t0 * a1 ^ 2 * s1

/-- Order-`114` contribution of order-`110` Plus block `3`. -/
def degreeZeroOrder114Block3_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (574208952489738240 : R) * t0 ^ 3 * a2 * a0
    - (287104476244869120 : R) * t0 ^ 3 * a1 ^ 2

/-- Order-`114` contribution of order-`110` Plus block `4`. -/
def degreeZeroOrder114Block4_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`114` contribution of order-`110` Plus block `5`. -/
def degreeZeroOrder114Block5_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`114` contribution of order-`110` Plus block `6`. -/
def degreeZeroOrder114Block6_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`114` contribution of order-`110` Plus block `7`. -/
def degreeZeroOrder114Block7_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`114` contribution of order-`110` Plus block `8`. -/
def degreeZeroOrder114Block8_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`114` contribution of order-`110` Plus block `9`. -/
def degreeZeroOrder114Block9_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`114` contribution of order-`110` Plus block `10`. -/
def degreeZeroOrder114Block10_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`114` contribution of order-`110` Plus block `11`. -/
def degreeZeroOrder114Block11_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`114` contribution of order-`110` Plus block `12`. -/
def degreeZeroOrder114Block12_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`114` contribution of order-`110` Plus block `13`. -/
def degreeZeroOrder114Block13_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`114` contribution of order-`110` Plus block `14`. -/
def degreeZeroOrder114Block14_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`114` contribution of order-`110` Plus block `15`. -/
def degreeZeroOrder114Block15_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`114` contribution of order-`110` Plus block `16`. -/
def degreeZeroOrder114Block16_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`114` contribution of order-`110` Plus block `17`. -/
def degreeZeroOrder114Block17_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`114` contribution of order-`110` Plus block `18`. -/
def degreeZeroOrder114Block18_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`114` contribution of order-`110` Plus block `19`. -/
def degreeZeroOrder114Block19_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`114` contribution of order-`110` Plus block `20`. -/
def degreeZeroOrder114Block20_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`114` contribution of order-`110` Plus block `21`. -/
def degreeZeroOrder114Block21_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`114` contribution of order-`110` Plus block `22`. -/
def degreeZeroOrder114Block22_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`114` contribution of order-`110` Plus block `23`. -/
def degreeZeroOrder114Block23_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`114` contribution of order-`110` Plus block `24`. -/
def degreeZeroOrder114Block24_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Frozen order-`114` coefficient of the cleared numerator
quotient (`h^12` of `degreeZeroSourceJetQuotient810`,
`h^3` of `degreeZeroOrder110Plus810`). -/
def degreeZeroOrder114810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
  degreeZeroOrder114Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder114Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder114Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder114Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder114Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder114Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder114Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder114Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder114Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder114Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder114Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder114Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder114Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder114Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder114Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder114Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder114Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder114Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder114Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder114Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder114Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder114Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder114Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder114Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder114Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda

/-! ## Order `115` (quotient `h^13`, order-`110` Plus `h^4`) -/

/-- Order-`115` contribution of order-`110` Plus block `0`. -/
def degreeZeroOrder115Block0_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1459166279268040704 : R) * v1 * a2 * a0 * lambda
    - (729583139634020352 : R) * v1 * a1 ^ 2 * lambda

/-- Order-`115` contribution of order-`110` Plus block `1`. -/
def degreeZeroOrder115Block1_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (1550364171722293248 : R) * t0 ^ 2 * a2 * a0 * lambda
    + (775182085861146624 : R) * t0 ^ 2 * a1 ^ 2 * lambda

/-- Order-`115` contribution of order-`110` Plus block `2`. -/
def degreeZeroOrder115Block2_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`115` contribution of order-`110` Plus block `3`. -/
def degreeZeroOrder115Block3_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`115` contribution of order-`110` Plus block `4`. -/
def degreeZeroOrder115Block4_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`115` contribution of order-`110` Plus block `5`. -/
def degreeZeroOrder115Block5_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`115` contribution of order-`110` Plus block `6`. -/
def degreeZeroOrder115Block6_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`115` contribution of order-`110` Plus block `7`. -/
def degreeZeroOrder115Block7_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`115` contribution of order-`110` Plus block `8`. -/
def degreeZeroOrder115Block8_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`115` contribution of order-`110` Plus block `9`. -/
def degreeZeroOrder115Block9_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`115` contribution of order-`110` Plus block `10`. -/
def degreeZeroOrder115Block10_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`115` contribution of order-`110` Plus block `11`. -/
def degreeZeroOrder115Block11_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`115` contribution of order-`110` Plus block `12`. -/
def degreeZeroOrder115Block12_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`115` contribution of order-`110` Plus block `13`. -/
def degreeZeroOrder115Block13_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`115` contribution of order-`110` Plus block `14`. -/
def degreeZeroOrder115Block14_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`115` contribution of order-`110` Plus block `15`. -/
def degreeZeroOrder115Block15_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`115` contribution of order-`110` Plus block `16`. -/
def degreeZeroOrder115Block16_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`115` contribution of order-`110` Plus block `17`. -/
def degreeZeroOrder115Block17_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`115` contribution of order-`110` Plus block `18`. -/
def degreeZeroOrder115Block18_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`115` contribution of order-`110` Plus block `19`. -/
def degreeZeroOrder115Block19_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`115` contribution of order-`110` Plus block `20`. -/
def degreeZeroOrder115Block20_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`115` contribution of order-`110` Plus block `21`. -/
def degreeZeroOrder115Block21_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`115` contribution of order-`110` Plus block `22`. -/
def degreeZeroOrder115Block22_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`115` contribution of order-`110` Plus block `23`. -/
def degreeZeroOrder115Block23_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`115` contribution of order-`110` Plus block `24`. -/
def degreeZeroOrder115Block24_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Frozen order-`115` coefficient of the cleared numerator
quotient (`h^13` of `degreeZeroSourceJetQuotient810`,
`h^4` of `degreeZeroOrder110Plus810`). -/
def degreeZeroOrder115810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
  degreeZeroOrder115Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder115Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder115Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder115Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder115Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder115Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder115Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder115Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder115Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder115Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder115Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder115Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder115Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder115Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder115Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder115Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder115Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder115Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder115Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder115Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder115Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder115Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder115Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder115Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder115Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda

/-! ## Order `116` (quotient `h^14`, order-`110` Plus `h^5`) -/

/-- Order-`116` contribution of order-`110` Plus block `0`. -/
def degreeZeroOrder116Block0_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (576460752303423488 : R) * t0 * a1 * b1
    - (1152921504606846976 : R) * t0 * a0 * b2
    + (6485183463413514240 : R) * v1 * a1 * a0

/-- Order-`116` contribution of order-`110` Plus block `1`. -/
def degreeZeroOrder116Block1_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (405323966463344640 : R) * t0 ^ 2 * a1 * a0
    - (4611686018427387904 : R) * a1 * a0 * s1

/-- Order-`116` contribution of order-`110` Plus block `2`. -/
def degreeZeroOrder116Block2_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`116` contribution of order-`110` Plus block `3`. -/
def degreeZeroOrder116Block3_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`116` contribution of order-`110` Plus block `4`. -/
def degreeZeroOrder116Block4_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`116` contribution of order-`110` Plus block `5`. -/
def degreeZeroOrder116Block5_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`116` contribution of order-`110` Plus block `6`. -/
def degreeZeroOrder116Block6_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`116` contribution of order-`110` Plus block `7`. -/
def degreeZeroOrder116Block7_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`116` contribution of order-`110` Plus block `8`. -/
def degreeZeroOrder116Block8_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`116` contribution of order-`110` Plus block `9`. -/
def degreeZeroOrder116Block9_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`116` contribution of order-`110` Plus block `10`. -/
def degreeZeroOrder116Block10_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`116` contribution of order-`110` Plus block `11`. -/
def degreeZeroOrder116Block11_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`116` contribution of order-`110` Plus block `12`. -/
def degreeZeroOrder116Block12_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`116` contribution of order-`110` Plus block `13`. -/
def degreeZeroOrder116Block13_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`116` contribution of order-`110` Plus block `14`. -/
def degreeZeroOrder116Block14_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`116` contribution of order-`110` Plus block `15`. -/
def degreeZeroOrder116Block15_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`116` contribution of order-`110` Plus block `16`. -/
def degreeZeroOrder116Block16_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`116` contribution of order-`110` Plus block `17`. -/
def degreeZeroOrder116Block17_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`116` contribution of order-`110` Plus block `18`. -/
def degreeZeroOrder116Block18_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`116` contribution of order-`110` Plus block `19`. -/
def degreeZeroOrder116Block19_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`116` contribution of order-`110` Plus block `20`. -/
def degreeZeroOrder116Block20_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`116` contribution of order-`110` Plus block `21`. -/
def degreeZeroOrder116Block21_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`116` contribution of order-`110` Plus block `22`. -/
def degreeZeroOrder116Block22_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`116` contribution of order-`110` Plus block `23`. -/
def degreeZeroOrder116Block23_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`116` contribution of order-`110` Plus block `24`. -/
def degreeZeroOrder116Block24_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Frozen order-`116` coefficient of the cleared numerator
quotient (`h^14` of `degreeZeroSourceJetQuotient810`,
`h^5` of `degreeZeroOrder110Plus810`). -/
def degreeZeroOrder116810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
  degreeZeroOrder116Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder116Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder116Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder116Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder116Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder116Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder116Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder116Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder116Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder116Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder116Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder116Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder116Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder116Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder116Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder116Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder116Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder116Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder116Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder116Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder116Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder116Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder116Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder116Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder116Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda

/-! ## Order `117` (quotient `h^15`, order-`110` Plus `h^6`) -/

/-- Order-`117` contribution of order-`110` Plus block `0`. -/
def degreeZeroOrder117Block0_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1459166279268040704 : R) * t0 * a1 * a0 * lambda

/-- Order-`117` contribution of order-`110` Plus block `1`. -/
def degreeZeroOrder117Block1_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`117` contribution of order-`110` Plus block `2`. -/
def degreeZeroOrder117Block2_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`117` contribution of order-`110` Plus block `3`. -/
def degreeZeroOrder117Block3_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`117` contribution of order-`110` Plus block `4`. -/
def degreeZeroOrder117Block4_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`117` contribution of order-`110` Plus block `5`. -/
def degreeZeroOrder117Block5_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`117` contribution of order-`110` Plus block `6`. -/
def degreeZeroOrder117Block6_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`117` contribution of order-`110` Plus block `7`. -/
def degreeZeroOrder117Block7_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`117` contribution of order-`110` Plus block `8`. -/
def degreeZeroOrder117Block8_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`117` contribution of order-`110` Plus block `9`. -/
def degreeZeroOrder117Block9_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`117` contribution of order-`110` Plus block `10`. -/
def degreeZeroOrder117Block10_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`117` contribution of order-`110` Plus block `11`. -/
def degreeZeroOrder117Block11_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`117` contribution of order-`110` Plus block `12`. -/
def degreeZeroOrder117Block12_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`117` contribution of order-`110` Plus block `13`. -/
def degreeZeroOrder117Block13_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`117` contribution of order-`110` Plus block `14`. -/
def degreeZeroOrder117Block14_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`117` contribution of order-`110` Plus block `15`. -/
def degreeZeroOrder117Block15_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`117` contribution of order-`110` Plus block `16`. -/
def degreeZeroOrder117Block16_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`117` contribution of order-`110` Plus block `17`. -/
def degreeZeroOrder117Block17_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`117` contribution of order-`110` Plus block `18`. -/
def degreeZeroOrder117Block18_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`117` contribution of order-`110` Plus block `19`. -/
def degreeZeroOrder117Block19_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`117` contribution of order-`110` Plus block `20`. -/
def degreeZeroOrder117Block20_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`117` contribution of order-`110` Plus block `21`. -/
def degreeZeroOrder117Block21_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`117` contribution of order-`110` Plus block `22`. -/
def degreeZeroOrder117Block22_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`117` contribution of order-`110` Plus block `23`. -/
def degreeZeroOrder117Block23_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`117` contribution of order-`110` Plus block `24`. -/
def degreeZeroOrder117Block24_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Frozen order-`117` coefficient of the cleared numerator
quotient (`h^15` of `degreeZeroSourceJetQuotient810`,
`h^6` of `degreeZeroOrder110Plus810`). -/
def degreeZeroOrder117810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
  degreeZeroOrder117Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder117Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder117Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder117Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder117Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder117Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder117Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder117Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder117Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder117Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder117Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder117Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder117Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder117Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder117Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder117Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder117Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder117Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder117Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder117Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder117Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder117Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder117Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder117Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder117Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda

/-! ## Order `118` (quotient `h^16`, order-`110` Plus `h^7`) -/

/-- Order-`118` contribution of order-`110` Plus block `0`. -/
def degreeZeroOrder118Block0_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (4611686018427387904 : R) * a0 * b1

/-- Order-`118` contribution of order-`110` Plus block `1`. -/
def degreeZeroOrder118Block1_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` contribution of order-`110` Plus block `2`. -/
def degreeZeroOrder118Block2_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` contribution of order-`110` Plus block `3`. -/
def degreeZeroOrder118Block3_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` contribution of order-`110` Plus block `4`. -/
def degreeZeroOrder118Block4_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` contribution of order-`110` Plus block `5`. -/
def degreeZeroOrder118Block5_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` contribution of order-`110` Plus block `6`. -/
def degreeZeroOrder118Block6_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` contribution of order-`110` Plus block `7`. -/
def degreeZeroOrder118Block7_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` contribution of order-`110` Plus block `8`. -/
def degreeZeroOrder118Block8_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` contribution of order-`110` Plus block `9`. -/
def degreeZeroOrder118Block9_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` contribution of order-`110` Plus block `10`. -/
def degreeZeroOrder118Block10_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` contribution of order-`110` Plus block `11`. -/
def degreeZeroOrder118Block11_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` contribution of order-`110` Plus block `12`. -/
def degreeZeroOrder118Block12_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` contribution of order-`110` Plus block `13`. -/
def degreeZeroOrder118Block13_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` contribution of order-`110` Plus block `14`. -/
def degreeZeroOrder118Block14_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` contribution of order-`110` Plus block `15`. -/
def degreeZeroOrder118Block15_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` contribution of order-`110` Plus block `16`. -/
def degreeZeroOrder118Block16_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` contribution of order-`110` Plus block `17`. -/
def degreeZeroOrder118Block17_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` contribution of order-`110` Plus block `18`. -/
def degreeZeroOrder118Block18_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` contribution of order-`110` Plus block `19`. -/
def degreeZeroOrder118Block19_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` contribution of order-`110` Plus block `20`. -/
def degreeZeroOrder118Block20_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` contribution of order-`110` Plus block `21`. -/
def degreeZeroOrder118Block21_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` contribution of order-`110` Plus block `22`. -/
def degreeZeroOrder118Block22_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` contribution of order-`110` Plus block `23`. -/
def degreeZeroOrder118Block23_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` contribution of order-`110` Plus block `24`. -/
def degreeZeroOrder118Block24_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Frozen order-`118` coefficient of the cleared numerator
quotient (`h^16` of `degreeZeroSourceJetQuotient810`,
`h^7` of `degreeZeroOrder110Plus810`). -/
def degreeZeroOrder118810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
  degreeZeroOrder118Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda

/-! ## Remaining Plus factor after order `118` (order-`110` Plus `h^8` and higher) -/

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `0`. -/
def degreeZeroOrder118PlusBlock0_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (648518346341351424 : R) * a0 ^ 2 * lambda

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `1`. -/
def degreeZeroOrder118PlusBlock1_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `2`. -/
def degreeZeroOrder118PlusBlock2_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `3`. -/
def degreeZeroOrder118PlusBlock3_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `4`. -/
def degreeZeroOrder118PlusBlock4_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `5`. -/
def degreeZeroOrder118PlusBlock5_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `6`. -/
def degreeZeroOrder118PlusBlock6_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `7`. -/
def degreeZeroOrder118PlusBlock7_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `8`. -/
def degreeZeroOrder118PlusBlock8_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `9`. -/
def degreeZeroOrder118PlusBlock9_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `10`. -/
def degreeZeroOrder118PlusBlock10_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `11`. -/
def degreeZeroOrder118PlusBlock11_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `12`. -/
def degreeZeroOrder118PlusBlock12_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `13`. -/
def degreeZeroOrder118PlusBlock13_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `14`. -/
def degreeZeroOrder118PlusBlock14_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `15`. -/
def degreeZeroOrder118PlusBlock15_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `16`. -/
def degreeZeroOrder118PlusBlock16_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `17`. -/
def degreeZeroOrder118PlusBlock17_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `18`. -/
def degreeZeroOrder118PlusBlock18_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `19`. -/
def degreeZeroOrder118PlusBlock19_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `20`. -/
def degreeZeroOrder118PlusBlock20_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `21`. -/
def degreeZeroOrder118PlusBlock21_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `22`. -/
def degreeZeroOrder118PlusBlock22_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `23`. -/
def degreeZeroOrder118PlusBlock23_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`118` Plus remainder contributed by order-`110` Plus block `24`. -/
def degreeZeroOrder118PlusBlock24_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Remaining factor of `degreeZeroOrder110Plus810` after the
orders `111` through `118` are peeled: the `h^8`-and-higher terms,
shifted down by `h^8`.  This is the holomorphic cofactor of the
order-`102` quotient. -/
def degreeZeroOrder118Plus810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
  degreeZeroOrder118PlusBlock0_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118PlusBlock1_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118PlusBlock2_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118PlusBlock3_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118PlusBlock4_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118PlusBlock5_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118PlusBlock6_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118PlusBlock7_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118PlusBlock8_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118PlusBlock9_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118PlusBlock10_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118PlusBlock11_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118PlusBlock12_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118PlusBlock13_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118PlusBlock14_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118PlusBlock15_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118PlusBlock16_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118PlusBlock17_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118PlusBlock18_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118PlusBlock19_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118PlusBlock20_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118PlusBlock21_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118PlusBlock22_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118PlusBlock23_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder118PlusBlock24_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda

/-! ## Blocked Plus expansions through order `118` -/

section DegreeZeroTowerCeilingScale810

variable {R : Type*} [CommRing R]


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock0_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock0_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock0_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock0_810, degreeZeroOrder111Block0_810, degreeZeroOrder112Block0_810, degreeZeroOrder113Block0_810, degreeZeroOrder114Block0_810, degreeZeroOrder115Block0_810, degreeZeroOrder116Block0_810, degreeZeroOrder117Block0_810, degreeZeroOrder118Block0_810, degreeZeroOrder118PlusBlock0_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock1_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock1_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock1_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock1_810, degreeZeroOrder111Block1_810, degreeZeroOrder112Block1_810, degreeZeroOrder113Block1_810, degreeZeroOrder114Block1_810, degreeZeroOrder115Block1_810, degreeZeroOrder116Block1_810, degreeZeroOrder117Block1_810, degreeZeroOrder118Block1_810, degreeZeroOrder118PlusBlock1_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock2_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock2_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock2_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock2_810, degreeZeroOrder111Block2_810, degreeZeroOrder112Block2_810, degreeZeroOrder113Block2_810, degreeZeroOrder114Block2_810, degreeZeroOrder115Block2_810, degreeZeroOrder116Block2_810, degreeZeroOrder117Block2_810, degreeZeroOrder118Block2_810, degreeZeroOrder118PlusBlock2_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock3_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock3_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock3_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock3_810, degreeZeroOrder111Block3_810, degreeZeroOrder112Block3_810, degreeZeroOrder113Block3_810, degreeZeroOrder114Block3_810, degreeZeroOrder115Block3_810, degreeZeroOrder116Block3_810, degreeZeroOrder117Block3_810, degreeZeroOrder118Block3_810, degreeZeroOrder118PlusBlock3_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock4_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock4_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock4_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock4_810, degreeZeroOrder111Block4_810, degreeZeroOrder112Block4_810, degreeZeroOrder113Block4_810, degreeZeroOrder114Block4_810, degreeZeroOrder115Block4_810, degreeZeroOrder116Block4_810, degreeZeroOrder117Block4_810, degreeZeroOrder118Block4_810, degreeZeroOrder118PlusBlock4_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock5_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock5_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock5_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock5_810, degreeZeroOrder111Block5_810, degreeZeroOrder112Block5_810, degreeZeroOrder113Block5_810, degreeZeroOrder114Block5_810, degreeZeroOrder115Block5_810, degreeZeroOrder116Block5_810, degreeZeroOrder117Block5_810, degreeZeroOrder118Block5_810, degreeZeroOrder118PlusBlock5_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock6_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock6_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock6_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock6_810, degreeZeroOrder111Block6_810, degreeZeroOrder112Block6_810, degreeZeroOrder113Block6_810, degreeZeroOrder114Block6_810, degreeZeroOrder115Block6_810, degreeZeroOrder116Block6_810, degreeZeroOrder117Block6_810, degreeZeroOrder118Block6_810, degreeZeroOrder118PlusBlock6_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock7_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock7_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock7_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock7_810, degreeZeroOrder111Block7_810, degreeZeroOrder112Block7_810, degreeZeroOrder113Block7_810, degreeZeroOrder114Block7_810, degreeZeroOrder115Block7_810, degreeZeroOrder116Block7_810, degreeZeroOrder117Block7_810, degreeZeroOrder118Block7_810, degreeZeroOrder118PlusBlock7_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock8_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock8_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock8_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock8_810, degreeZeroOrder111Block8_810, degreeZeroOrder112Block8_810, degreeZeroOrder113Block8_810, degreeZeroOrder114Block8_810, degreeZeroOrder115Block8_810, degreeZeroOrder116Block8_810, degreeZeroOrder117Block8_810, degreeZeroOrder118Block8_810, degreeZeroOrder118PlusBlock8_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock9_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock9_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock9_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock9_810, degreeZeroOrder111Block9_810, degreeZeroOrder112Block9_810, degreeZeroOrder113Block9_810, degreeZeroOrder114Block9_810, degreeZeroOrder115Block9_810, degreeZeroOrder116Block9_810, degreeZeroOrder117Block9_810, degreeZeroOrder118Block9_810, degreeZeroOrder118PlusBlock9_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock10_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock10_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock10_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock10_810, degreeZeroOrder111Block10_810, degreeZeroOrder112Block10_810, degreeZeroOrder113Block10_810, degreeZeroOrder114Block10_810, degreeZeroOrder115Block10_810, degreeZeroOrder116Block10_810, degreeZeroOrder117Block10_810, degreeZeroOrder118Block10_810, degreeZeroOrder118PlusBlock10_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock11_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock11_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock11_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock11_810, degreeZeroOrder111Block11_810, degreeZeroOrder112Block11_810, degreeZeroOrder113Block11_810, degreeZeroOrder114Block11_810, degreeZeroOrder115Block11_810, degreeZeroOrder116Block11_810, degreeZeroOrder117Block11_810, degreeZeroOrder118Block11_810, degreeZeroOrder118PlusBlock11_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock12_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock12_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock12_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock12_810, degreeZeroOrder111Block12_810, degreeZeroOrder112Block12_810, degreeZeroOrder113Block12_810, degreeZeroOrder114Block12_810, degreeZeroOrder115Block12_810, degreeZeroOrder116Block12_810, degreeZeroOrder117Block12_810, degreeZeroOrder118Block12_810, degreeZeroOrder118PlusBlock12_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock13_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock13_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock13_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock13_810, degreeZeroOrder111Block13_810, degreeZeroOrder112Block13_810, degreeZeroOrder113Block13_810, degreeZeroOrder114Block13_810, degreeZeroOrder115Block13_810, degreeZeroOrder116Block13_810, degreeZeroOrder117Block13_810, degreeZeroOrder118Block13_810, degreeZeroOrder118PlusBlock13_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock14_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock14_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock14_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock14_810, degreeZeroOrder111Block14_810, degreeZeroOrder112Block14_810, degreeZeroOrder113Block14_810, degreeZeroOrder114Block14_810, degreeZeroOrder115Block14_810, degreeZeroOrder116Block14_810, degreeZeroOrder117Block14_810, degreeZeroOrder118Block14_810, degreeZeroOrder118PlusBlock14_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock15_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock15_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock15_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock15_810, degreeZeroOrder111Block15_810, degreeZeroOrder112Block15_810, degreeZeroOrder113Block15_810, degreeZeroOrder114Block15_810, degreeZeroOrder115Block15_810, degreeZeroOrder116Block15_810, degreeZeroOrder117Block15_810, degreeZeroOrder118Block15_810, degreeZeroOrder118PlusBlock15_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock16_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock16_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock16_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock16_810, degreeZeroOrder111Block16_810, degreeZeroOrder112Block16_810, degreeZeroOrder113Block16_810, degreeZeroOrder114Block16_810, degreeZeroOrder115Block16_810, degreeZeroOrder116Block16_810, degreeZeroOrder117Block16_810, degreeZeroOrder118Block16_810, degreeZeroOrder118PlusBlock16_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock17_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock17_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock17_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock17_810, degreeZeroOrder111Block17_810, degreeZeroOrder112Block17_810, degreeZeroOrder113Block17_810, degreeZeroOrder114Block17_810, degreeZeroOrder115Block17_810, degreeZeroOrder116Block17_810, degreeZeroOrder117Block17_810, degreeZeroOrder118Block17_810, degreeZeroOrder118PlusBlock17_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock18_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock18_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock18_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock18_810, degreeZeroOrder111Block18_810, degreeZeroOrder112Block18_810, degreeZeroOrder113Block18_810, degreeZeroOrder114Block18_810, degreeZeroOrder115Block18_810, degreeZeroOrder116Block18_810, degreeZeroOrder117Block18_810, degreeZeroOrder118Block18_810, degreeZeroOrder118PlusBlock18_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock19_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock19_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock19_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock19_810, degreeZeroOrder111Block19_810, degreeZeroOrder112Block19_810, degreeZeroOrder113Block19_810, degreeZeroOrder114Block19_810, degreeZeroOrder115Block19_810, degreeZeroOrder116Block19_810, degreeZeroOrder117Block19_810, degreeZeroOrder118Block19_810, degreeZeroOrder118PlusBlock19_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock20_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock20_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock20_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock20_810, degreeZeroOrder111Block20_810, degreeZeroOrder112Block20_810, degreeZeroOrder113Block20_810, degreeZeroOrder114Block20_810, degreeZeroOrder115Block20_810, degreeZeroOrder116Block20_810, degreeZeroOrder117Block20_810, degreeZeroOrder118Block20_810, degreeZeroOrder118PlusBlock20_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock21_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock21_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock21_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock21_810, degreeZeroOrder111Block21_810, degreeZeroOrder112Block21_810, degreeZeroOrder113Block21_810, degreeZeroOrder114Block21_810, degreeZeroOrder115Block21_810, degreeZeroOrder116Block21_810, degreeZeroOrder117Block21_810, degreeZeroOrder118Block21_810, degreeZeroOrder118PlusBlock21_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock22_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock22_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock22_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock22_810, degreeZeroOrder111Block22_810, degreeZeroOrder112Block22_810, degreeZeroOrder113Block22_810, degreeZeroOrder114Block22_810, degreeZeroOrder115Block22_810, degreeZeroOrder116Block22_810, degreeZeroOrder117Block22_810, degreeZeroOrder118Block22_810, degreeZeroOrder118PlusBlock22_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock23_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock23_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock23_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock23_810, degreeZeroOrder111Block23_810, degreeZeroOrder112Block23_810, degreeZeroOrder113Block23_810, degreeZeroOrder114Block23_810, degreeZeroOrder115Block23_810, degreeZeroOrder116Block23_810, degreeZeroOrder117Block23_810, degreeZeroOrder118Block23_810, degreeZeroOrder118PlusBlock23_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroOrder110PlusBlock24_810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110PlusBlock24_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118PlusBlock24_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroOrder110PlusBlock24_810, degreeZeroOrder111Block24_810, degreeZeroOrder112Block24_810, degreeZeroOrder113Block24_810, degreeZeroOrder114Block24_810, degreeZeroOrder115Block24_810, degreeZeroOrder116Block24_810, degreeZeroOrder117Block24_810, degreeZeroOrder118Block24_810, degreeZeroOrder118PlusBlock24_810]
  ring


set_option maxHeartbeats 800000000 in
/-- Order-`110` Plus remainder through order `118`. -/
theorem degreeZeroOrder110Plus810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder112810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder113810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder114810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder115810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder116810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder117810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder118810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder118Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda := by
  have hb0 := degreeZeroOrder110PlusBlock0_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb1 := degreeZeroOrder110PlusBlock1_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb2 := degreeZeroOrder110PlusBlock2_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb3 := degreeZeroOrder110PlusBlock3_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb4 := degreeZeroOrder110PlusBlock4_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb5 := degreeZeroOrder110PlusBlock5_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb6 := degreeZeroOrder110PlusBlock6_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb7 := degreeZeroOrder110PlusBlock7_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb8 := degreeZeroOrder110PlusBlock8_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb9 := degreeZeroOrder110PlusBlock9_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb10 := degreeZeroOrder110PlusBlock10_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb11 := degreeZeroOrder110PlusBlock11_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb12 := degreeZeroOrder110PlusBlock12_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb13 := degreeZeroOrder110PlusBlock13_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb14 := degreeZeroOrder110PlusBlock14_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb15 := degreeZeroOrder110PlusBlock15_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb16 := degreeZeroOrder110PlusBlock16_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb17 := degreeZeroOrder110PlusBlock17_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb18 := degreeZeroOrder110PlusBlock18_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb19 := degreeZeroOrder110PlusBlock19_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb20 := degreeZeroOrder110PlusBlock20_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb21 := degreeZeroOrder110PlusBlock21_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb22 := degreeZeroOrder110PlusBlock22_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb23 := degreeZeroOrder110PlusBlock23_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb24 := degreeZeroOrder110PlusBlock24_810_orders111to118
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  simp only [degreeZeroOrder110Plus810]
  rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14,
    hb15, hb16, hb17, hb18, hb19, hb20, hb21, hb22, hb23, hb24]
  simp only [degreeZeroOrder111810, degreeZeroOrder112810, degreeZeroOrder113810, degreeZeroOrder114810, degreeZeroOrder115810, degreeZeroOrder116810, degreeZeroOrder117810, degreeZeroOrder118810, degreeZeroOrder118Plus810]
  ring

#print axioms degreeZeroOrder110Plus810_orders111to118

theorem degreeZeroOrder110Plus810_zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroOrder110Plus810 0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder111810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda := by
  simpa using degreeZeroOrder110Plus810_orders111to118
    0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda

#print axioms degreeZeroOrder110Plus810_zero

set_option maxHeartbeats 800000000 in
/-- Quotient expansion through order `118`. -/
theorem degreeZeroSourceJetQuotient810_orders111to118
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetQuotient810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroSourceJetHead810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder106810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder107810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder108810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder109810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 9 * degreeZeroOrder111810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 10 * degreeZeroOrder112810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 11 * degreeZeroOrder113810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 12 * degreeZeroOrder114810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 13 * degreeZeroOrder115810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 14 * degreeZeroOrder116810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 15 * degreeZeroOrder117810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 16 * degreeZeroOrder118810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 17 * degreeZeroOrder118Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda := by
  rw [degreeZeroSourceJetQuotient810_orders103to110,
    degreeZeroOrder110Plus810_orders111to118]
  ring

#print axioms degreeZeroSourceJetQuotient810_orders111to118

end DegreeZeroTowerCeilingScale810

/-! ## Ring maps and evaluation -/


section DegreeZeroTowerCeilingMap810


variable {R S : Type*} [CommRing R] [CommRing S]


set_option maxHeartbeats 800000000 in
theorem map_degreeZeroOrder111810
    (phi : R →+* S) (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (degreeZeroOrder111810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      degreeZeroOrder111810 (phi t0) (phi v1) (phi u1) (phi a4) (phi a3)
        (phi a2) (phi a1) (phi a0) (phi s1) (phi w1) (phi b62) (phi b5)
        (phi b4) (phi b3) (phi b2) (phi b1) (phi lambda) := by
  simp only [degreeZeroOrder111810, degreeZeroOrder111Block0_810, degreeZeroOrder111Block1_810, degreeZeroOrder111Block2_810, degreeZeroOrder111Block3_810, degreeZeroOrder111Block4_810, degreeZeroOrder111Block5_810, degreeZeroOrder111Block6_810, degreeZeroOrder111Block7_810, degreeZeroOrder111Block8_810, degreeZeroOrder111Block9_810, degreeZeroOrder111Block10_810, degreeZeroOrder111Block11_810, degreeZeroOrder111Block12_810, degreeZeroOrder111Block13_810, degreeZeroOrder111Block14_810, degreeZeroOrder111Block15_810, degreeZeroOrder111Block16_810, degreeZeroOrder111Block17_810, degreeZeroOrder111Block18_810, degreeZeroOrder111Block19_810, degreeZeroOrder111Block20_810, degreeZeroOrder111Block21_810, degreeZeroOrder111Block22_810, degreeZeroOrder111Block23_810, degreeZeroOrder111Block24_810, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, map_zero]


set_option maxHeartbeats 800000000 in
theorem map_degreeZeroOrder112810
    (phi : R →+* S) (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (degreeZeroOrder112810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      degreeZeroOrder112810 (phi t0) (phi v1) (phi u1) (phi a4) (phi a3)
        (phi a2) (phi a1) (phi a0) (phi s1) (phi w1) (phi b62) (phi b5)
        (phi b4) (phi b3) (phi b2) (phi b1) (phi lambda) := by
  simp only [degreeZeroOrder112810, degreeZeroOrder112Block0_810, degreeZeroOrder112Block1_810, degreeZeroOrder112Block2_810, degreeZeroOrder112Block3_810, degreeZeroOrder112Block4_810, degreeZeroOrder112Block5_810, degreeZeroOrder112Block6_810, degreeZeroOrder112Block7_810, degreeZeroOrder112Block8_810, degreeZeroOrder112Block9_810, degreeZeroOrder112Block10_810, degreeZeroOrder112Block11_810, degreeZeroOrder112Block12_810, degreeZeroOrder112Block13_810, degreeZeroOrder112Block14_810, degreeZeroOrder112Block15_810, degreeZeroOrder112Block16_810, degreeZeroOrder112Block17_810, degreeZeroOrder112Block18_810, degreeZeroOrder112Block19_810, degreeZeroOrder112Block20_810, degreeZeroOrder112Block21_810, degreeZeroOrder112Block22_810, degreeZeroOrder112Block23_810, degreeZeroOrder112Block24_810, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, map_zero]


set_option maxHeartbeats 800000000 in
theorem map_degreeZeroOrder113810
    (phi : R →+* S) (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (degreeZeroOrder113810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      degreeZeroOrder113810 (phi t0) (phi v1) (phi u1) (phi a4) (phi a3)
        (phi a2) (phi a1) (phi a0) (phi s1) (phi w1) (phi b62) (phi b5)
        (phi b4) (phi b3) (phi b2) (phi b1) (phi lambda) := by
  simp only [degreeZeroOrder113810, degreeZeroOrder113Block0_810, degreeZeroOrder113Block1_810, degreeZeroOrder113Block2_810, degreeZeroOrder113Block3_810, degreeZeroOrder113Block4_810, degreeZeroOrder113Block5_810, degreeZeroOrder113Block6_810, degreeZeroOrder113Block7_810, degreeZeroOrder113Block8_810, degreeZeroOrder113Block9_810, degreeZeroOrder113Block10_810, degreeZeroOrder113Block11_810, degreeZeroOrder113Block12_810, degreeZeroOrder113Block13_810, degreeZeroOrder113Block14_810, degreeZeroOrder113Block15_810, degreeZeroOrder113Block16_810, degreeZeroOrder113Block17_810, degreeZeroOrder113Block18_810, degreeZeroOrder113Block19_810, degreeZeroOrder113Block20_810, degreeZeroOrder113Block21_810, degreeZeroOrder113Block22_810, degreeZeroOrder113Block23_810, degreeZeroOrder113Block24_810, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, map_zero]


set_option maxHeartbeats 800000000 in
theorem map_degreeZeroOrder114810
    (phi : R →+* S) (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (degreeZeroOrder114810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      degreeZeroOrder114810 (phi t0) (phi v1) (phi u1) (phi a4) (phi a3)
        (phi a2) (phi a1) (phi a0) (phi s1) (phi w1) (phi b62) (phi b5)
        (phi b4) (phi b3) (phi b2) (phi b1) (phi lambda) := by
  simp only [degreeZeroOrder114810, degreeZeroOrder114Block0_810, degreeZeroOrder114Block1_810, degreeZeroOrder114Block2_810, degreeZeroOrder114Block3_810, degreeZeroOrder114Block4_810, degreeZeroOrder114Block5_810, degreeZeroOrder114Block6_810, degreeZeroOrder114Block7_810, degreeZeroOrder114Block8_810, degreeZeroOrder114Block9_810, degreeZeroOrder114Block10_810, degreeZeroOrder114Block11_810, degreeZeroOrder114Block12_810, degreeZeroOrder114Block13_810, degreeZeroOrder114Block14_810, degreeZeroOrder114Block15_810, degreeZeroOrder114Block16_810, degreeZeroOrder114Block17_810, degreeZeroOrder114Block18_810, degreeZeroOrder114Block19_810, degreeZeroOrder114Block20_810, degreeZeroOrder114Block21_810, degreeZeroOrder114Block22_810, degreeZeroOrder114Block23_810, degreeZeroOrder114Block24_810, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, map_zero]


set_option maxHeartbeats 800000000 in
theorem map_degreeZeroOrder115810
    (phi : R →+* S) (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (degreeZeroOrder115810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      degreeZeroOrder115810 (phi t0) (phi v1) (phi u1) (phi a4) (phi a3)
        (phi a2) (phi a1) (phi a0) (phi s1) (phi w1) (phi b62) (phi b5)
        (phi b4) (phi b3) (phi b2) (phi b1) (phi lambda) := by
  simp only [degreeZeroOrder115810, degreeZeroOrder115Block0_810, degreeZeroOrder115Block1_810, degreeZeroOrder115Block2_810, degreeZeroOrder115Block3_810, degreeZeroOrder115Block4_810, degreeZeroOrder115Block5_810, degreeZeroOrder115Block6_810, degreeZeroOrder115Block7_810, degreeZeroOrder115Block8_810, degreeZeroOrder115Block9_810, degreeZeroOrder115Block10_810, degreeZeroOrder115Block11_810, degreeZeroOrder115Block12_810, degreeZeroOrder115Block13_810, degreeZeroOrder115Block14_810, degreeZeroOrder115Block15_810, degreeZeroOrder115Block16_810, degreeZeroOrder115Block17_810, degreeZeroOrder115Block18_810, degreeZeroOrder115Block19_810, degreeZeroOrder115Block20_810, degreeZeroOrder115Block21_810, degreeZeroOrder115Block22_810, degreeZeroOrder115Block23_810, degreeZeroOrder115Block24_810, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, map_zero]


set_option maxHeartbeats 800000000 in
theorem map_degreeZeroOrder116810
    (phi : R →+* S) (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (degreeZeroOrder116810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      degreeZeroOrder116810 (phi t0) (phi v1) (phi u1) (phi a4) (phi a3)
        (phi a2) (phi a1) (phi a0) (phi s1) (phi w1) (phi b62) (phi b5)
        (phi b4) (phi b3) (phi b2) (phi b1) (phi lambda) := by
  simp only [degreeZeroOrder116810, degreeZeroOrder116Block0_810, degreeZeroOrder116Block1_810, degreeZeroOrder116Block2_810, degreeZeroOrder116Block3_810, degreeZeroOrder116Block4_810, degreeZeroOrder116Block5_810, degreeZeroOrder116Block6_810, degreeZeroOrder116Block7_810, degreeZeroOrder116Block8_810, degreeZeroOrder116Block9_810, degreeZeroOrder116Block10_810, degreeZeroOrder116Block11_810, degreeZeroOrder116Block12_810, degreeZeroOrder116Block13_810, degreeZeroOrder116Block14_810, degreeZeroOrder116Block15_810, degreeZeroOrder116Block16_810, degreeZeroOrder116Block17_810, degreeZeroOrder116Block18_810, degreeZeroOrder116Block19_810, degreeZeroOrder116Block20_810, degreeZeroOrder116Block21_810, degreeZeroOrder116Block22_810, degreeZeroOrder116Block23_810, degreeZeroOrder116Block24_810, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, map_zero]


set_option maxHeartbeats 800000000 in
theorem map_degreeZeroOrder117810
    (phi : R →+* S) (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (degreeZeroOrder117810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      degreeZeroOrder117810 (phi t0) (phi v1) (phi u1) (phi a4) (phi a3)
        (phi a2) (phi a1) (phi a0) (phi s1) (phi w1) (phi b62) (phi b5)
        (phi b4) (phi b3) (phi b2) (phi b1) (phi lambda) := by
  simp only [degreeZeroOrder117810, degreeZeroOrder117Block0_810, degreeZeroOrder117Block1_810, degreeZeroOrder117Block2_810, degreeZeroOrder117Block3_810, degreeZeroOrder117Block4_810, degreeZeroOrder117Block5_810, degreeZeroOrder117Block6_810, degreeZeroOrder117Block7_810, degreeZeroOrder117Block8_810, degreeZeroOrder117Block9_810, degreeZeroOrder117Block10_810, degreeZeroOrder117Block11_810, degreeZeroOrder117Block12_810, degreeZeroOrder117Block13_810, degreeZeroOrder117Block14_810, degreeZeroOrder117Block15_810, degreeZeroOrder117Block16_810, degreeZeroOrder117Block17_810, degreeZeroOrder117Block18_810, degreeZeroOrder117Block19_810, degreeZeroOrder117Block20_810, degreeZeroOrder117Block21_810, degreeZeroOrder117Block22_810, degreeZeroOrder117Block23_810, degreeZeroOrder117Block24_810, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, map_zero]


set_option maxHeartbeats 800000000 in
theorem map_degreeZeroOrder118810
    (phi : R →+* S) (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (degreeZeroOrder118810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      degreeZeroOrder118810 (phi t0) (phi v1) (phi u1) (phi a4) (phi a3)
        (phi a2) (phi a1) (phi a0) (phi s1) (phi w1) (phi b62) (phi b5)
        (phi b4) (phi b3) (phi b2) (phi b1) (phi lambda) := by
  simp only [degreeZeroOrder118810, degreeZeroOrder118Block0_810, degreeZeroOrder118Block1_810, degreeZeroOrder118Block2_810, degreeZeroOrder118Block3_810, degreeZeroOrder118Block4_810, degreeZeroOrder118Block5_810, degreeZeroOrder118Block6_810, degreeZeroOrder118Block7_810, degreeZeroOrder118Block8_810, degreeZeroOrder118Block9_810, degreeZeroOrder118Block10_810, degreeZeroOrder118Block11_810, degreeZeroOrder118Block12_810, degreeZeroOrder118Block13_810, degreeZeroOrder118Block14_810, degreeZeroOrder118Block15_810, degreeZeroOrder118Block16_810, degreeZeroOrder118Block17_810, degreeZeroOrder118Block18_810, degreeZeroOrder118Block19_810, degreeZeroOrder118Block20_810, degreeZeroOrder118Block21_810, degreeZeroOrder118Block22_810, degreeZeroOrder118Block23_810, degreeZeroOrder118Block24_810, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, map_zero]


set_option maxHeartbeats 800000000 in
theorem map_degreeZeroOrder118Plus810
    (phi : R →+* S) (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (degreeZeroOrder118Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda) =
      degreeZeroOrder118Plus810 (phi h) (phi t0) (phi v1) (phi u1) (phi a4) (phi a3)
        (phi a2) (phi a1) (phi a0) (phi s1) (phi w1) (phi b62) (phi b5)
        (phi b4) (phi b3) (phi b2) (phi b1) (phi lambda) := by
  simp only [degreeZeroOrder118Plus810, degreeZeroOrder118PlusBlock0_810, degreeZeroOrder118PlusBlock1_810, degreeZeroOrder118PlusBlock2_810, degreeZeroOrder118PlusBlock3_810, degreeZeroOrder118PlusBlock4_810, degreeZeroOrder118PlusBlock5_810, degreeZeroOrder118PlusBlock6_810, degreeZeroOrder118PlusBlock7_810, degreeZeroOrder118PlusBlock8_810, degreeZeroOrder118PlusBlock9_810, degreeZeroOrder118PlusBlock10_810, degreeZeroOrder118PlusBlock11_810, degreeZeroOrder118PlusBlock12_810, degreeZeroOrder118PlusBlock13_810, degreeZeroOrder118PlusBlock14_810, degreeZeroOrder118PlusBlock15_810, degreeZeroOrder118PlusBlock16_810, degreeZeroOrder118PlusBlock17_810, degreeZeroOrder118PlusBlock18_810, degreeZeroOrder118PlusBlock19_810, degreeZeroOrder118PlusBlock20_810, degreeZeroOrder118PlusBlock21_810, degreeZeroOrder118PlusBlock22_810, degreeZeroOrder118PlusBlock23_810, degreeZeroOrder118PlusBlock24_810, map_add, map_sub, map_mul,
    map_pow, map_neg, map_ofNat, map_zero]

end DegreeZeroTowerCeilingMap810

section DegreeZeroTowerCeilingEval810

variable {k : Type*} [CommRing k]


theorem degreeZeroOrder111810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (degreeZeroOrder111810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      degreeZeroOrder111810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_degreeZeroOrder111810 (Polynomial.evalRingHom a)
      t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)


theorem degreeZeroOrder112810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (degreeZeroOrder112810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      degreeZeroOrder112810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_degreeZeroOrder112810 (Polynomial.evalRingHom a)
      t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)


theorem degreeZeroOrder113810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (degreeZeroOrder113810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      degreeZeroOrder113810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_degreeZeroOrder113810 (Polynomial.evalRingHom a)
      t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)


theorem degreeZeroOrder114810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (degreeZeroOrder114810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      degreeZeroOrder114810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_degreeZeroOrder114810 (Polynomial.evalRingHom a)
      t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)


theorem degreeZeroOrder115810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (degreeZeroOrder115810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      degreeZeroOrder115810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_degreeZeroOrder115810 (Polynomial.evalRingHom a)
      t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)


theorem degreeZeroOrder116810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (degreeZeroOrder116810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      degreeZeroOrder116810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_degreeZeroOrder116810 (Polynomial.evalRingHom a)
      t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)


theorem degreeZeroOrder117810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (degreeZeroOrder117810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      degreeZeroOrder117810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_degreeZeroOrder117810 (Polynomial.evalRingHom a)
      t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)


theorem degreeZeroOrder118810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (degreeZeroOrder118810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      degreeZeroOrder118810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_degreeZeroOrder118810 (Polynomial.evalRingHom a)
      t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)


theorem degreeZeroOrder118Plus810_eval
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (degreeZeroOrder118Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      degreeZeroOrder118Plus810 (h.eval a) (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_degreeZeroOrder118Plus810 (Polynomial.evalRingHom a) h
      t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)

#print axioms degreeZeroOrder111810_eval
#print axioms degreeZeroOrder118Plus810_eval

end DegreeZeroTowerCeilingEval810

/-! ## Pole obstruction and `h₀`-divisibility

Each named coefficient is the `h^{k-102}` term of
`degreeZeroSourceJetQuotient810`.  If the remaining numerator after
cancelling `h₀^{k-102}` evaluates to that named coefficient, the
remaining-pole obstruction forces it to vanish.  After order `118` the
remaining pole is `1`.  The four scalar load solves are not inserted.
The clearing identity itself remains a hypothesis.
-/

section DegreeZeroTowerCeilingHeads810

variable {k : Type*} [Field k] [CharZero k]


/-- Named `h^9` coefficient of the order-`102` quotient, forced if
it is the remaining pole-`8` head after cancelling `h₀^9`. -/
theorem degreeZeroOrder111810_zero_of_remaining_pole
    (h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^
            degreeZeroEffectiveTowerLength810 *
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)))
    (hderiv :
      Differential.deriv
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (Q : k[X])
    (hfact :
      degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        h0 ^ 9 * Q)
    (hhead : Q.eval a = degreeZeroOrder111810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) :
    degreeZeroOrder111810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^ (9 + 8) *
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) := by
    have hpow : degreeZeroEffectiveTowerLength810 = 9 + 8 := rfl
    rwa [hpow] at hclear
  exact degreeZero_remainingHead_eval_zero810 h0
    (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda))
    Q ((degreeZeroClearedIntegerScale810 : RatFunc k) *
        sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda))
    j a (degreeZeroOrder111810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) 9 8 (by decide) hh0
    hdegree hroot hfact hhead hclear_mn hderiv

#print axioms degreeZeroOrder111810_zero_of_remaining_pole

/-- Named `h^10` coefficient of the order-`102` quotient, forced if
it is the remaining pole-`7` head after cancelling `h₀^10`. -/
theorem degreeZeroOrder112810_zero_of_remaining_pole
    (h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^
            degreeZeroEffectiveTowerLength810 *
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)))
    (hderiv :
      Differential.deriv
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (Q : k[X])
    (hfact :
      degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        h0 ^ 10 * Q)
    (hhead : Q.eval a = degreeZeroOrder112810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) :
    degreeZeroOrder112810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^ (10 + 7) *
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) := by
    have hpow : degreeZeroEffectiveTowerLength810 = 10 + 7 := rfl
    rwa [hpow] at hclear
  exact degreeZero_remainingHead_eval_zero810 h0
    (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda))
    Q ((degreeZeroClearedIntegerScale810 : RatFunc k) *
        sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda))
    j a (degreeZeroOrder112810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) 10 7 (by decide) hh0
    hdegree hroot hfact hhead hclear_mn hderiv

#print axioms degreeZeroOrder112810_zero_of_remaining_pole

/-- Named `h^11` coefficient of the order-`102` quotient, forced if
it is the remaining pole-`6` head after cancelling `h₀^11`. -/
theorem degreeZeroOrder113810_zero_of_remaining_pole
    (h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^
            degreeZeroEffectiveTowerLength810 *
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)))
    (hderiv :
      Differential.deriv
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (Q : k[X])
    (hfact :
      degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        h0 ^ 11 * Q)
    (hhead : Q.eval a = degreeZeroOrder113810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) :
    degreeZeroOrder113810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^ (11 + 6) *
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) := by
    have hpow : degreeZeroEffectiveTowerLength810 = 11 + 6 := rfl
    rwa [hpow] at hclear
  exact degreeZero_remainingHead_eval_zero810 h0
    (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda))
    Q ((degreeZeroClearedIntegerScale810 : RatFunc k) *
        sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda))
    j a (degreeZeroOrder113810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) 11 6 (by decide) hh0
    hdegree hroot hfact hhead hclear_mn hderiv

#print axioms degreeZeroOrder113810_zero_of_remaining_pole

/-- Named `h^12` coefficient of the order-`102` quotient, forced if
it is the remaining pole-`5` head after cancelling `h₀^12`. -/
theorem degreeZeroOrder114810_zero_of_remaining_pole
    (h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^
            degreeZeroEffectiveTowerLength810 *
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)))
    (hderiv :
      Differential.deriv
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (Q : k[X])
    (hfact :
      degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        h0 ^ 12 * Q)
    (hhead : Q.eval a = degreeZeroOrder114810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) :
    degreeZeroOrder114810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^ (12 + 5) *
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) := by
    have hpow : degreeZeroEffectiveTowerLength810 = 12 + 5 := rfl
    rwa [hpow] at hclear
  exact degreeZero_remainingHead_eval_zero810 h0
    (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda))
    Q ((degreeZeroClearedIntegerScale810 : RatFunc k) *
        sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda))
    j a (degreeZeroOrder114810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) 12 5 (by decide) hh0
    hdegree hroot hfact hhead hclear_mn hderiv

#print axioms degreeZeroOrder114810_zero_of_remaining_pole

/-- Named `h^13` coefficient of the order-`102` quotient, forced if
it is the remaining pole-`4` head after cancelling `h₀^13`. -/
theorem degreeZeroOrder115810_zero_of_remaining_pole
    (h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^
            degreeZeroEffectiveTowerLength810 *
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)))
    (hderiv :
      Differential.deriv
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (Q : k[X])
    (hfact :
      degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        h0 ^ 13 * Q)
    (hhead : Q.eval a = degreeZeroOrder115810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) :
    degreeZeroOrder115810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^ (13 + 4) *
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) := by
    have hpow : degreeZeroEffectiveTowerLength810 = 13 + 4 := rfl
    rwa [hpow] at hclear
  exact degreeZero_remainingHead_eval_zero810 h0
    (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda))
    Q ((degreeZeroClearedIntegerScale810 : RatFunc k) *
        sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda))
    j a (degreeZeroOrder115810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) 13 4 (by decide) hh0
    hdegree hroot hfact hhead hclear_mn hderiv

#print axioms degreeZeroOrder115810_zero_of_remaining_pole

/-- Named `h^14` coefficient of the order-`102` quotient, forced if
it is the remaining pole-`3` head after cancelling `h₀^14`. -/
theorem degreeZeroOrder116810_zero_of_remaining_pole
    (h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^
            degreeZeroEffectiveTowerLength810 *
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)))
    (hderiv :
      Differential.deriv
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (Q : k[X])
    (hfact :
      degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        h0 ^ 14 * Q)
    (hhead : Q.eval a = degreeZeroOrder116810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) :
    degreeZeroOrder116810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^ (14 + 3) *
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) := by
    have hpow : degreeZeroEffectiveTowerLength810 = 14 + 3 := rfl
    rwa [hpow] at hclear
  exact degreeZero_remainingHead_eval_zero810 h0
    (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda))
    Q ((degreeZeroClearedIntegerScale810 : RatFunc k) *
        sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda))
    j a (degreeZeroOrder116810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) 14 3 (by decide) hh0
    hdegree hroot hfact hhead hclear_mn hderiv

#print axioms degreeZeroOrder116810_zero_of_remaining_pole

/-- Named `h^15` coefficient of the order-`102` quotient, forced if
it is the remaining pole-`2` head after cancelling `h₀^15`. -/
theorem degreeZeroOrder117810_zero_of_remaining_pole
    (h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^
            degreeZeroEffectiveTowerLength810 *
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)))
    (hderiv :
      Differential.deriv
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (Q : k[X])
    (hfact :
      degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        h0 ^ 15 * Q)
    (hhead : Q.eval a = degreeZeroOrder117810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) :
    degreeZeroOrder117810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^ (15 + 2) *
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) := by
    have hpow : degreeZeroEffectiveTowerLength810 = 15 + 2 := rfl
    rwa [hpow] at hclear
  exact degreeZero_remainingHead_eval_zero810 h0
    (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda))
    Q ((degreeZeroClearedIntegerScale810 : RatFunc k) *
        sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda))
    j a (degreeZeroOrder117810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) 15 2 (by decide) hh0
    hdegree hroot hfact hhead hclear_mn hderiv

#print axioms degreeZeroOrder117810_zero_of_remaining_pole

/-- Named `h^16` coefficient of the order-`102` quotient, forced if
it is the remaining pole-`1` head after cancelling `h₀^16`. -/
theorem degreeZeroOrder118810_zero_of_remaining_pole
    (h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^
            degreeZeroEffectiveTowerLength810 *
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)))
    (hderiv :
      Differential.deriv
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (Q : k[X])
    (hfact :
      degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        h0 ^ 16 * Q)
    (hhead : Q.eval a = degreeZeroOrder118810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) :
    degreeZeroOrder118810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^ (16 + 1) *
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) := by
    have hpow : degreeZeroEffectiveTowerLength810 = 16 + 1 := rfl
    rwa [hpow] at hclear
  exact degreeZero_remainingHead_eval_zero810 h0
    (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda))
    Q ((degreeZeroClearedIntegerScale810 : RatFunc k) *
        sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda))
    j a (degreeZeroOrder118810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) 16 1 (by decide) hh0
    hdegree hroot hfact hhead hclear_mn hderiv

#print axioms degreeZeroOrder118810_zero_of_remaining_pole

set_option maxHeartbeats 1600000000 in
/-- Remaining-numerator peels of orders `111` through `118`.  After
order `118` the remaining pole is `1`.  This is not a closure. -/
theorem degreeZero_orders111to118_remaining_dvd810
    (h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^
            degreeZeroEffectiveTowerLength810 *
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)))
    (hderiv :
      Differential.deriv
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ Q110 Q111 Q112 Q113 Q114 Q115 Q116 Q117 Q118 : k[X],
      degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        h0 ^ 8 * Q110 ∧ Q110.eval a = 0 ∧
      Q110 = h0 * Q111 ∧ Q111.eval a = 0 ∧
      Q111 = h0 * Q112 ∧ Q112.eval a = 0 ∧
      Q112 = h0 * Q113 ∧ Q113.eval a = 0 ∧
      Q113 = h0 * Q114 ∧ Q114.eval a = 0 ∧
      Q114 = h0 * Q115 ∧ Q115.eval a = 0 ∧
      Q115 = h0 * Q116 ∧ Q116.eval a = 0 ∧
      Q116 = h0 * Q117 ∧ Q117.eval a = 0 ∧
      Q117 = h0 * Q118 ∧ Q118.eval a = 0 ∧
      h0 ∣ Q118 := by
  let rho : RatFunc k :=
    (degreeZeroClearedIntegerScale810 : RatFunc k) *
      sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)
  have hclear17 :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^ 17 *
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) := by
    have hpow : degreeZeroEffectiveTowerLength810 = 17 := rfl
    rwa [hpow] at hclear
  have hclear17' :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^ 17 * rho :=
    hclear17
  have hderiv' :
      Differential.deriv rho =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0 :=
    hderiv
  obtain ⟨Q103, Q104, Q105, Q106, Q107, Q108, Q109, Q110, h103f, h103z,
      h104f, h104z, h105f, h105z, h106f, h106z, h107f, h107z, h108f,
      h108z, h109f, h109z, h110f, h110z, _hdvd110⟩ :=
    degreeZero_orders103to110_remaining_dvd810 h0 t0 v1 u1 a4 a3 a2 a1
      a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda j a hh0 hdegree hroot hclear
      hderiv
  have hjet8 :
      degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        h0 ^ 8 * Q110 := by
    simp only [h103f, h104f, h105f, h106f, h107f, h108f, h109f, h110f]
    ring
  have hclear9 :
      algebraMap k[X] (RatFunc k) Q110 =
        (algebraMap k[X] (RatFunc k) h0) ^ (8 + 1) * rho :=
    degreeZero_algebraMap_cancel_pow810 h0 Q110 rho 8 9 hh0
      (by
        have hpow : (8 + 9 : ℕ) = 17 := rfl
        rw [← hjet8, hpow]
        exact hclear17')
  obtain ⟨Q111, h111f, hclear8, h111z, _hdvd111⟩ :=
    degreeZero_remainingNumerator_succ_dvd810 h0 Q110 rho j a 8
      (by decide) hh0 hdegree hroot h110z hclear9 hderiv'
  obtain ⟨Q112, h112f, hclear7, h112z, _hdvd112⟩ :=
    degreeZero_remainingNumerator_succ_dvd810 h0 Q111 rho j a 7
      (by decide) hh0 hdegree hroot h111z hclear8 hderiv'
  obtain ⟨Q113, h113f, hclear6, h113z, _hdvd113⟩ :=
    degreeZero_remainingNumerator_succ_dvd810 h0 Q112 rho j a 6
      (by decide) hh0 hdegree hroot h112z hclear7 hderiv'
  obtain ⟨Q114, h114f, hclear5, h114z, _hdvd114⟩ :=
    degreeZero_remainingNumerator_succ_dvd810 h0 Q113 rho j a 5
      (by decide) hh0 hdegree hroot h113z hclear6 hderiv'
  obtain ⟨Q115, h115f, hclear4, h115z, _hdvd115⟩ :=
    degreeZero_remainingNumerator_succ_dvd810 h0 Q114 rho j a 4
      (by decide) hh0 hdegree hroot h114z hclear5 hderiv'
  obtain ⟨Q116, h116f, hclear3, h116z, _hdvd116⟩ :=
    degreeZero_remainingNumerator_succ_dvd810 h0 Q115 rho j a 3
      (by decide) hh0 hdegree hroot h115z hclear4 hderiv'
  obtain ⟨Q117, h117f, hclear2, h117z, _hdvd117⟩ :=
    degreeZero_remainingNumerator_succ_dvd810 h0 Q116 rho j a 2
      (by decide) hh0 hdegree hroot h116z hclear3 hderiv'
  obtain ⟨Q118, h118f, hclear1, h118z, hdvd118⟩ :=
    degreeZero_remainingNumerator_succ_dvd810 h0 Q117 rho j a 1
      (by decide) hh0 hdegree hroot h117z hclear2 hderiv'
  exact ⟨Q110, Q111, Q112, Q113, Q114, Q115, Q116, Q117, Q118, hjet8, h110z, h111f, h111z, h112f, h112z, h113f, h113z, h114f, h114z, h115f, h115z, h116f, h116z, h117f, h117z, h118f, h118z, hdvd118⟩

#print axioms degreeZero_orders111to118_remaining_dvd810

/-- Batch `h₀^{16}`-divisibility of the order-`102` quotient through
order `118`.  Remaining pole `1`. -/
theorem degreeZero_orders111to118_pow_dvd810
    (h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^
            degreeZeroEffectiveTowerLength810 *
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)))
    (hderiv :
      Differential.deriv
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    h0 ^ degreeZeroTowerDivisibilityAfter118810 ∣
      degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
  obtain ⟨Q110, Q111, Q112, Q113, Q114, Q115, Q116, Q117, Q118, hjet8, _h110z, h111f, _h111z, h112f, _h112z, h113f, _h113z, h114f, _h114z, h115f, _h115z, h116f, _h116z, h117f, _h117z, h118f, _h118z, _hdvd118⟩ :=
    degreeZero_orders111to118_remaining_dvd810 h0 t0 v1 u1 a4 a3 a2 a1
      a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda j a hh0 hdegree hroot hclear
      hderiv
  refine ⟨Q118, ?_⟩
  simp only [degreeZeroTowerDivisibilityAfter118810, hjet8, h111f,
    h112f, h113f, h114f, h115f, h116f, h117f, h118f]
  ring

#print axioms degreeZero_orders111to118_pow_dvd810

/-- The specialised jet, as a pole-`17` numerator of a simple-pole
rational function, is divisible by `h₀^{17}`. -/
theorem degreeZeroSourceJetQuotient810_pow_seventeen_dvd
    (h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^
            degreeZeroEffectiveTowerLength810 *
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)))
    (hderiv :
      Differential.deriv
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    h0 ^ degreeZeroTowerCeilingDivisibility810 ∣
      degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
  let rho : RatFunc k :=
    (degreeZeroClearedIntegerScale810 : RatFunc k) *
      sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)
  have hclear17 :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^ 17 *
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) := by
    have hpow : degreeZeroEffectiveTowerLength810 = 17 := rfl
    rwa [hpow] at hclear
  have hclear17' :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^ 17 * rho :=
    hclear17
  have hderiv' :
      Differential.deriv rho =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0 :=
    hderiv
  simpa [degreeZeroTowerCeilingDivisibility810] using
    degreeZero_pow_dvd_of_remaining_pole810 h0
      (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda))
      rho j a 17 hh0 hdegree hroot hclear17' hderiv'

#print axioms degreeZeroSourceJetQuotient810_pow_seventeen_dvd

/-- Cancel-and-expose on the specialised jet, under the parent pole-`17`
clearing and `j ≠ 0`.  Frozen exhaustion is `h₀^{17}`; the remaining
factor is `rho` and `j ≠ 0` is impossible.  The source-primitive
identity is not re-proved here. -/
theorem degreeZeroFace810_linearRoot_order118Ceiling
    (h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda j a : k) (hh0 : h0 ≠ 0) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0)
    (hclear :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^
            degreeZeroEffectiveTowerLength810 *
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)))
    (hderiv :
      Differential.deriv
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0)
    (hj : j ≠ 0) : False := by
  let rho : RatFunc k :=
    (degreeZeroClearedIntegerScale810 : RatFunc k) *
      sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)
  have hclear17 :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^ 17 *
          ((degreeZeroClearedIntegerScale810 : RatFunc k) *
            sourceRhoResidualLeftJet810
              (algebraMap k[X] (RatFunc k) h0)
              (algebraMap k[X] (RatFunc k) t0)
              (algebraMap k[X] (RatFunc k) v1)
              (algebraMap k[X] (RatFunc k) u1)
              (algebraMap k[X] (RatFunc k) a4)
              (algebraMap k[X] (RatFunc k) a3)
              (algebraMap k[X] (RatFunc k) a2)
              (algebraMap k[X] (RatFunc k) a1)
              (algebraMap k[X] (RatFunc k) a0)
              (algebraMap k[X] (RatFunc k) s1)
              (algebraMap k[X] (RatFunc k) w1)
              (algebraMap k[X] (RatFunc k) b62)
              (algebraMap k[X] (RatFunc k) b5)
              (algebraMap k[X] (RatFunc k) b4)
              (algebraMap k[X] (RatFunc k) b3)
              (algebraMap k[X] (RatFunc k) b2)
              (algebraMap k[X] (RatFunc k) b1) (RatFunc.C lambda)) := by
    have hpow : degreeZeroEffectiveTowerLength810 = 17 := rfl
    rwa [hpow] at hclear
  have hclear17' :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^ 17 * rho :=
    hclear17
  have hderiv' :
      Differential.deriv rho =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0 :=
    hderiv
  obtain ⟨Q, hQ⟩ :=
    degreeZeroSourceJetQuotient810_pow_seventeen_dvd h0 t0 v1 u1 a4 a3
      a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda j a hh0 hdegree hroot
      hclear hderiv
  exact degreeZero_of_pow_dvd_simplePole_ne_zero810 a j h0
    (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda))
    Q rho 17 hh0 hroot hQ hclear17' hderiv' hj

#print axioms degreeZeroFace810_linearRoot_order118Ceiling

end DegreeZeroTowerCeilingHeads810

end Max11DegreeRoutes
