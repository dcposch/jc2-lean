import Grok810DegreeZeroSourceNumeratorScratch

/-! # Orders `103` through `110` of the `(8,10)` degree-zero bounded tower

Untracked working note.  No tracked file was edited.

`Grok810DegreeZeroSourceNumeratorScratch` established the `h^{119}`-cleared
source numerator (`977` terms, scale `2^{62}`), the six unsolved Pi-tower
substitutions, base order `102`, remaining pole `17 = 119 - 102`, and the
order-`102` head (`244` terms).  The head vanishes at a linear root of `h₀`
by `degreeZeroSourceJetHead810_zero_of_deriv_eq_simplePole`, consuming the
Z4 interfaces `localLinearPoleOne_head_eval_zero_of_deriv_eq_simplePole810`
and `algebraMap_cancel_one_of_one_clearing810`.  A parallel lane
(`Grok810DegreeZeroClearingDischargeScratch`) discharges the remaining-`17`
clearing; this file keeps `hclear` / `hderiv` as hypotheses exactly as the
parent does.

Each order `k ∈ {103,…,110}` is the `h^{k-102}` coefficient of the
cleared numerator quotient `Head + h · Plus`.  Vanishing of a remaining
numerator that evaluates to that named coefficient is recorded by
`degreeZeroOrder{k}810_zero_of_remaining_pole`.  The batch
`h₀`-divisibility
`degreeZero_orders103to110_remaining_dvd810` peels eight remaining
numerators from the pole-`17` quotient, leaving remaining pole `9`.
The next unused compact-numerator order is `111`.  No chamber is closed.

CAS: `derive_810_degree_zero_tower_orders103to110.py` /
`emit_810_degree_zero_tower_orders103to110_lean.py`.  No `sorry`, no new
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

/-! ## Bookkeeping: orders `103`–`110`, remaining pole `9` -/

/-- Last compact-numerator order extracted in this batch. -/
def degreeZeroTowerBatchLastOrder810 : ℕ := 110

/-- Next unused compact-numerator order after this batch. -/
def degreeZeroTowerNextUnusedOrder810 : ℕ := 111

/-- Remaining pole of the order-`102` quotient after orders `103`–`110`:
`17 - 8 = 9`, equivalently `119 - 110`. -/
def degreeZeroRemainingPoleAfter110810 : ℕ := 9

/-- Vanishing multiplicity recorded by this batch on the order-`102`
quotient: eight remaining-numerator peels. -/
def degreeZeroTowerBatchDivisibility810 : ℕ := 8

theorem degreeZeroTowerBatchLastOrder810_eq :
    degreeZeroTowerBatchLastOrder810 = 110 :=
  rfl

theorem degreeZeroTowerNextUnusedOrder810_eq :
    degreeZeroTowerNextUnusedOrder810 = 111 :=
  rfl

theorem degreeZeroRemainingPoleAfter110810_eq :
    degreeZeroRemainingPoleAfter110810 = 9 :=
  rfl

theorem degreeZeroTowerBatchDivisibility810_eq :
    degreeZeroTowerBatchDivisibility810 = 8 :=
  rfl

theorem degreeZeroTowerNextUnusedOrder810_succ :
    degreeZeroTowerNextUnusedOrder810 =
      degreeZeroTowerBatchLastOrder810 + 1 :=
  rfl

theorem degreeZeroRemainingPoleAfter110810_eq_sub_batch :
    degreeZeroRemainingPoleAfter110810 =
      degreeZeroEffectiveTowerLength810 -
        degreeZeroTowerBatchDivisibility810 :=
  rfl

theorem degreeZeroRemainingPoleAfter110810_eq_sub_clearing :
    degreeZeroRemainingPoleAfter110810 =
      degreeZeroSourceClearingPower810 -
        degreeZeroTowerBatchLastOrder810 :=
  rfl

theorem degreeZeroTowerBatchLastOrder810_lt_ceiling :
    degreeZeroTowerBatchLastOrder810 < degreeZeroTowerCeiling810 := by
  decide

theorem degreeZeroRemainingPoleAfter110810_ne_zero :
    degreeZeroRemainingPoleAfter110810 ≠ 0 := by
  decide

#print axioms degreeZeroRemainingPoleAfter110810_eq_sub_batch
#print axioms degreeZeroRemainingPoleAfter110810_eq_sub_clearing
#print axioms degreeZeroTowerBatchLastOrder810_lt_ceiling

/-! ## Linear divisibility and clearing cancellation -/

section DegreeZeroTowerDvd810

variable {k : Type*} [Field k]

/-- A degree-one polynomial divides every polynomial vanishing at its
unique root. -/
theorem degreeZero_linearPolynomial_dvd_of_eval_eq_zero810
    (h0 f : k[X]) (a : k) (hdegree : h0.natDegree = 1)
    (hroot : h0.eval a = 0) (hf : f.eval a = 0) : h0 ∣ f := by
  have hlinearRoot : X - C a ∣ f := Polynomial.dvd_iff_isRoot.mpr hf
  obtain ⟨c, hc, d, hlinear⟩ := Polynomial.natDegree_eq_one.mp hdegree
  have hca : c * a + d = 0 := by simpa [← hlinear] using hroot
  have hd : d = -(c * a) := by linear_combination hca
  have hfactor : h0 = C c * (X - C a) := by
    calc
      h0 = C c * X + C d := hlinear.symm
      _ = C c * X - C (c * a) := by rw [hd, map_neg]; ring
      _ = C c * (X - C a) := by rw [mul_sub, ← map_mul]
  have hscaleDvd : h0 ∣ X - C a := by
    refine ⟨C c⁻¹, ?_⟩
    rw [hfactor]
    calc
      X - C a = 1 * (X - C a) := by rw [one_mul]
      _ = (C c * C c⁻¹) * (X - C a) := by
        rw [← map_mul, mul_inv_cancel₀ hc, map_one]
      _ = C c * (X - C a) * C c⁻¹ := by ring
  exact hscaleDvd.trans hlinearRoot

/-- Cancel `m` polynomial powers from a pole-`(m+n)` clearing. -/
theorem degreeZero_algebraMap_cancel_pow810
    (h0 Q : k[X]) (rho : RatFunc k) (m n : ℕ) (hh0 : h0 ≠ 0)
    (hclear :
      algebraMap k[X] (RatFunc k) (h0 ^ m * Q) =
        (algebraMap k[X] (RatFunc k) h0) ^ (m + n) * rho) :
    algebraMap k[X] (RatFunc k) Q =
      (algebraMap k[X] (RatFunc k) h0) ^ n * rho := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  have hhRF : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  apply mul_left_cancel₀ (pow_ne_zero m hhRF)
  have hmapPow :
      algebraMap k[X] (RatFunc k) (h0 ^ m * Q) =
        hRF ^ m * algebraMap k[X] (RatFunc k) Q := by
    simp only [hRF, map_mul, map_pow]
  calc
    hRF ^ m * algebraMap k[X] (RatFunc k) Q =
        algebraMap k[X] (RatFunc k) (h0 ^ m * Q) := hmapPow.symm
    _ = hRF ^ (m + n) * rho := hclear
    _ = hRF ^ m * (hRF ^ n * rho) := by
      rw [pow_add]
      ring

/-- Cancel one polynomial power of a linear clearing. -/
theorem degreeZero_algebraMap_cancel_one_clearing810
    (h0 old new : k[X]) (rho : RatFunc k) (r : ℕ) (hh0 : h0 ≠ 0)
    (hfact : old = h0 * new)
    (hclear : algebraMap k[X] (RatFunc k) old =
      (algebraMap k[X] (RatFunc k) h0) ^ (r + 1) * rho) :
    algebraMap k[X] (RatFunc k) new =
      (algebraMap k[X] (RatFunc k) h0) ^ r * rho :=
  degreeZero_algebraMap_cancel_pow810 h0 new rho 1 r hh0
    (by
      have hclear' :
          algebraMap k[X] (RatFunc k) (h0 * new) =
            (algebraMap k[X] (RatFunc k) h0) ^ (1 + r) * rho := by
        simpa [hfact, add_comm r 1] using hclear
      simpa [pow_one] using hclear')

/-- Evaluation of a remaining numerator `c₀ + h₀ · rest` at a root of
the linear scale is the head `c₀`. -/
theorem degreeZero_eval_head_of_linear_factor810
    (h0 c0 rest : k[X]) (a : k) (hroot : h0.eval a = 0) :
    (c0 + h0 * rest).eval a = c0.eval a := by
  simp [Polynomial.eval_add, Polynomial.eval_mul, hroot, zero_mul,
    add_zero]

#print axioms degreeZero_linearPolynomial_dvd_of_eval_eq_zero810
#print axioms degreeZero_algebraMap_cancel_pow810
#print axioms degreeZero_algebraMap_cancel_one_clearing810
#print axioms degreeZero_eval_head_of_linear_factor810

end DegreeZeroTowerDvd810

/-! ## Remaining-head obstruction after cancelling `m` powers -/

section DegreeZeroTowerRemainingHead810

variable {k : Type*} [Field k] [CharZero k]

/-- Cancel `m` polynomial powers from a pole-`(m+n)` clearing and apply
the remaining pole-`n` obstruction.  Instantiating `m = 0` and `n = 17`
recovers `degreeZeroSourceJetHead810_zero_of_deriv_eq_simplePole` on the
order-`102` quotient. -/
theorem degreeZero_remainingHead_eval_zero810
    (h0 A0 Q : k[X]) (rho : RatFunc k) (j a head : k) (m n : ℕ)
    (hn : n ≠ 0) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hfact : A0 = h0 ^ m * Q) (hhead : Q.eval a = head)
    (hclear : algebraMap k[X] (RatFunc k) A0 =
      (algebraMap k[X] (RatFunc k) h0) ^ (m + n) * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    head = 0 := by
  have hclearQ :
      algebraMap k[X] (RatFunc k) Q =
        (algebraMap k[X] (RatFunc k) h0) ^ n * rho :=
    degreeZero_algebraMap_cancel_pow810 h0 Q rho m n hh0
      (by simpa [hfact] using hclear)
  have hQ0 : Q.eval a = 0 :=
    localLinearPole_head_eval_zero_of_deriv_eq_simplePole810 n hn a j
      h0 Q rho hdegree hroot hclearQ hderiv
  exact hhead.symm.trans hQ0

/-- If a remaining pole-`(r+1)` numerator vanishes at the linear root,
one more linear factor cancels and the pole-`r` obstruction forces the
new remaining numerator to vanish. -/
theorem degreeZero_remainingNumerator_succ_dvd810
    (h0 Qold : k[X]) (rho : RatFunc k) (j a : k) (r : ℕ)
    (hr : r ≠ 0) (hh0 : h0 ≠ 0)
    (hdegree : h0.natDegree = 1) (hroot : h0.eval a = 0)
    (hQold : Qold.eval a = 0)
    (hclear : algebraMap k[X] (RatFunc k) Qold =
      (algebraMap k[X] (RatFunc k) h0) ^ (r + 1) * rho)
    (hderiv : Differential.deriv rho =
      RatFunc.C j / algebraMap k[X] (RatFunc k) h0) :
    ∃ Qnew : k[X],
      Qold = h0 * Qnew ∧
        algebraMap k[X] (RatFunc k) Qnew =
          (algebraMap k[X] (RatFunc k) h0) ^ r * rho ∧
        Qnew.eval a = 0 ∧ h0 ∣ Qnew := by
  obtain ⟨Qnew, hfact⟩ :=
    degreeZero_linearPolynomial_dvd_of_eval_eq_zero810 h0 Qold a
      hdegree hroot hQold
  have hclear' :
      algebraMap k[X] (RatFunc k) Qnew =
        (algebraMap k[X] (RatFunc k) h0) ^ r * rho :=
    degreeZero_algebraMap_cancel_one_clearing810 h0 Qold Qnew rho r
      hh0 hfact hclear
  have hzero : Qnew.eval a = 0 :=
    localLinearPole_head_eval_zero_of_deriv_eq_simplePole810 r hr a j
      h0 Qnew rho hdegree hroot hclear' hderiv
  exact ⟨Qnew, hfact, hclear', hzero,
    degreeZero_linearPolynomial_dvd_of_eval_eq_zero810 h0 Qnew a
      hdegree hroot hzero⟩

#print axioms degreeZero_remainingHead_eval_zero810
#print axioms degreeZero_remainingNumerator_succ_dvd810

end DegreeZeroTowerRemainingHead810

/-! ## Order `103` (quotient `h^1`, Plus `h^0`) -/

/-- Order-`103` contribution of Plus block `0`. -/
def degreeZeroOrder103Block0_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`103` contribution of Plus block `1`. -/
def degreeZeroOrder103Block1_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`103` contribution of Plus block `2`. -/
def degreeZeroOrder103Block2_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (129197014310191104 : R) * a4 ^ 4 * lambda

/-- Order-`103` contribution of Plus block `3`. -/
def degreeZeroOrder103Block3_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`103` contribution of Plus block `4`. -/
def degreeZeroOrder103Block4_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`103` contribution of Plus block `5`. -/
def degreeZeroOrder103Block5_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1614962678877388800 : R) * t0 * u1 * a4 ^ 3 * lambda
    - (807481339438694400 : R) * v1 ^ 2 * a4 ^ 3 * lambda
    - (2422444018316083200 : R) * v1 * u1 ^ 2 * a4 ^ 2 * lambda
    - (403740669719347200 : R) * u1 ^ 4 * a4 * lambda

/-- Order-`103` contribution of Plus block `6`. -/
def degreeZeroOrder103Block6_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`103` contribution of Plus block `7`. -/
def degreeZeroOrder103Block7_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`103` contribution of Plus block `8`. -/
def degreeZeroOrder103Block8_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`103` contribution of Plus block `9`. -/
def degreeZeroOrder103Block9_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (3330860525184614400 : R) * t0 ^ 2 * v1 * a4 ^ 3 * lambda
    + (4996290787776921600 : R) * t0 ^ 2 * u1 ^ 2 * a4 ^ 2 * lambda
    + (9992581575553843200 : R) * t0 * v1 ^ 2 * u1 * a4 ^ 2 * lambda
    + (6661721050369228800 : R) * t0 * v1 * u1 ^ 3 * a4 * lambda
    + (333086052518461440 : R) * t0 * u1 ^ 5 * lambda
    + (832715131296153600 : R) * v1 ^ 4 * a4 ^ 2 * lambda
    + (3330860525184614400 : R) * v1 ^ 3 * u1 ^ 2 * a4 * lambda
    + (832715131296153600 : R) * v1 ^ 2 * u1 ^ 4 * lambda

/-- Order-`103` contribution of Plus block `10`. -/
def degreeZeroOrder103Block10_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`103` contribution of Plus block `11`. -/
def degreeZeroOrder103Block11_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`103` contribution of Plus block `12`. -/
def degreeZeroOrder103Block12_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

set_option maxHeartbeats 200000000 in
/-- Order-`103` contribution of Plus block `13`. -/
def degreeZeroOrder103Block13_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1422555015964262400 : R) * t0 ^ 4 * a4 ^ 3 * lambda
    - (17070660191571148800 : R) * t0 ^ 3 * v1 * u1 * a4 ^ 2 * lambda
    - (5690220063857049600 : R) * t0 ^ 3 * u1 ^ 3 * a4 * lambda
    - (8535330095785574400 : R) * t0 ^ 2 * v1 ^ 3 * a4 ^ 2 * lambda
    - (25605990287356723200 : R) * t0 ^ 2 * v1 ^ 2 * u1 ^ 2 * a4 * lambda
    - (4267665047892787200 : R) * t0 ^ 2 * v1 * u1 ^ 4 * lambda
    - (8535330095785574400 : R) * t0 * v1 ^ 4 * u1 * a4 * lambda
    - (5690220063857049600 : R) * t0 * v1 ^ 3 * u1 ^ 3 * lambda
    - (284511003192852480 : R) * v1 ^ 6 * a4 * lambda
    - (853533009578557440 : R) * v1 ^ 5 * u1 ^ 2 * lambda

/-- Order-`103` contribution of Plus block `14`. -/
def degreeZeroOrder103Block14_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`103` contribution of Plus block `15`. -/
def degreeZeroOrder103Block15_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`103` contribution of Plus block `16`. -/
def degreeZeroOrder103Block16_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (5227889683668664320 : R) * t0 ^ 5 * u1 * a4 ^ 2 * lambda
    + (13069724209171660800 : R) * t0 ^ 4 * v1 ^ 2 * a4 ^ 2 * lambda
    + (26139448418343321600 : R) * t0 ^ 4 * v1 * u1 ^ 2 * a4 * lambda
    + (2178287368195276800 : R) * t0 ^ 4 * u1 ^ 4 * lambda
    + (34852597891124428800 : R) * t0 ^ 3 * v1 ^ 3 * u1 * a4 * lambda
    + (17426298945562214400 : R) * t0 ^ 3 * v1 ^ 2 * u1 ^ 3 * lambda

/-- Order-`103` contribution of Plus block `17`. -/
def degreeZeroOrder103Block17_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (5227889683668664320 : R) * t0 ^ 2 * v1 ^ 5 * a4 * lambda
    + (13069724209171660800 : R) * t0 ^ 2 * v1 ^ 4 * u1 ^ 2 * lambda
    + (1742629894556221440 : R) * t0 * v1 ^ 6 * u1 * lambda
    + (31118390974218240 : R) * v1 ^ 8 * lambda

/-- Order-`103` contribution of Plus block `18`. -/
def degreeZeroOrder103Block18_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`103` contribution of Plus block `19`. -/
def degreeZeroOrder103Block19_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (6208118999356538880 : R) * t0 ^ 6 * v1 * a4 ^ 2 * lambda
    - (6208118999356538880 : R) * t0 ^ 6 * u1 ^ 2 * a4 * lambda
    - (37248713996139233280 : R) * t0 ^ 5 * v1 ^ 2 * u1 * a4 * lambda
    - (12416237998713077760 : R) * t0 ^ 5 * v1 * u1 ^ 3 * lambda
    - (15520297498391347200 : R) * t0 ^ 4 * v1 ^ 4 * a4 * lambda
    - (31040594996782694400 : R) * t0 ^ 4 * v1 ^ 3 * u1 ^ 2 * lambda
    - (12416237998713077760 : R) * t0 ^ 3 * v1 ^ 5 * u1 * lambda
    - (886874142765219840 : R) * t0 ^ 2 * v1 ^ 7 * lambda

/-- Order-`103` contribution of Plus block `20`. -/
def degreeZeroOrder103Block20_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`103` contribution of Plus block `21`. -/
def degreeZeroOrder103Block21_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (900731551245926400 : R) * t0 ^ 8 * a4 ^ 2 * lambda
    + (14411704819934822400 : R) * t0 ^ 7 * v1 * u1 * a4 * lambda
    + (2401950803322470400 : R) * t0 ^ 7 * u1 ^ 3 * lambda
    + (16813655623257292800 : R) * t0 ^ 6 * v1 ^ 3 * a4 * lambda
    + (25220483434885939200 : R) * t0 ^ 6 * v1 ^ 2 * u1 ^ 2 * lambda
    + (25220483434885939200 : R) * t0 ^ 5 * v1 ^ 4 * u1 * lambda
    + (4203413905814323200 : R) * t0 ^ 4 * v1 ^ 6 * lambda

/-- Order-`103` contribution of Plus block `22`. -/
def degreeZeroOrder103Block22_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1826483423359795200 : R) * t0 ^ 9 * u1 * a4 * lambda
    - (8219175405119078400 : R) * t0 ^ 8 * v1 ^ 2 * a4 * lambda
    - (8219175405119078400 : R) * t0 ^ 8 * v1 * u1 ^ 2 * lambda
    - (21917801080317542400 : R) * t0 ^ 7 * v1 ^ 3 * u1 * lambda
    - (7671230378111139840 : R) * t0 ^ 6 * v1 ^ 5 * lambda

/-- Order-`103` contribution of Plus block `23`. -/
def degreeZeroOrder103Block23_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (155860783605596160 : R) * t0 ^ 12 * a4 * lambda
    - (1870329403267153920 : R) * t0 ^ 11 * v1 * u1 * lambda
    - (3428937239323115520 : R) * t0 ^ 10 * v1 ^ 3 * lambda
    + (1849314466151792640 : R) * t0 ^ 10 * v1 * a4 * lambda
    + (924657233075896320 : R) * t0 ^ 10 * u1 ^ 2 * lambda
    + (9246572330758963200 : R) * t0 ^ 9 * v1 ^ 2 * u1 * lambda
    + (6934929248069222400 : R) * t0 ^ 8 * v1 ^ 4 * lambda

/-- Order-`103` contribution of Plus block `24`. -/
def degreeZeroOrder103Block24_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (8020911814063155 : R) * t0 ^ 16 * lambda
    - (136284519318595200 : R) * t0 ^ 14 * v1 * lambda
    + (145370153939834880 : R) * t0 ^ 13 * u1 * lambda
    + (944906000608926720 : R) * t0 ^ 12 * v1 ^ 2 * lambda

/-- Frozen order-`103` coefficient of the cleared numerator
quotient (`h^1` of `degreeZeroSourceJetQuotient810`,
`h^0` of `degreeZeroSourceJetPlus810`). -/
def degreeZeroOrder103810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
  degreeZeroOrder103Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder103Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder103Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder103Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder103Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder103Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder103Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder103Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder103Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder103Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder103Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder103Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder103Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder103Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder103Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder103Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder103Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder103Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder103Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder103Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder103Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder103Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder103Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder103Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder103Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda

/-! ## Order `104` (quotient `h^2`, Plus `h^1`) -/

/-- Order-`104` contribution of Plus block `0`. -/
def degreeZeroOrder104Block0_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`104` contribution of Plus block `1`. -/
def degreeZeroOrder104Block1_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (2296835809958952960 : R) * a4 ^ 3 * a3

/-- Order-`104` contribution of Plus block `2`. -/
def degreeZeroOrder104Block2_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`104` contribution of Plus block `3`. -/
def degreeZeroOrder104Block3_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (1297036692682702848 : R) * u1 * a4 ^ 2 * b4
    + (3242591731706757120 : R) * u1 * a4 * a3 * b5
    + (1945555039024054272 : R) * a4 ^ 2 * a3 * b62

/-- Order-`104` contribution of Plus block `4`. -/
def degreeZeroOrder104Block4_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (13781014859753717760 : R) * t0 * u1 * a4 ^ 2 * a3
    + (10766417859182592000 : R) * v1 ^ 2 * a4 ^ 2 * a3
    + (21532835718365184000 : R) * v1 * u1 ^ 2 * a4 * a3
    + (1794402976530432000 : R) * u1 ^ 4 * a3

/-- Order-`104` contribution of Plus block `5`. -/
def degreeZeroOrder104Block5_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`104` contribution of Plus block `6`. -/
def degreeZeroOrder104Block6_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (2756202971950743552 : R) * t0 * v1 * a4 ^ 2 * b4
    - (6890507429876858880 : R) * t0 * v1 * a4 * a3 * b5
    - (2756202971950743552 : R) * t0 * u1 ^ 2 * a4 * b4
    - (3445253714938429440 : R) * t0 * u1 ^ 2 * a3 * b5
    - (8268608915852230656 : R) * t0 * u1 * a4 * a3 * b62

set_option maxHeartbeats 200000000 in
/-- Order-`104` contribution of Plus block `7`. -/
def degreeZeroOrder104Block7_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (4823355200913801216 : R) * t0 * a4 ^ 2 * a3 * w1
    - (2756202971950743552 : R) * v1 ^ 2 * u1 * a4 * b4
    - (3445253714938429440 : R) * v1 ^ 2 * u1 * a3 * b5
    - (4134304457926115328 : R) * v1 ^ 2 * a4 * a3 * b62
    - (918734323983581184 : R) * v1 * u1 ^ 3 * b4
    - (4134304457926115328 : R) * v1 * u1 ^ 2 * a3 * b62
    - (9646710401827602432 : R) * v1 * u1 * a4 * a3 * w1
    - (5512405943901487104 : R) * v1 * a4 ^ 2 * a3 * s1
    - (1607785066971267072 : R) * u1 ^ 3 * a3 * w1
    - (5512405943901487104 : R) * u1 ^ 2 * a4 * a3 * s1

/-- Order-`104` contribution of Plus block `8`. -/
def degreeZeroOrder104Block8_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (20187033485967360000 : R) * t0 ^ 2 * v1 * a4 ^ 2 * a3
    - (20187033485967360000 : R) * t0 ^ 2 * u1 ^ 2 * a4 * a3
    - (64598507155095552000 : R) * t0 * v1 ^ 2 * u1 * a4 * a3
    - (21532835718365184000 : R) * t0 * v1 * u1 ^ 3 * a3
    - (7401912278188032000 : R) * v1 ^ 4 * a4 * a3
    - (14803824556376064000 : R) * v1 ^ 3 * u1 ^ 2 * a3

/-- Order-`104` contribution of Plus block `9`. -/
def degreeZeroOrder104Block9_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`104` contribution of Plus block `10`. -/
def degreeZeroOrder104Block10_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (1435522381224345600 : R) * t0 ^ 3 * a4 ^ 2 * b4
    + (3588805953060864000 : R) * t0 ^ 3 * a4 * a3 * b5
    + (8613134287346073600 : R) * t0 ^ 2 * v1 * u1 * a4 * b4
    + (10766417859182592000 : R) * t0 ^ 2 * v1 * u1 * a3 * b5
    + (12919701431019110400 : R) * t0 ^ 2 * v1 * a4 * a3 * b62
    + (1435522381224345600 : R) * t0 ^ 2 * u1 ^ 3 * b4
    + (6459850715509555200 : R) * t0 ^ 2 * u1 ^ 2 * a3 * b62

set_option maxHeartbeats 200000000 in
/-- Order-`104` contribution of Plus block `11`. -/
def degreeZeroOrder104Block11_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (15072985002855628800 : R) * t0 ^ 2 * u1 * a4 * a3 * w1
    + (8613134287346073600 : R) * t0 ^ 2 * a4 ^ 2 * a3 * s1
    + (2871044762448691200 : R) * t0 * v1 ^ 3 * a4 * b4
    + (3588805953060864000 : R) * t0 * v1 ^ 3 * a3 * b5
    + (4306567143673036800 : R) * t0 * v1 ^ 2 * u1 ^ 2 * b4
    + (12919701431019110400 : R) * t0 * v1 ^ 2 * u1 * a3 * b62
    + (15072985002855628800 : R) * t0 * v1 ^ 2 * a4 * a3 * w1
    + (15072985002855628800 : R) * t0 * v1 * u1 ^ 2 * a3 * w1
    + (34452537149384294400 : R) * t0 * v1 * u1 * a4 * a3 * s1
    + (5742089524897382400 : R) * t0 * u1 ^ 3 * a3 * s1
    + (717761190612172800 : R) * v1 ^ 4 * u1 * b4
    + (1076641785918259200 : R) * v1 ^ 4 * a3 * b62

/-- Order-`104` contribution of Plus block `12`. -/
def degreeZeroOrder104Block12_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (2313097586933760000 : R) * t0 ^ 4 * a4 ^ 2 * a3
    + (51813385947316224000 : R) * t0 ^ 3 * v1 * u1 * a4 * a3
    + (8635564324552704000 : R) * t0 ^ 3 * u1 ^ 3 * a3
    + (42560995599581184000 : R) * t0 ^ 2 * v1 ^ 3 * a4 * a3
    + (63841493399371776000 : R) * t0 ^ 2 * v1 ^ 2 * u1 ^ 2 * a3
    + (29607649112752128000 : R) * t0 * v1 ^ 4 * u1 * a3
    + (5024328334285209600 : R) * v1 ^ 3 * u1 * a3 * w1
    + (5742089524897382400 : R) * v1 ^ 3 * a4 * a3 * s1
    + (8613134287346073600 : R) * v1 ^ 2 * u1 ^ 2 * a3 * s1

/-- Order-`104` contribution of Plus block `13`. -/
def degreeZeroOrder104Block13_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (1264493347523788800 : R) * v1 ^ 6 * a3

set_option maxHeartbeats 200000000 in
/-- Order-`104` contribution of Plus block `14`. -/
def degreeZeroOrder104Block14_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (2960764911275212800 : R) * t0 ^ 4 * u1 * a4 * b4
    - (3700956139094016000 : R) * t0 ^ 4 * u1 * a3 * b5
    - (4441147366912819200 : R) * t0 ^ 4 * a4 * a3 * b62
    - (5921529822550425600 : R) * t0 ^ 3 * v1 ^ 2 * a4 * b4
    - (7401912278188032000 : R) * t0 ^ 3 * v1 ^ 2 * a3 * b5
    - (5921529822550425600 : R) * t0 ^ 3 * v1 * u1 ^ 2 * b4
    - (17764589467651276800 : R) * t0 ^ 3 * v1 * u1 * a3 * b62
    - (20725354378926489600 : R) * t0 ^ 3 * v1 * a4 * a3 * w1
    - (10362677189463244800 : R) * t0 ^ 3 * u1 ^ 2 * a3 * w1
    - (23686119290201702400 : R) * t0 ^ 3 * u1 * a4 * a3 * s1

/-- Order-`104` contribution of Plus block `15`. -/
def degreeZeroOrder104Block15_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (5921529822550425600 : R) * t0 ^ 2 * v1 ^ 3 * u1 * b4
    - (8882294733825638400 : R) * t0 ^ 2 * v1 ^ 3 * a3 * b62
    - (31088031568389734400 : R) * t0 ^ 2 * v1 ^ 2 * u1 * a3 * w1
    - (35529178935302553600 : R) * t0 ^ 2 * v1 ^ 2 * a4 * a3 * s1
    - (35529178935302553600 : R) * t0 ^ 2 * v1 * u1 ^ 2 * a3 * s1
    - (592152982255042560 : R) * t0 * v1 ^ 5 * b4
    - (5181338594731622400 : R) * t0 * v1 ^ 4 * a3 * w1
    - (23686119290201702400 : R) * t0 * v1 ^ 3 * u1 * a3 * s1
    - (1184305964510085120 : R) * v1 ^ 5 * a3 * s1

/-- Order-`104` contribution of Plus block `16`. -/
def degreeZeroOrder104Block16_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (3793480042571366400 : R) * t0 ^ 5 * u1 * a4 * a3
    - (30822025345892352000 : R) * t0 ^ 4 * v1 ^ 2 * a4 * a3
    - (30822025345892352000 : R) * t0 ^ 4 * v1 * u1 ^ 2 * a3
    - (69547134113808384000 : R) * t0 ^ 3 * v1 ^ 3 * u1 * a3
    - (14699735164964044800 : R) * t0 ^ 2 * v1 ^ 5 * a3

/-- Order-`104` contribution of Plus block `17`. -/
def degreeZeroOrder104Block17_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (3034784034057093120 : R) * t0 ^ 5 * v1 * a4 * b4
    + (3793480042571366400 : R) * t0 ^ 5 * v1 * a3 * b5
    + (1517392017028546560 : R) * t0 ^ 5 * u1 ^ 2 * b4
    + (4552176051085639680 : R) * t0 ^ 5 * u1 * a3 * b62
    + (5310872059599912960 : R) * t0 ^ 5 * a4 * a3 * w1
    + (7586960085142732800 : R) * t0 ^ 4 * v1 ^ 2 * u1 * b4
    + (11380440127714099200 : R) * t0 ^ 4 * v1 ^ 2 * a3 * b62
    + (26554360297999564800 : R) * t0 ^ 4 * v1 * u1 * a3 * w1
    + (30347840340570931200 : R) * t0 ^ 4 * v1 * a4 * a3 * s1

/-- Order-`104` contribution of Plus block `18`. -/
def degreeZeroOrder104Block18_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (2904383157593702400 : R) * t0 ^ 6 * v1 * a4 * a3
    + (1452191578796851200 : R) * t0 ^ 6 * u1 ^ 2 * a3
    + (34852597891124428800 : R) * t0 ^ 5 * v1 ^ 2 * u1 * a3
    + (15173920170285465600 : R) * t0 ^ 4 * u1 ^ 2 * a3 * s1
    + (2528986695047577600 : R) * t0 ^ 3 * v1 ^ 4 * b4
    + (17702906865333043200 : R) * t0 ^ 3 * v1 ^ 3 * a3 * w1
    + (60695680681141862400 : R) * t0 ^ 3 * v1 ^ 2 * u1 * a3 * s1
    + (15173920170285465600 : R) * t0 ^ 2 * v1 ^ 4 * a3 * s1

/-- Order-`104` contribution of Plus block `19`. -/
def degreeZeroOrder104Block19_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (442572671633326080 : R) * t0 ^ 7 * a4 * b4
    - (553215839541657600 : R) * t0 ^ 7 * a3 * b5
    - (3098008701433282560 : R) * t0 ^ 6 * v1 * u1 * b4
    - (4647013052149923840 : R) * t0 ^ 6 * v1 * a3 * b62
    + (25413352628944896000 : R) * t0 ^ 4 * v1 ^ 4 * a3

/-- Order-`104` contribution of Plus block `20`. -/
def degreeZeroOrder104Block20_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (862238749910630400 : R) * t0 ^ 8 * a4 * a3
    - (1970831428367155200 : R) * t0 ^ 7 * v1 * u1 * a3
    - (12646168332022579200 : R) * t0 ^ 6 * v1 ^ 3 * a3
    - (5421515227508244480 : R) * t0 ^ 6 * u1 * a3 * w1
    - (6196017402866565120 : R) * t0 ^ 6 * a4 * a3 * s1
    - (3098008701433282560 : R) * t0 ^ 5 * v1 ^ 3 * b4
    - (16264545682524733440 : R) * t0 ^ 5 * v1 ^ 2 * a3 * w1
    - (37176104417199390720 : R) * t0 ^ 5 * v1 * u1 * a3 * s1
    - (30980087014332825600 : R) * t0 ^ 4 * v1 ^ 3 * a3 * s1

/-- Order-`104` contribution of Plus block `21`. -/
def degreeZeroOrder104Block21_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (394166285673431040 : R) * t0 ^ 8 * u1 * b4
    + (591249428510146560 : R) * t0 ^ 8 * a3 * b62
    + (1576665142693724160 : R) * t0 ^ 7 * v1 ^ 2 * b4
    + (5518327999428034560 : R) * t0 ^ 7 * v1 * a3 * w1
    + (6306660570774896640 : R) * t0 ^ 7 * u1 * a3 * s1
    + (22073311997712138240 : R) * t0 ^ 6 * v1 ^ 2 * a3 * s1

/-- Order-`104` contribution of Plus block `22`. -/
def degreeZeroOrder104Block22_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (355844563455180800 : R) * t0 ^ 9 * v1 * b4
    - (889611408637952000 : R) * t0 ^ 9 * u1 * a3
    - (622727986046566400 : R) * t0 ^ 9 * a3 * w1
    + (500406417358848000 : R) * t0 ^ 8 * v1 ^ 2 * a3
    - (6405202142193254400 : R) * t0 ^ 8 * v1 * a3 * s1

/-- Order-`104` contribution of Plus block `23`. -/
def degreeZeroOrder104Block23_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (147882890811801600 : R) * t0 ^ 12 * a3
    + (29518924013895680 : R) * t0 ^ 11 * b4
    + (913241711679897600 : R) * t0 ^ 10 * v1 * a3
    + (649416328305704960 : R) * t0 ^ 10 * a3 * s1

/-- Order-`104` contribution of Plus block `24`. -/
def degreeZeroOrder104Block24_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Frozen order-`104` coefficient of the cleared numerator
quotient (`h^2` of `degreeZeroSourceJetQuotient810`,
`h^1` of `degreeZeroSourceJetPlus810`). -/
def degreeZeroOrder104810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
  degreeZeroOrder104Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder104Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder104Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder104Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder104Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder104Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder104Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder104Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder104Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder104Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder104Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder104Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder104Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder104Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder104Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder104Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder104Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder104Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder104Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder104Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder104Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder104Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder104Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder104Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder104Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda

/-! ## Order `105` (quotient `h^3`, Plus `h^2`) -/

/-- Order-`105` contribution of Plus block `0`. -/
def degreeZeroOrder105Block0_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`105` contribution of Plus block `1`. -/
def degreeZeroOrder105Block1_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`105` contribution of Plus block `2`. -/
def degreeZeroOrder105Block2_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (1550364171722293248 : R) * u1 * a4 ^ 2 * a3 * lambda

/-- Order-`105` contribution of Plus block `3`. -/
def degreeZeroOrder105Block3_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`105` contribution of Plus block `4`. -/
def degreeZeroOrder105Block4_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`105` contribution of Plus block `5`. -/
def degreeZeroOrder105Block5_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (4844888036632166400 : R) * t0 * v1 * a4 ^ 2 * a3 * lambda
    - (4844888036632166400 : R) * t0 * u1 ^ 2 * a4 * a3 * lambda
    - (4844888036632166400 : R) * v1 ^ 2 * u1 * a4 * a3 * lambda
    - (1614962678877388800 : R) * v1 * u1 ^ 3 * a3 * lambda

/-- Order-`105` contribution of Plus block `6`. -/
def degreeZeroOrder105Block6_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`105` contribution of Plus block `7`. -/
def degreeZeroOrder105Block7_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`105` contribution of Plus block `8`. -/
def degreeZeroOrder105Block8_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`105` contribution of Plus block `9`. -/
def degreeZeroOrder105Block9_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (3330860525184614400 : R) * t0 ^ 3 * a4 ^ 2 * a3 * lambda
    + (19985163151107686400 : R) * t0 ^ 2 * v1 * u1 * a4 * a3 * lambda
    + (3330860525184614400 : R) * t0 ^ 2 * u1 ^ 3 * a3 * lambda
    + (6661721050369228800 : R) * t0 * v1 ^ 3 * a4 * a3 * lambda
    + (9992581575553843200 : R) * t0 * v1 ^ 2 * u1 ^ 2 * a3 * lambda
    + (1665430262592307200 : R) * v1 ^ 4 * u1 * a3 * lambda

/-- Order-`105` contribution of Plus block `10`. -/
def degreeZeroOrder105Block10_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`105` contribution of Plus block `11`. -/
def degreeZeroOrder105Block11_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`105` contribution of Plus block `12`. -/
def degreeZeroOrder105Block12_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`105` contribution of Plus block `13`. -/
def degreeZeroOrder105Block13_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (8535330095785574400 : R) * t0 ^ 4 * u1 * a4 * a3 * lambda
    - (17070660191571148800 : R) * t0 ^ 3 * v1 ^ 2 * a4 * a3 * lambda
    - (17070660191571148800 : R) * t0 ^ 3 * v1 * u1 ^ 2 * a3 * lambda
    - (17070660191571148800 : R) * t0 ^ 2 * v1 ^ 3 * u1 * a3 * lambda
    - (1707066019157114880 : R) * t0 * v1 ^ 5 * a3 * lambda

/-- Order-`105` contribution of Plus block `14`. -/
def degreeZeroOrder105Block14_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`105` contribution of Plus block `15`. -/
def degreeZeroOrder105Block15_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`105` contribution of Plus block `16`. -/
def degreeZeroOrder105Block16_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (10455779367337328640 : R) * t0 ^ 5 * v1 * a4 * a3 * lambda
    + (5227889683668664320 : R) * t0 ^ 5 * u1 ^ 2 * a3 * lambda
    + (26139448418343321600 : R) * t0 ^ 4 * v1 ^ 2 * u1 * a3 * lambda
    + (8713149472781107200 : R) * t0 ^ 3 * v1 ^ 4 * a3 * lambda

/-- Order-`105` contribution of Plus block `17`. -/
def degreeZeroOrder105Block17_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`105` contribution of Plus block `18`. -/
def degreeZeroOrder105Block18_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`105` contribution of Plus block `19`. -/
def degreeZeroOrder105Block19_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1773748285530439680 : R) * t0 ^ 7 * a4 * a3 * lambda
    - (12416237998713077760 : R) * t0 ^ 6 * v1 * u1 * a3 * lambda
    - (12416237998713077760 : R) * t0 ^ 5 * v1 ^ 3 * a3 * lambda

/-- Order-`105` contribution of Plus block `20`. -/
def degreeZeroOrder105Block20_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`105` contribution of Plus block `21`. -/
def degreeZeroOrder105Block21_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (1801463102491852800 : R) * t0 ^ 8 * u1 * a3 * lambda
    + (7205852409967411200 : R) * t0 ^ 7 * v1 ^ 2 * a3 * lambda

/-- Order-`105` contribution of Plus block `22`. -/
def degreeZeroOrder105Block22_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1826483423359795200 : R) * t0 ^ 9 * v1 * a3 * lambda

/-- Order-`105` contribution of Plus block `23`. -/
def degreeZeroOrder105Block23_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (168119496922890240 : R) * t0 ^ 11 * a3 * lambda

/-- Order-`105` contribution of Plus block `24`. -/
def degreeZeroOrder105Block24_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Frozen order-`105` coefficient of the cleared numerator
quotient (`h^3` of `degreeZeroSourceJetQuotient810`,
`h^2` of `degreeZeroSourceJetPlus810`). -/
def degreeZeroOrder105810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
  degreeZeroOrder105Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder105Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder105Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder105Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder105Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder105Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder105Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder105Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder105Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder105Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder105Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder105Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder105Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder105Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder105Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder105Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder105Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder105Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder105Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder105Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder105Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder105Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder105Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder105Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder105Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda

/-! ## Order `106` (quotient `h^4`, Plus `h^3`) -/

/-- Order-`106` contribution of Plus block `0`. -/
def degreeZeroOrder106Block0_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`106` contribution of Plus block `1`. -/
def degreeZeroOrder106Block1_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (6890507429876858880 : R) * u1 * a4 ^ 2 * a2
    - (6890507429876858880 : R) * u1 * a4 * a3 ^ 2

/-- Order-`106` contribution of Plus block `2`. -/
def degreeZeroOrder106Block2_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

set_option maxHeartbeats 200000000 in
/-- Order-`106` contribution of Plus block `3`. -/
def degreeZeroOrder106Block3_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (972777519512027136 : R) * v1 * a4 ^ 2 * b3
    + (2594073385365405696 : R) * v1 * a4 * a3 * b4
    + (3242591731706757120 : R) * v1 * a4 * a2 * b5
    + (1621295865853378560 : R) * v1 * a3 ^ 2 * b5
    + (972777519512027136 : R) * u1 ^ 2 * a4 * b3
    + (1297036692682702848 : R) * u1 ^ 2 * a3 * b4
    + (1621295865853378560 : R) * u1 ^ 2 * a2 * b5
    + (3891110078048108544 : R) * u1 * a4 * a2 * b62
    + (1945555039024054272 : R) * u1 * a3 ^ 2 * b62
    + (2269814212194729984 : R) * a4 ^ 2 * a2 * w1
    + (2269814212194729984 : R) * a4 * a3 ^ 2 * w1

/-- Order-`106` contribution of Plus block `4`. -/
def degreeZeroOrder106Block4_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (13781014859753717760 : R) * t0 * v1 * a4 ^ 2 * a2
    + (13781014859753717760 : R) * t0 * v1 * a4 * a3 ^ 2
    + (13781014859753717760 : R) * t0 * u1 ^ 2 * a4 * a2
    + (6890507429876858880 : R) * t0 * u1 ^ 2 * a3 ^ 2
    + (21532835718365184000 : R) * v1 ^ 2 * u1 * a4 * a2
    + (10766417859182592000 : R) * v1 ^ 2 * u1 * a3 ^ 2
    + (7177611906121728000 : R) * v1 * u1 ^ 3 * a2

/-- Order-`106` contribution of Plus block `5`. -/
def degreeZeroOrder106Block5_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1033576114481528832 : R) * t0 ^ 2 * a4 ^ 2 * b3
    - (2756202971950743552 : R) * t0 ^ 2 * a4 * a3 * b4
    - (3445253714938429440 : R) * t0 ^ 2 * a4 * a2 * b5

set_option maxHeartbeats 200000000 in
/-- Order-`106` contribution of Plus block `6`. -/
def degreeZeroOrder106Block6_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1722626857469214720 : R) * t0 ^ 2 * a3 ^ 2 * b5
    - (4134304457926115328 : R) * t0 * v1 * u1 * a4 * b3
    - (5512405943901487104 : R) * t0 * v1 * u1 * a3 * b4
    - (6890507429876858880 : R) * t0 * v1 * u1 * a2 * b5
    - (8268608915852230656 : R) * t0 * v1 * a4 * a2 * b62
    - (4134304457926115328 : R) * t0 * v1 * a3 ^ 2 * b62
    - (689050742987685888 : R) * t0 * u1 ^ 3 * b3
    - (4134304457926115328 : R) * t0 * u1 ^ 2 * a2 * b62
    - (9646710401827602432 : R) * t0 * u1 * a4 * a2 * w1
    - (4823355200913801216 : R) * t0 * u1 * a3 ^ 2 * w1

set_option maxHeartbeats 200000000 in
/-- Order-`106` contribution of Plus block `7`. -/
def degreeZeroOrder106Block7_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (5512405943901487104 : R) * t0 * a4 ^ 2 * a2 * s1
    - (5512405943901487104 : R) * t0 * a4 * a3 ^ 2 * s1
    - (689050742987685888 : R) * v1 ^ 3 * a4 * b3
    - (918734323983581184 : R) * v1 ^ 3 * a3 * b4
    - (1148417904979476480 : R) * v1 ^ 3 * a2 * b5
    - (1033576114481528832 : R) * v1 ^ 2 * u1 ^ 2 * b3
    - (4134304457926115328 : R) * v1 ^ 2 * u1 * a2 * b62
    - (4823355200913801216 : R) * v1 ^ 2 * a4 * a2 * w1
    - (2411677600456900608 : R) * v1 ^ 2 * a3 ^ 2 * w1
    - (4823355200913801216 : R) * v1 * u1 ^ 2 * a2 * w1
    - (11024811887802974208 : R) * v1 * u1 * a4 * a2 * s1
    - (5512405943901487104 : R) * v1 * u1 * a3 ^ 2 * s1
    - (1837468647967162368 : R) * u1 ^ 3 * a2 * s1

/-- Order-`106` contribution of Plus block `8`. -/
def degreeZeroOrder106Block8_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (2691604464795648000 : R) * t0 ^ 3 * a4 ^ 2 * a2
    - (2691604464795648000 : R) * t0 ^ 3 * a4 * a3 ^ 2
    - (40374066971934720000 : R) * t0 ^ 2 * v1 * u1 * a4 * a2
    - (20187033485967360000 : R) * t0 ^ 2 * v1 * u1 * a3 ^ 2
    - (6729011161989120000 : R) * t0 ^ 2 * u1 ^ 3 * a2
    - (21532835718365184000 : R) * t0 * v1 ^ 3 * a4 * a2
    - (10766417859182592000 : R) * t0 * v1 ^ 3 * a3 ^ 2
    - (32299253577547776000 : R) * t0 * v1 ^ 2 * u1 ^ 2 * a2
    - (7401912278188032000 : R) * v1 ^ 4 * u1 * a2

/-- Order-`106` contribution of Plus block `9`. -/
def degreeZeroOrder106Block9_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

set_option maxHeartbeats 200000000 in
/-- Order-`106` contribution of Plus block `10`. -/
def degreeZeroOrder106Block10_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (2153283571836518400 : R) * t0 ^ 3 * u1 * a4 * b3
    + (2871044762448691200 : R) * t0 ^ 3 * u1 * a3 * b4
    + (3588805953060864000 : R) * t0 ^ 3 * u1 * a2 * b5
    + (4306567143673036800 : R) * t0 ^ 3 * a4 * a2 * b62
    + (2153283571836518400 : R) * t0 ^ 3 * a3 ^ 2 * b62
    + (3229925357754777600 : R) * t0 ^ 2 * v1 ^ 2 * a4 * b3
    + (4306567143673036800 : R) * t0 ^ 2 * v1 ^ 2 * a3 * b4
    + (5383208929591296000 : R) * t0 ^ 2 * v1 ^ 2 * a2 * b5
    + (3229925357754777600 : R) * t0 ^ 2 * v1 * u1 ^ 2 * b3
    + (12919701431019110400 : R) * t0 ^ 2 * v1 * u1 * a2 * b62
    + (15072985002855628800 : R) * t0 ^ 2 * v1 * a4 * a2 * w1
    + (7536492501427814400 : R) * t0 ^ 2 * v1 * a3 ^ 2 * w1
    + (7536492501427814400 : R) * t0 ^ 2 * u1 ^ 2 * a2 * w1

set_option maxHeartbeats 200000000 in
/-- Order-`106` contribution of Plus block `11`. -/
def degreeZeroOrder106Block11_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (17226268574692147200 : R) * t0 ^ 2 * u1 * a4 * a2 * s1
    + (8613134287346073600 : R) * t0 ^ 2 * u1 * a3 ^ 2 * s1
    + (2153283571836518400 : R) * t0 * v1 ^ 3 * u1 * b3
    + (4306567143673036800 : R) * t0 * v1 ^ 3 * a2 * b62
    + (15072985002855628800 : R) * t0 * v1 ^ 2 * u1 * a2 * w1
    + (17226268574692147200 : R) * t0 * v1 ^ 2 * a4 * a2 * s1
    + (8613134287346073600 : R) * t0 * v1 ^ 2 * a3 ^ 2 * s1
    + (17226268574692147200 : R) * t0 * v1 * u1 ^ 2 * a2 * s1
    + (107664178591825920 : R) * v1 ^ 5 * b3
    + (1256082083571302400 : R) * v1 ^ 4 * a2 * w1

/-- Order-`106` contribution of Plus block `12`. -/
def degreeZeroOrder106Block12_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (4626195173867520000 : R) * t0 ^ 4 * u1 * a4 * a2
    + (2313097586933760000 : R) * t0 ^ 4 * u1 * a3 ^ 2
    + (25906692973658112000 : R) * t0 ^ 3 * v1 ^ 2 * a4 * a2
    + (12953346486829056000 : R) * t0 ^ 3 * v1 ^ 2 * a3 ^ 2
    + (25906692973658112000 : R) * t0 ^ 3 * v1 * u1 ^ 2 * a2
    + (42560995599581184000 : R) * t0 ^ 2 * v1 ^ 3 * u1 * a2
    + (5921529822550425600 : R) * t0 * v1 ^ 5 * a2
    + (5742089524897382400 : R) * v1 ^ 3 * u1 * a2 * s1

/-- Order-`106` contribution of Plus block `13`. -/
def degreeZeroOrder106Block13_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (2220573683456409600 : R) * t0 ^ 4 * v1 * a4 * b3

set_option maxHeartbeats 200000000 in
/-- Order-`106` contribution of Plus block `14`. -/
def degreeZeroOrder106Block14_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (2960764911275212800 : R) * t0 ^ 4 * v1 * a3 * b4
    - (3700956139094016000 : R) * t0 ^ 4 * v1 * a2 * b5
    - (1110286841728204800 : R) * t0 ^ 4 * u1 ^ 2 * b3
    - (4441147366912819200 : R) * t0 ^ 4 * u1 * a2 * b62
    - (5181338594731622400 : R) * t0 ^ 4 * a4 * a2 * w1
    - (2590669297365811200 : R) * t0 ^ 4 * a3 ^ 2 * w1
    - (4441147366912819200 : R) * t0 ^ 3 * v1 ^ 2 * u1 * b3
    - (8882294733825638400 : R) * t0 ^ 3 * v1 ^ 2 * a2 * b62
    - (20725354378926489600 : R) * t0 ^ 3 * v1 * u1 * a2 * w1
    - (23686119290201702400 : R) * t0 ^ 3 * v1 * a4 * a2 * s1
    - (11843059645100851200 : R) * t0 ^ 3 * v1 * a3 ^ 2 * s1
    - (11843059645100851200 : R) * t0 ^ 3 * u1 ^ 2 * a2 * s1
    - (1110286841728204800 : R) * t0 ^ 2 * v1 ^ 4 * b3

/-- Order-`106` contribution of Plus block `15`. -/
def degreeZeroOrder106Block15_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (10362677189463244800 : R) * t0 ^ 2 * v1 ^ 3 * a2 * w1
    - (35529178935302553600 : R) * t0 ^ 2 * v1 ^ 2 * u1 * a2 * s1
    - (5921529822550425600 : R) * t0 * v1 ^ 4 * a2 * s1

/-- Order-`106` contribution of Plus block `16`. -/
def degreeZeroOrder106Block16_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (3793480042571366400 : R) * t0 ^ 5 * v1 * a4 * a2
    - (1896740021285683200 : R) * t0 ^ 5 * v1 * a3 ^ 2
    - (1896740021285683200 : R) * t0 ^ 5 * u1 ^ 2 * a2
    - (30822025345892352000 : R) * t0 ^ 4 * v1 ^ 2 * u1 * a2
    - (17386783528452096000 : R) * t0 ^ 3 * v1 ^ 4 * a2

set_option maxHeartbeats 200000000 in
/-- Order-`106` contribution of Plus block `17`. -/
def degreeZeroOrder106Block17_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (379348004257136640 : R) * t0 ^ 6 * a4 * b3
    + (505797339009515520 : R) * t0 ^ 6 * a3 * b4
    + (632246673761894400 : R) * t0 ^ 6 * a2 * b5
    + (2276088025542819840 : R) * t0 ^ 5 * v1 * u1 * b3
    + (4552176051085639680 : R) * t0 ^ 5 * v1 * a2 * b62
    + (5310872059599912960 : R) * t0 ^ 5 * u1 * a2 * w1
    + (6069568068114186240 : R) * t0 ^ 5 * a4 * a2 * s1
    + (3034784034057093120 : R) * t0 ^ 5 * a3 ^ 2 * s1
    + (1896740021285683200 : R) * t0 ^ 4 * v1 ^ 3 * b3
    + (13277180148999782400 : R) * t0 ^ 4 * v1 ^ 2 * a2 * w1
    + (30347840340570931200 : R) * t0 ^ 4 * v1 * u1 * a2 * s1

/-- Order-`106` contribution of Plus block `18`. -/
def degreeZeroOrder106Block18_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (829823759312486400 : R) * t0 ^ 7 * a4 * a2
    - (414911879656243200 : R) * t0 ^ 7 * a3 ^ 2
    + (2904383157593702400 : R) * t0 ^ 6 * v1 * u1 * a2
    + (11617532630374809600 : R) * t0 ^ 5 * v1 ^ 3 * a2
    + (20231893560380620800 : R) * t0 ^ 3 * v1 ^ 3 * a2 * s1

/-- Order-`106` contribution of Plus block `19`. -/
def degreeZeroOrder106Block19_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (331929503724994560 : R) * t0 ^ 7 * u1 * b3
    - (663859007449989120 : R) * t0 ^ 7 * a2 * b62
    - (1161753263037480960 : R) * t0 ^ 6 * v1 ^ 2 * b3
    - (5421515227508244480 : R) * t0 ^ 6 * v1 * a2 * w1

/-- Order-`106` contribution of Plus block `20`. -/
def degreeZeroOrder106Block20_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (862238749910630400 : R) * t0 ^ 8 * u1 * a2
    - (985415714183577600 : R) * t0 ^ 7 * v1 ^ 2 * a2
    - (6196017402866565120 : R) * t0 ^ 6 * u1 * a2 * s1
    - (18588052208599695360 : R) * t0 ^ 5 * v1 ^ 2 * a2 * s1

/-- Order-`106` contribution of Plus block `21`. -/
def degreeZeroOrder106Block21_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (295624714255073280 : R) * t0 ^ 8 * v1 * b3
    + (689790999928504320 : R) * t0 ^ 8 * a2 * w1
    + (6306660570774896640 : R) * t0 ^ 7 * v1 * a2 * s1

/-- Order-`106` contribution of Plus block `22`. -/
def degreeZeroOrder106Block22_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (26688342259138560 : R) * t0 ^ 10 * b3
    - (889611408637952000 : R) * t0 ^ 9 * v1 * a2
    - (711689126910361600 : R) * t0 ^ 9 * a2 * s1

/-- Order-`106` contribution of Plus block `23`. -/
def degreeZeroOrder106Block23_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (166043947578163200 : R) * t0 ^ 11 * a2

/-- Order-`106` contribution of Plus block `24`. -/
def degreeZeroOrder106Block24_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Frozen order-`106` coefficient of the cleared numerator
quotient (`h^4` of `degreeZeroSourceJetQuotient810`,
`h^3` of `degreeZeroSourceJetPlus810`). -/
def degreeZeroOrder106810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
  degreeZeroOrder106Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder106Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder106Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder106Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder106Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder106Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder106Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder106Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder106Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder106Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder106Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder106Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder106Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder106Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder106Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder106Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder106Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder106Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder106Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder106Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder106Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder106Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder106Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder106Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder106Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda

/-! ## Order `107` (quotient `h^5`, Plus `h^4`) -/

/-- Order-`107` contribution of Plus block `0`. -/
def degreeZeroOrder107Block0_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`107` contribution of Plus block `1`. -/
def degreeZeroOrder107Block1_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`107` contribution of Plus block `2`. -/
def degreeZeroOrder107Block2_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (1550364171722293248 : R) * v1 * a4 ^ 2 * a2 * lambda
    + (1550364171722293248 : R) * v1 * a4 * a3 ^ 2 * lambda
    + (1550364171722293248 : R) * u1 ^ 2 * a4 * a2 * lambda
    + (775182085861146624 : R) * u1 ^ 2 * a3 ^ 2 * lambda

/-- Order-`107` contribution of Plus block `3`. -/
def degreeZeroOrder107Block3_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`107` contribution of Plus block `4`. -/
def degreeZeroOrder107Block4_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (2422444018316083200 : R) * t0 ^ 2 * a4 ^ 2 * a2 * lambda

/-- Order-`107` contribution of Plus block `5`. -/
def degreeZeroOrder107Block5_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (2422444018316083200 : R) * t0 ^ 2 * a4 * a3 ^ 2 * lambda
    - (9689776073264332800 : R) * t0 * v1 * u1 * a4 * a2 * lambda
    - (4844888036632166400 : R) * t0 * v1 * u1 * a3 ^ 2 * lambda
    - (1614962678877388800 : R) * t0 * u1 ^ 3 * a2 * lambda
    - (1614962678877388800 : R) * v1 ^ 3 * a4 * a2 * lambda
    - (807481339438694400 : R) * v1 ^ 3 * a3 ^ 2 * lambda
    - (2422444018316083200 : R) * v1 ^ 2 * u1 ^ 2 * a2 * lambda

/-- Order-`107` contribution of Plus block `6`. -/
def degreeZeroOrder107Block6_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`107` contribution of Plus block `7`. -/
def degreeZeroOrder107Block7_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`107` contribution of Plus block `8`. -/
def degreeZeroOrder107Block8_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`107` contribution of Plus block `9`. -/
def degreeZeroOrder107Block9_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (6661721050369228800 : R) * t0 ^ 3 * u1 * a4 * a2 * lambda
    + (3330860525184614400 : R) * t0 ^ 3 * u1 * a3 ^ 2 * lambda
    + (9992581575553843200 : R) * t0 ^ 2 * v1 ^ 2 * a4 * a2 * lambda
    + (4996290787776921600 : R) * t0 ^ 2 * v1 ^ 2 * a3 ^ 2 * lambda
    + (9992581575553843200 : R) * t0 ^ 2 * v1 * u1 ^ 2 * a2 * lambda
    + (6661721050369228800 : R) * t0 * v1 ^ 3 * u1 * a2 * lambda
    + (333086052518461440 : R) * v1 ^ 5 * a2 * lambda

/-- Order-`107` contribution of Plus block `10`. -/
def degreeZeroOrder107Block10_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`107` contribution of Plus block `11`. -/
def degreeZeroOrder107Block11_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`107` contribution of Plus block `12`. -/
def degreeZeroOrder107Block12_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`107` contribution of Plus block `13`. -/
def degreeZeroOrder107Block13_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (8535330095785574400 : R) * t0 ^ 4 * v1 * a4 * a2 * lambda
    - (4267665047892787200 : R) * t0 ^ 4 * v1 * a3 ^ 2 * lambda
    - (4267665047892787200 : R) * t0 ^ 4 * u1 ^ 2 * a2 * lambda
    - (17070660191571148800 : R) * t0 ^ 3 * v1 ^ 2 * u1 * a2 * lambda
    - (4267665047892787200 : R) * t0 ^ 2 * v1 ^ 4 * a2 * lambda

/-- Order-`107` contribution of Plus block `14`. -/
def degreeZeroOrder107Block14_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`107` contribution of Plus block `15`. -/
def degreeZeroOrder107Block15_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`107` contribution of Plus block `16`. -/
def degreeZeroOrder107Block16_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (1742629894556221440 : R) * t0 ^ 6 * a4 * a2 * lambda
    + (871314947278110720 : R) * t0 ^ 6 * a3 ^ 2 * lambda
    + (10455779367337328640 : R) * t0 ^ 5 * v1 * u1 * a2 * lambda
    + (8713149472781107200 : R) * t0 ^ 4 * v1 ^ 3 * a2 * lambda

/-- Order-`107` contribution of Plus block `17`. -/
def degreeZeroOrder107Block17_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`107` contribution of Plus block `18`. -/
def degreeZeroOrder107Block18_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`107` contribution of Plus block `19`. -/
def degreeZeroOrder107Block19_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1773748285530439680 : R) * t0 ^ 7 * u1 * a2 * lambda
    - (6208118999356538880 : R) * t0 ^ 6 * v1 ^ 2 * a2 * lambda

/-- Order-`107` contribution of Plus block `20`. -/
def degreeZeroOrder107Block20_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`107` contribution of Plus block `21`. -/
def degreeZeroOrder107Block21_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (1801463102491852800 : R) * t0 ^ 8 * v1 * a2 * lambda

/-- Order-`107` contribution of Plus block `22`. -/
def degreeZeroOrder107Block22_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (182648342335979520 : R) * t0 ^ 10 * a2 * lambda

/-- Order-`107` contribution of Plus block `23`. -/
def degreeZeroOrder107Block23_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`107` contribution of Plus block `24`. -/
def degreeZeroOrder107Block24_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Frozen order-`107` coefficient of the cleared numerator
quotient (`h^5` of `degreeZeroSourceJetQuotient810`,
`h^4` of `degreeZeroSourceJetPlus810`). -/
def degreeZeroOrder107810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
  degreeZeroOrder107Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder107Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder107Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder107Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder107Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder107Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder107Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder107Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder107Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder107Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder107Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder107Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder107Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder107Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder107Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder107Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder107Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder107Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder107Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder107Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder107Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder107Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder107Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder107Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder107Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda

/-! ## Order `108` (quotient `h^6`, Plus `h^5`) -/

/-- Order-`108` contribution of Plus block `0`. -/
def degreeZeroOrder108Block0_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`108` contribution of Plus block `1`. -/
def degreeZeroOrder108Block1_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (6890507429876858880 : R) * v1 * a4 ^ 2 * a1
    - (13781014859753717760 : R) * v1 * a4 * a3 * a2
    - (2296835809958952960 : R) * v1 * a3 ^ 3
    - (6890507429876858880 : R) * u1 ^ 2 * a4 * a1
    - (6890507429876858880 : R) * u1 ^ 2 * a3 * a2

/-- Order-`108` contribution of Plus block `2`. -/
def degreeZeroOrder108Block2_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (648518346341351424 : R) * t0 * a4 ^ 2 * b2
    + (1945555039024054272 : R) * t0 * a4 * a3 * b3
    + (2594073385365405696 : R) * t0 * a4 * a2 * b4
    + (3242591731706757120 : R) * t0 * a4 * a1 * b5
    + (1297036692682702848 : R) * t0 * a3 ^ 2 * b4
    + (3242591731706757120 : R) * t0 * a3 * a2 * b5
    + (1297036692682702848 : R) * v1 * u1 * a4 * b2
    + (1945555039024054272 : R) * v1 * u1 * a3 * b3

set_option maxHeartbeats 200000000 in
/-- Order-`108` contribution of Plus block `3`. -/
def degreeZeroOrder108Block3_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (2594073385365405696 : R) * v1 * u1 * a2 * b4
    + (3242591731706757120 : R) * v1 * u1 * a1 * b5
    + (3891110078048108544 : R) * v1 * a4 * a1 * b62
    + (3891110078048108544 : R) * v1 * a3 * a2 * b62
    + (216172782113783808 : R) * u1 ^ 3 * b2
    + (1945555039024054272 : R) * u1 ^ 2 * a1 * b62
    + (4539628424389459968 : R) * u1 * a4 * a1 * w1
    + (4539628424389459968 : R) * u1 * a3 * a2 * w1
    + (2594073385365405696 : R) * a4 ^ 2 * a1 * s1
    + (5188146770730811392 : R) * a4 * a3 * a2 * s1
    + (864691128455135232 : R) * a3 ^ 3 * s1

/-- Order-`108` contribution of Plus block `4`. -/
def degreeZeroOrder108Block4_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (3014597000571125760 : R) * t0 ^ 2 * a4 ^ 2 * a1
    + (6029194001142251520 : R) * t0 ^ 2 * a4 * a3 * a2
    + (1004865666857041920 : R) * t0 ^ 2 * a3 ^ 3
    + (27562029719507435520 : R) * t0 * v1 * u1 * a4 * a1
    + (27562029719507435520 : R) * t0 * v1 * u1 * a3 * a2
    + (4593671619917905920 : R) * t0 * u1 ^ 3 * a1
    + (7177611906121728000 : R) * v1 ^ 3 * a4 * a1
    + (7177611906121728000 : R) * v1 ^ 3 * a3 * a2
    + (10766417859182592000 : R) * v1 ^ 2 * u1 ^ 2 * a1

/-- Order-`108` contribution of Plus block `5`. -/
def degreeZeroOrder108Block5_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1378101485975371776 : R) * t0 ^ 2 * u1 * a4 * b2
    - (2067152228963057664 : R) * t0 ^ 2 * u1 * a3 * b3
    - (2756202971950743552 : R) * t0 ^ 2 * u1 * a2 * b4
    - (3445253714938429440 : R) * t0 ^ 2 * u1 * a1 * b5
    - (4134304457926115328 : R) * t0 ^ 2 * a4 * a1 * b62

set_option maxHeartbeats 200000000 in
/-- Order-`108` contribution of Plus block `6`. -/
def degreeZeroOrder108Block6_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (4134304457926115328 : R) * t0 ^ 2 * a3 * a2 * b62
    - (1378101485975371776 : R) * t0 * v1 ^ 2 * a4 * b2
    - (2067152228963057664 : R) * t0 * v1 ^ 2 * a3 * b3
    - (2756202971950743552 : R) * t0 * v1 ^ 2 * a2 * b4
    - (3445253714938429440 : R) * t0 * v1 ^ 2 * a1 * b5
    - (1378101485975371776 : R) * t0 * v1 * u1 ^ 2 * b2
    - (8268608915852230656 : R) * t0 * v1 * u1 * a1 * b62
    - (9646710401827602432 : R) * t0 * v1 * a4 * a1 * w1
    - (9646710401827602432 : R) * t0 * v1 * a3 * a2 * w1
    - (4823355200913801216 : R) * t0 * u1 ^ 2 * a1 * w1
    - (11024811887802974208 : R) * t0 * u1 * a4 * a1 * s1
    - (11024811887802974208 : R) * t0 * u1 * a3 * a2 * s1

/-- Order-`108` contribution of Plus block `7`. -/
def degreeZeroOrder108Block7_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (459367161991790592 : R) * v1 ^ 3 * u1 * b2
    - (1378101485975371776 : R) * v1 ^ 3 * a1 * b62
    - (4823355200913801216 : R) * v1 ^ 2 * u1 * a1 * w1
    - (5512405943901487104 : R) * v1 ^ 2 * a4 * a1 * s1
    - (5512405943901487104 : R) * v1 ^ 2 * a3 * a2 * s1
    - (5512405943901487104 : R) * v1 * u1 ^ 2 * a1 * s1

/-- Order-`108` contribution of Plus block `8`. -/
def degreeZeroOrder108Block8_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (5383208929591296000 : R) * t0 ^ 3 * u1 * a4 * a1
    - (5383208929591296000 : R) * t0 ^ 3 * u1 * a3 * a2
    - (20187033485967360000 : R) * t0 ^ 2 * v1 ^ 2 * a4 * a1
    - (20187033485967360000 : R) * t0 ^ 2 * v1 ^ 2 * a3 * a2
    - (20187033485967360000 : R) * t0 ^ 2 * v1 * u1 ^ 2 * a1
    - (21532835718365184000 : R) * t0 * v1 ^ 3 * u1 * a1
    - (1480382455637606400 : R) * v1 ^ 5 * a1

/-- Order-`108` contribution of Plus block `9`. -/
def degreeZeroOrder108Block9_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (1435522381224345600 : R) * t0 ^ 3 * v1 * a4 * b2
    + (2153283571836518400 : R) * t0 ^ 3 * v1 * a3 * b3
    + (2871044762448691200 : R) * t0 ^ 3 * v1 * a2 * b4
    + (3588805953060864000 : R) * t0 ^ 3 * v1 * a1 * b5

set_option maxHeartbeats 200000000 in
/-- Order-`108` contribution of Plus block `10`. -/
def degreeZeroOrder108Block10_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (717761190612172800 : R) * t0 ^ 3 * u1 ^ 2 * b2
    + (4306567143673036800 : R) * t0 ^ 3 * u1 * a1 * b62
    + (5024328334285209600 : R) * t0 ^ 3 * a4 * a1 * w1
    + (5024328334285209600 : R) * t0 ^ 3 * a3 * a2 * w1
    + (2153283571836518400 : R) * t0 ^ 2 * v1 ^ 2 * u1 * b2
    + (6459850715509555200 : R) * t0 ^ 2 * v1 ^ 2 * a1 * b62
    + (15072985002855628800 : R) * t0 ^ 2 * v1 * u1 * a1 * w1
    + (17226268574692147200 : R) * t0 ^ 2 * v1 * a4 * a1 * s1
    + (17226268574692147200 : R) * t0 ^ 2 * v1 * a3 * a2 * s1
    + (8613134287346073600 : R) * t0 ^ 2 * u1 ^ 2 * a1 * s1

/-- Order-`108` contribution of Plus block `11`. -/
def degreeZeroOrder108Block11_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (358880595306086400 : R) * t0 * v1 ^ 4 * b2
    + (5024328334285209600 : R) * t0 * v1 ^ 3 * a1 * w1
    + (17226268574692147200 : R) * t0 * v1 ^ 2 * u1 * a1 * s1
    + (1435522381224345600 : R) * v1 ^ 4 * a1 * s1

/-- Order-`108` contribution of Plus block `12`. -/
def degreeZeroOrder108Block12_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (4626195173867520000 : R) * t0 ^ 4 * v1 * a4 * a1
    + (4626195173867520000 : R) * t0 ^ 4 * v1 * a3 * a2
    + (2313097586933760000 : R) * t0 ^ 4 * u1 ^ 2 * a1
    + (25906692973658112000 : R) * t0 ^ 3 * v1 ^ 2 * u1 * a1
    + (10640248899895296000 : R) * t0 ^ 2 * v1 ^ 4 * a1

/-- Order-`108` contribution of Plus block `13`. -/
def degreeZeroOrder108Block13_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (296076491127521280 : R) * t0 ^ 5 * a4 * b2
    - (444114736691281920 : R) * t0 ^ 5 * a3 * b3
    - (592152982255042560 : R) * t0 ^ 5 * a2 * b4
    - (740191227818803200 : R) * t0 ^ 5 * a1 * b5
    - (1480382455637606400 : R) * t0 ^ 4 * v1 * u1 * b2

/-- Order-`108` contribution of Plus block `14`. -/
def degreeZeroOrder108Block14_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (4441147366912819200 : R) * t0 ^ 4 * v1 * a1 * b62
    - (5181338594731622400 : R) * t0 ^ 4 * u1 * a1 * w1
    - (5921529822550425600 : R) * t0 ^ 4 * a4 * a1 * s1
    - (5921529822550425600 : R) * t0 ^ 4 * a3 * a2 * s1
    - (986921637091737600 : R) * t0 ^ 3 * v1 ^ 3 * b2
    - (10362677189463244800 : R) * t0 ^ 3 * v1 ^ 2 * a1 * w1
    - (23686119290201702400 : R) * t0 ^ 3 * v1 * u1 * a1 * s1

/-- Order-`108` contribution of Plus block `15`. -/
def degreeZeroOrder108Block15_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (790308342202368000 : R) * t0 ^ 6 * a4 * a1
    + (790308342202368000 : R) * t0 ^ 6 * a3 * a2
    - (11843059645100851200 : R) * t0 ^ 2 * v1 ^ 3 * a1 * s1

/-- Order-`108` contribution of Plus block `16`. -/
def degreeZeroOrder108Block16_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (3793480042571366400 : R) * t0 ^ 5 * v1 * u1 * a1
    - (10274008448630784000 : R) * t0 ^ 4 * v1 ^ 3 * a1

/-- Order-`108` contribution of Plus block `17`. -/
def degreeZeroOrder108Block17_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (252898669504757760 : R) * t0 ^ 6 * u1 * b2
    + (758696008514273280 : R) * t0 ^ 6 * a1 * b62
    + (758696008514273280 : R) * t0 ^ 5 * v1 ^ 2 * b2
    + (5310872059599912960 : R) * t0 ^ 5 * v1 * a1 * w1
    + (6069568068114186240 : R) * t0 ^ 5 * u1 * a1 * s1
    + (15173920170285465600 : R) * t0 ^ 4 * v1 ^ 2 * a1 * s1

/-- Order-`108` contribution of Plus block `18`. -/
def degreeZeroOrder108Block18_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (829823759312486400 : R) * t0 ^ 7 * u1 * a1
    + (1452191578796851200 : R) * t0 ^ 6 * v1 ^ 2 * a1

/-- Order-`108` contribution of Plus block `19`. -/
def degreeZeroOrder108Block19_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (221286335816663040 : R) * t0 ^ 7 * v1 * b2
    - (774502175358320640 : R) * t0 ^ 7 * a1 * w1
    - (6196017402866565120 : R) * t0 ^ 6 * v1 * a1 * s1

/-- Order-`108` contribution of Plus block `20`. -/
def degreeZeroOrder108Block20_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (862238749910630400 : R) * t0 ^ 8 * v1 * a1

/-- Order-`108` contribution of Plus block `21`. -/
def degreeZeroOrder108Block21_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (21898126981857280 : R) * t0 ^ 9 * b2
    + (788332571346862080 : R) * t0 ^ 8 * a1 * s1

/-- Order-`108` contribution of Plus block `22`. -/
def degreeZeroOrder108Block22_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (189042424335564800 : R) * t0 ^ 10 * a1

/-- Order-`108` contribution of Plus block `23`. -/
def degreeZeroOrder108Block23_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`108` contribution of Plus block `24`. -/
def degreeZeroOrder108Block24_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Frozen order-`108` coefficient of the cleared numerator
quotient (`h^6` of `degreeZeroSourceJetQuotient810`,
`h^5` of `degreeZeroSourceJetPlus810`). -/
def degreeZeroOrder108810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
  degreeZeroOrder108Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder108Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder108Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder108Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder108Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder108Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder108Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder108Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder108Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder108Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder108Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder108Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder108Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder108Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder108Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder108Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder108Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder108Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder108Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder108Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder108Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder108Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder108Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder108Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder108Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda

/-! ## Order `109` (quotient `h^7`, Plus `h^6`) -/

/-- Order-`109` contribution of Plus block `0`. -/
def degreeZeroOrder109Block0_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`109` contribution of Plus block `1`. -/
def degreeZeroOrder109Block1_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (1550364171722293248 : R) * t0 * a4 ^ 2 * a1 * lambda
    + (3100728343444586496 : R) * t0 * a4 * a3 * a2 * lambda
    + (516788057240764416 : R) * t0 * a3 ^ 3 * lambda
    + (3100728343444586496 : R) * v1 * u1 * a4 * a1 * lambda
    + (3100728343444586496 : R) * v1 * u1 * a3 * a2 * lambda

/-- Order-`109` contribution of Plus block `2`. -/
def degreeZeroOrder109Block2_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (516788057240764416 : R) * u1 ^ 3 * a1 * lambda

/-- Order-`109` contribution of Plus block `3`. -/
def degreeZeroOrder109Block3_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`109` contribution of Plus block `4`. -/
def degreeZeroOrder109Block4_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (4844888036632166400 : R) * t0 ^ 2 * u1 * a4 * a1 * lambda
    - (4844888036632166400 : R) * t0 ^ 2 * u1 * a3 * a2 * lambda

/-- Order-`109` contribution of Plus block `5`. -/
def degreeZeroOrder109Block5_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (4844888036632166400 : R) * t0 * v1 ^ 2 * a4 * a1 * lambda
    - (4844888036632166400 : R) * t0 * v1 ^ 2 * a3 * a2 * lambda
    - (4844888036632166400 : R) * t0 * v1 * u1 ^ 2 * a1 * lambda
    - (1614962678877388800 : R) * v1 ^ 3 * u1 * a1 * lambda

/-- Order-`109` contribution of Plus block `6`. -/
def degreeZeroOrder109Block6_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`109` contribution of Plus block `7`. -/
def degreeZeroOrder109Block7_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`109` contribution of Plus block `8`. -/
def degreeZeroOrder109Block8_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`109` contribution of Plus block `9`. -/
def degreeZeroOrder109Block9_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (6661721050369228800 : R) * t0 ^ 3 * v1 * a4 * a1 * lambda
    + (6661721050369228800 : R) * t0 ^ 3 * v1 * a3 * a2 * lambda
    + (3330860525184614400 : R) * t0 ^ 3 * u1 ^ 2 * a1 * lambda
    + (9992581575553843200 : R) * t0 ^ 2 * v1 ^ 2 * u1 * a1 * lambda
    + (1665430262592307200 : R) * t0 * v1 ^ 4 * a1 * lambda

/-- Order-`109` contribution of Plus block `10`. -/
def degreeZeroOrder109Block10_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`109` contribution of Plus block `11`. -/
def degreeZeroOrder109Block11_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`109` contribution of Plus block `12`. -/
def degreeZeroOrder109Block12_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`109` contribution of Plus block `13`. -/
def degreeZeroOrder109Block13_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1707066019157114880 : R) * t0 ^ 5 * a4 * a1 * lambda
    - (1707066019157114880 : R) * t0 ^ 5 * a3 * a2 * lambda
    - (8535330095785574400 : R) * t0 ^ 4 * v1 * u1 * a1 * lambda
    - (5690220063857049600 : R) * t0 ^ 3 * v1 ^ 3 * a1 * lambda

/-- Order-`109` contribution of Plus block `14`. -/
def degreeZeroOrder109Block14_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`109` contribution of Plus block `15`. -/
def degreeZeroOrder109Block15_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`109` contribution of Plus block `16`. -/
def degreeZeroOrder109Block16_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (1742629894556221440 : R) * t0 ^ 6 * u1 * a1 * lambda
    + (5227889683668664320 : R) * t0 ^ 5 * v1 ^ 2 * a1 * lambda

/-- Order-`109` contribution of Plus block `17`. -/
def degreeZeroOrder109Block17_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`109` contribution of Plus block `18`. -/
def degreeZeroOrder109Block18_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`109` contribution of Plus block `19`. -/
def degreeZeroOrder109Block19_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1773748285530439680 : R) * t0 ^ 7 * v1 * a1 * lambda

/-- Order-`109` contribution of Plus block `20`. -/
def degreeZeroOrder109Block20_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`109` contribution of Plus block `21`. -/
def degreeZeroOrder109Block21_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (200162566943539200 : R) * t0 ^ 9 * a1 * lambda

/-- Order-`109` contribution of Plus block `22`. -/
def degreeZeroOrder109Block22_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`109` contribution of Plus block `23`. -/
def degreeZeroOrder109Block23_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`109` contribution of Plus block `24`. -/
def degreeZeroOrder109Block24_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Frozen order-`109` coefficient of the cleared numerator
quotient (`h^7` of `degreeZeroSourceJetQuotient810`,
`h^6` of `degreeZeroSourceJetPlus810`). -/
def degreeZeroOrder109810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
  degreeZeroOrder109Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder109Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder109Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder109Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder109Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder109Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder109Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder109Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder109Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder109Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder109Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder109Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder109Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder109Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder109Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder109Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder109Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder109Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder109Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder109Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder109Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder109Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder109Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder109Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder109Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda

/-! ## Order `110` (quotient `h^8`, Plus `h^7`) -/

/-- Order-`110` contribution of Plus block `0`. -/
def degreeZeroOrder110Block0_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (288230376151711744 : R) * a4 ^ 2 * b1
    - (1152921504606846976 : R) * a4 * a3 * b2
    - (1729382256910270464 : R) * a4 * a2 * b3
    - (2305843009213693952 : R) * a4 * a1 * b4
    - (2882303761517117440 : R) * a4 * a0 * b5
    - (864691128455135232 : R) * a3 ^ 2 * b3
    - (2305843009213693952 : R) * a3 * a2 * b4
    - (2882303761517117440 : R) * a3 * a1 * b5
    - (1441151880758558720 : R) * a2 ^ 2 * b5

/-- Order-`110` contribution of Plus block `1`. -/
def degreeZeroOrder110Block1_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (3242591731706757120 : R) * t0 * a4 ^ 2 * a0
    - (6485183463413514240 : R) * t0 * a4 * a3 * a1
    - (3242591731706757120 : R) * t0 * a4 * a2 ^ 2
    - (3242591731706757120 : R) * t0 * a3 ^ 2 * a2
    - (13781014859753717760 : R) * v1 * u1 * a4 * a0
    - (13781014859753717760 : R) * v1 * u1 * a3 * a1
    - (6890507429876858880 : R) * v1 * u1 * a2 ^ 2
    - (2296835809958952960 : R) * u1 ^ 3 * a0

set_option maxHeartbeats 200000000 in
/-- Order-`110` contribution of Plus block `2`. -/
def degreeZeroOrder110Block2_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (648518346341351424 : R) * t0 * u1 * a4 * b1
    + (1297036692682702848 : R) * t0 * u1 * a3 * b2
    + (1945555039024054272 : R) * t0 * u1 * a2 * b3
    + (2594073385365405696 : R) * t0 * u1 * a1 * b4
    + (3242591731706757120 : R) * t0 * u1 * a0 * b5
    + (3891110078048108544 : R) * t0 * a4 * a0 * b62
    + (3891110078048108544 : R) * t0 * a3 * a1 * b62
    + (1945555039024054272 : R) * t0 * a2 ^ 2 * b62
    + (324259173170675712 : R) * v1 ^ 2 * a4 * b1
    + (648518346341351424 : R) * v1 ^ 2 * a3 * b2
    + (972777519512027136 : R) * v1 ^ 2 * a2 * b3
    + (1297036692682702848 : R) * v1 ^ 2 * a1 * b4
    + (1621295865853378560 : R) * v1 ^ 2 * a0 * b5
    + (324259173170675712 : R) * v1 * u1 ^ 2 * b1

/-- Order-`110` contribution of Plus block `3`. -/
def degreeZeroOrder110Block3_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (3891110078048108544 : R) * v1 * u1 * a0 * b62
    + (4539628424389459968 : R) * v1 * a4 * a0 * w1
    + (4539628424389459968 : R) * v1 * a3 * a1 * w1
    + (2269814212194729984 : R) * v1 * a2 ^ 2 * w1
    + (2269814212194729984 : R) * u1 ^ 2 * a0 * w1
    + (5188146770730811392 : R) * u1 * a4 * a0 * s1
    + (5188146770730811392 : R) * u1 * a3 * a1 * s1
    + (2594073385365405696 : R) * u1 * a2 ^ 2 * s1

/-- Order-`110` contribution of Plus block `4`. -/
def degreeZeroOrder110Block4_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (6029194001142251520 : R) * t0 ^ 2 * u1 * a4 * a0
    + (6029194001142251520 : R) * t0 ^ 2 * u1 * a3 * a1
    + (3014597000571125760 : R) * t0 ^ 2 * u1 * a2 ^ 2
    + (13781014859753717760 : R) * t0 * v1 ^ 2 * a4 * a0
    + (13781014859753717760 : R) * t0 * v1 ^ 2 * a3 * a1
    + (6890507429876858880 : R) * t0 * v1 ^ 2 * a2 ^ 2
    + (13781014859753717760 : R) * t0 * v1 * u1 ^ 2 * a0
    + (7177611906121728000 : R) * v1 ^ 3 * u1 * a0

/-- Order-`110` contribution of Plus block `5`. -/
def degreeZeroOrder110Block5_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (689050742987685888 : R) * t0 ^ 2 * v1 * a4 * b1
    - (1378101485975371776 : R) * t0 ^ 2 * v1 * a3 * b2
    - (2067152228963057664 : R) * t0 ^ 2 * v1 * a2 * b3
    - (2756202971950743552 : R) * t0 ^ 2 * v1 * a1 * b4
    - (3445253714938429440 : R) * t0 ^ 2 * v1 * a0 * b5
    - (344525371493842944 : R) * t0 ^ 2 * u1 ^ 2 * b1
    - (4134304457926115328 : R) * t0 ^ 2 * u1 * a0 * b62

set_option maxHeartbeats 200000000 in
/-- Order-`110` contribution of Plus block `6`. -/
def degreeZeroOrder110Block6_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (4823355200913801216 : R) * t0 ^ 2 * a4 * a0 * w1
    - (4823355200913801216 : R) * t0 ^ 2 * a3 * a1 * w1
    - (2411677600456900608 : R) * t0 ^ 2 * a2 ^ 2 * w1
    - (689050742987685888 : R) * t0 * v1 ^ 2 * u1 * b1
    - (4134304457926115328 : R) * t0 * v1 ^ 2 * a0 * b62
    - (9646710401827602432 : R) * t0 * v1 * u1 * a0 * w1
    - (11024811887802974208 : R) * t0 * v1 * a4 * a0 * s1
    - (11024811887802974208 : R) * t0 * v1 * a3 * a1 * s1
    - (5512405943901487104 : R) * t0 * v1 * a2 ^ 2 * s1
    - (5512405943901487104 : R) * t0 * u1 ^ 2 * a0 * s1

/-- Order-`110` contribution of Plus block `7`. -/
def degreeZeroOrder110Block7_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (57420895248973824 : R) * v1 ^ 4 * b1
    - (1607785066971267072 : R) * v1 ^ 3 * a0 * w1
    - (5512405943901487104 : R) * v1 ^ 2 * u1 * a0 * s1

/-- Order-`110` contribution of Plus block `8`. -/
def degreeZeroOrder110Block8_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (5383208929591296000 : R) * t0 ^ 3 * v1 * a4 * a0
    - (5383208929591296000 : R) * t0 ^ 3 * v1 * a3 * a1
    - (2691604464795648000 : R) * t0 ^ 3 * v1 * a2 ^ 2
    - (2691604464795648000 : R) * t0 ^ 3 * u1 ^ 2 * a0
    - (20187033485967360000 : R) * t0 ^ 2 * v1 ^ 2 * u1 * a0
    - (5383208929591296000 : R) * t0 * v1 ^ 4 * a0

/-- Order-`110` contribution of Plus block `9`. -/
def degreeZeroOrder110Block9_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (179440297653043200 : R) * t0 ^ 4 * a4 * b1
    + (358880595306086400 : R) * t0 ^ 4 * a3 * b2
    + (538320892959129600 : R) * t0 ^ 4 * a2 * b3
    + (717761190612172800 : R) * t0 ^ 4 * a1 * b4
    + (897201488265216000 : R) * t0 ^ 4 * a0 * b5
    + (717761190612172800 : R) * t0 ^ 3 * v1 * u1 * b1
    + (4306567143673036800 : R) * t0 ^ 3 * v1 * a0 * b62

/-- Order-`110` contribution of Plus block `10`. -/
def degreeZeroOrder110Block10_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (5024328334285209600 : R) * t0 ^ 3 * u1 * a0 * w1
    + (5742089524897382400 : R) * t0 ^ 3 * a4 * a0 * s1
    + (5742089524897382400 : R) * t0 ^ 3 * a3 * a1 * s1
    + (2871044762448691200 : R) * t0 ^ 3 * a2 ^ 2 * s1
    + (358880595306086400 : R) * t0 ^ 2 * v1 ^ 3 * b1
    + (7536492501427814400 : R) * t0 ^ 2 * v1 ^ 2 * a0 * w1
    + (17226268574692147200 : R) * t0 ^ 2 * v1 * u1 * a0 * s1

/-- Order-`110` contribution of Plus block `11`. -/
def degreeZeroOrder110Block11_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (5742089524897382400 : R) * t0 * v1 ^ 3 * a0 * s1

/-- Order-`110` contribution of Plus block `12`. -/
def degreeZeroOrder110Block12_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (740191227818803200 : R) * t0 ^ 5 * a4 * a0
    - (740191227818803200 : R) * t0 ^ 5 * a3 * a1
    - (370095613909401600 : R) * t0 ^ 5 * a2 ^ 2
    + (4626195173867520000 : R) * t0 ^ 4 * v1 * u1 * a0
    + (8635564324552704000 : R) * t0 ^ 3 * v1 ^ 3 * a0

/-- Order-`110` contribution of Plus block `13`. -/
def degreeZeroOrder110Block13_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (148038245563760640 : R) * t0 ^ 5 * u1 * b1
    - (888229473382563840 : R) * t0 ^ 5 * a0 * b62
    - (370095613909401600 : R) * t0 ^ 4 * v1 ^ 2 * b1

/-- Order-`110` contribution of Plus block `14`. -/
def degreeZeroOrder110Block14_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (5181338594731622400 : R) * t0 ^ 4 * v1 * a0 * w1
    - (5921529822550425600 : R) * t0 ^ 4 * u1 * a0 * s1
    - (11843059645100851200 : R) * t0 ^ 3 * v1 ^ 2 * a0 * s1

/-- Order-`110` contribution of Plus block `15`. -/
def degreeZeroOrder110Block15_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (790308342202368000 : R) * t0 ^ 6 * u1 * a0
    - (1896740021285683200 : R) * t0 ^ 5 * v1 ^ 2 * a0

/-- Order-`110` contribution of Plus block `16`. -/
def degreeZeroOrder110Block16_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`110` contribution of Plus block `17`. -/
def degreeZeroOrder110Block17_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (126449334752378880 : R) * t0 ^ 6 * v1 * b1
    + (885145343266652160 : R) * t0 ^ 6 * a0 * w1
    + (6069568068114186240 : R) * t0 ^ 5 * v1 * a0 * s1

/-- Order-`110` contribution of Plus block `18`. -/
def degreeZeroOrder110Block18_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (829823759312486400 : R) * t0 ^ 7 * v1 * a0

/-- Order-`110` contribution of Plus block `19`. -/
def degreeZeroOrder110Block19_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (13830395988541440 : R) * t0 ^ 8 * b1
    - (885145343266652160 : R) * t0 ^ 7 * a0 * s1

/-- Order-`110` contribution of Plus block `20`. -/
def degreeZeroOrder110Block20_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (218981269818572800 : R) * t0 ^ 9 * a0

/-- Order-`110` contribution of Plus block `21`. -/
def degreeZeroOrder110Block21_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`110` contribution of Plus block `22`. -/
def degreeZeroOrder110Block22_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`110` contribution of Plus block `23`. -/
def degreeZeroOrder110Block23_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`110` contribution of Plus block `24`. -/
def degreeZeroOrder110Block24_810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Frozen order-`110` coefficient of the cleared numerator
quotient (`h^8` of `degreeZeroSourceJetQuotient810`,
`h^7` of `degreeZeroSourceJetPlus810`). -/
def degreeZeroOrder110810 {R : Type*} [CommRing R] (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
  degreeZeroOrder110Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda

/-! ## Remaining Plus factor after order `110` (Plus `h^8` and higher) -/

set_option maxHeartbeats 200000000 in
/-- Order-`110` Plus remainder contributed by Plus block `0`. -/
def degreeZeroOrder110PlusBlock0_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (648518346341351424 : R) * h ^ 8 * a0 ^ 2 * lambda
    + (4611686018427387904 : R) * h ^ 7 * a0 * b1
    - (1459166279268040704 : R) * h ^ 6 * t0 * a1 * a0 * lambda
    - (576460752303423488 : R) * h ^ 5 * t0 * a1 * b1
    - (1152921504606846976 : R) * h ^ 5 * t0 * a0 * b2
    + (6485183463413514240 : R) * h ^ 5 * v1 * a1 * a0
    - (1459166279268040704 : R) * h ^ 4 * v1 * a2 * a0 * lambda
    - (729583139634020352 : R) * h ^ 4 * v1 * a1 ^ 2 * lambda
    - (576460752303423488 : R) * h ^ 3 * v1 * a2 * b1
    - (1152921504606846976 : R) * h ^ 3 * v1 * a1 * b2
    - (1729382256910270464 : R) * h ^ 3 * v1 * a0 * b3
    + (6485183463413514240 : R) * h ^ 3 * u1 * a2 * a0
    + (3242591731706757120 : R) * h ^ 3 * u1 * a1 ^ 2
    - (4035225266123964416 : R) * h ^ 3 * a2 * a0 * w1
    - (2017612633061982208 : R) * h ^ 3 * a1 ^ 2 * w1
    - (1459166279268040704 : R) * h ^ 2 * u1 * a3 * a0 * lambda
    - (1459166279268040704 : R) * h ^ 2 * u1 * a2 * a1 * lambda
    - (576460752303423488 : R) * h * u1 * a3 * b1
    - (1152921504606846976 : R) * h * u1 * a2 * b2
    - (1729382256910270464 : R) * h * u1 * a1 * b3
    - (2305843009213693952 : R) * h * u1 * a0 * b4
    + (6485183463413514240 : R) * h * a4 * a3 * a0
    + (6485183463413514240 : R) * h * a4 * a2 * a1
    + (3242591731706757120 : R) * h * a3 ^ 2 * a1
    + (3242591731706757120 : R) * h * a3 * a2 ^ 2
    - (3458764513820540928 : R) * h * a3 * a0 * b62
    - (3458764513820540928 : R) * h * a2 * a1 * b62
    - (729583139634020352 : R) * a4 ^ 2 * a0 * lambda
    - (1459166279268040704 : R) * a4 * a3 * a1 * lambda
    - (729583139634020352 : R) * a4 * a2 ^ 2 * lambda
    - (729583139634020352 : R) * a3 ^ 2 * a2 * lambda

set_option maxHeartbeats 200000000 in
/-- Order-`110` Plus remainder contributed by Plus block `1`. -/
def degreeZeroOrder110PlusBlock1_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (405323966463344640 : R) * h ^ 5 * t0 ^ 2 * a1 * a0
    - (4611686018427387904 : R) * h ^ 5 * a1 * a0 * s1
    + (1550364171722293248 : R) * h ^ 4 * t0 ^ 2 * a2 * a0 * lambda
    + (775182085861146624 : R) * h ^ 4 * t0 ^ 2 * a1 ^ 2 * lambda
    - (6485183463413514240 : R) * h ^ 3 * t0 * v1 * a2 * a0
    - (3242591731706757120 : R) * h ^ 3 * t0 * v1 * a1 ^ 2
    + (3100728343444586496 : R) * h ^ 2 * t0 * v1 * a3 * a0 * lambda
    + (3100728343444586496 : R) * h ^ 2 * t0 * v1 * a2 * a1 * lambda
    - (6485183463413514240 : R) * h * t0 * u1 * a3 * a0
    - (6485183463413514240 : R) * h * t0 * u1 * a2 * a1
    - (6890507429876858880 : R) * h * v1 ^ 2 * a3 * a0
    - (6890507429876858880 : R) * h * v1 ^ 2 * a2 * a1
    + (3100728343444586496 : R) * t0 * u1 * a4 * a0 * lambda
    + (3100728343444586496 : R) * t0 * u1 * a3 * a1 * lambda
    + (1550364171722293248 : R) * t0 * u1 * a2 ^ 2 * lambda
    + (1550364171722293248 : R) * v1 ^ 2 * a4 * a0 * lambda
    + (1550364171722293248 : R) * v1 ^ 2 * a3 * a1 * lambda
    + (775182085861146624 : R) * v1 ^ 2 * a2 ^ 2 * lambda
    + (1550364171722293248 : R) * v1 * u1 ^ 2 * a0 * lambda

set_option maxHeartbeats 200000000 in
/-- Order-`110` Plus remainder contributed by Plus block `2`. -/
def degreeZeroOrder110PlusBlock2_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (324259173170675712 : R) * h ^ 3 * t0 ^ 2 * a2 * b1
    + (648518346341351424 : R) * h ^ 3 * t0 ^ 2 * a1 * b2
    + (972777519512027136 : R) * h ^ 3 * t0 ^ 2 * a0 * b3
    + (5188146770730811392 : R) * h ^ 3 * t0 * a2 * a0 * s1
    + (2594073385365405696 : R) * h ^ 3 * t0 * a1 ^ 2 * s1
    + (648518346341351424 : R) * h * t0 * v1 * a3 * b1
    + (1297036692682702848 : R) * h * t0 * v1 * a2 * b2
    + (1945555039024054272 : R) * h * t0 * v1 * a1 * b3
    + (2594073385365405696 : R) * h * t0 * v1 * a0 * b4
    + (4539628424389459968 : R) * h * t0 * a3 * a0 * w1
    + (4539628424389459968 : R) * h * t0 * a2 * a1 * w1

/-- Order-`110` Plus remainder contributed by Plus block `3`. -/
def degreeZeroOrder110PlusBlock3_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (574208952489738240 : R) * h ^ 3 * t0 ^ 3 * a2 * a0
    - (287104476244869120 : R) * h ^ 3 * t0 ^ 3 * a1 ^ 2
    + (6029194001142251520 : R) * h * t0 ^ 2 * v1 * a3 * a0
    + (6029194001142251520 : R) * h * t0 ^ 2 * v1 * a2 * a1
    + (5188146770730811392 : R) * h * v1 * a3 * a0 * s1
    + (5188146770730811392 : R) * h * v1 * a2 * a1 * s1

/-- Order-`110` Plus remainder contributed by Plus block `4`. -/
def degreeZeroOrder110PlusBlock4_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1614962678877388800 : R) * h ^ 2 * t0 ^ 3 * a3 * a0 * lambda
    - (1614962678877388800 : R) * h ^ 2 * t0 ^ 3 * a2 * a1 * lambda
    - (4844888036632166400 : R) * t0 ^ 2 * v1 * a4 * a0 * lambda
    - (4844888036632166400 : R) * t0 ^ 2 * v1 * a3 * a1 * lambda
    - (2422444018316083200 : R) * t0 ^ 2 * v1 * a2 ^ 2 * lambda
    - (2422444018316083200 : R) * t0 ^ 2 * u1 ^ 2 * a0 * lambda

/-- Order-`110` Plus remainder contributed by Plus block `5`. -/
def degreeZeroOrder110PlusBlock5_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (229683580995895296 : R) * h * t0 ^ 3 * a3 * b1
    - (459367161991790592 : R) * h * t0 ^ 3 * a2 * b2
    - (689050742987685888 : R) * h * t0 ^ 3 * a1 * b3
    - (918734323983581184 : R) * h * t0 ^ 3 * a0 * b4
    - (4844888036632166400 : R) * t0 * v1 ^ 2 * u1 * a0 * lambda
    - (403740669719347200 : R) * v1 ^ 4 * a0 * lambda

/-- Order-`110` Plus remainder contributed by Plus block `6`. -/
def degreeZeroOrder110PlusBlock6_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (5512405943901487104 : R) * h * t0 ^ 2 * a3 * a0 * s1
    - (5512405943901487104 : R) * h * t0 ^ 2 * a2 * a1 * s1

/-- Order-`110` Plus remainder contributed by Plus block `7`. -/
def degreeZeroOrder110PlusBlock7_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`110` Plus remainder contributed by Plus block `8`. -/
def degreeZeroOrder110PlusBlock8_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (672901116198912000 : R) * h * t0 ^ 4 * a3 * a0
    + (672901116198912000 : R) * h * t0 ^ 4 * a2 * a1
    + (1665430262592307200 : R) * t0 ^ 4 * a4 * a0 * lambda
    + (1665430262592307200 : R) * t0 ^ 4 * a3 * a1 * lambda

/-- Order-`110` Plus remainder contributed by Plus block `9`. -/
def degreeZeroOrder110PlusBlock9_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (832715131296153600 : R) * t0 ^ 4 * a2 ^ 2 * lambda
    + (6661721050369228800 : R) * t0 ^ 3 * v1 * u1 * a0 * lambda
    + (3330860525184614400 : R) * t0 ^ 2 * v1 ^ 3 * a0 * lambda

/-- Order-`110` Plus remainder contributed by Plus block `10`. -/
def degreeZeroOrder110PlusBlock10_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`110` Plus remainder contributed by Plus block `11`. -/
def degreeZeroOrder110PlusBlock11_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`110` Plus remainder contributed by Plus block `12`. -/
def degreeZeroOrder110PlusBlock12_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`110` Plus remainder contributed by Plus block `13`. -/
def degreeZeroOrder110PlusBlock13_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (1707066019157114880 : R) * t0 ^ 5 * u1 * a0 * lambda
    - (4267665047892787200 : R) * t0 ^ 4 * v1 ^ 2 * a0 * lambda

/-- Order-`110` Plus remainder contributed by Plus block `14`. -/
def degreeZeroOrder110PlusBlock14_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`110` Plus remainder contributed by Plus block `15`. -/
def degreeZeroOrder110PlusBlock15_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`110` Plus remainder contributed by Plus block `16`. -/
def degreeZeroOrder110PlusBlock16_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    (1742629894556221440 : R) * t0 ^ 6 * v1 * a0 * lambda

/-- Order-`110` Plus remainder contributed by Plus block `17`. -/
def degreeZeroOrder110PlusBlock17_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`110` Plus remainder contributed by Plus block `18`. -/
def degreeZeroOrder110PlusBlock18_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`110` Plus remainder contributed by Plus block `19`. -/
def degreeZeroOrder110PlusBlock19_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    - (221718535691304960 : R) * t0 ^ 8 * a0 * lambda

/-- Order-`110` Plus remainder contributed by Plus block `20`. -/
def degreeZeroOrder110PlusBlock20_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`110` Plus remainder contributed by Plus block `21`. -/
def degreeZeroOrder110PlusBlock21_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`110` Plus remainder contributed by Plus block `22`. -/
def degreeZeroOrder110PlusBlock22_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`110` Plus remainder contributed by Plus block `23`. -/
def degreeZeroOrder110PlusBlock23_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Order-`110` Plus remainder contributed by Plus block `24`. -/
def degreeZeroOrder110PlusBlock24_810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
    0

/-- Remaining factor of `degreeZeroSourceJetPlus810` after the
orders `103` through `110` are peeled: the `h^8`-and-higher terms,
shifted down by `h^8`. -/
def degreeZeroOrder110Plus810 {R : Type*} [CommRing R] (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) : R :=
  degreeZeroOrder110PlusBlock0_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110PlusBlock1_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110PlusBlock2_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110PlusBlock3_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110PlusBlock4_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110PlusBlock5_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110PlusBlock6_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110PlusBlock7_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110PlusBlock8_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110PlusBlock9_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110PlusBlock10_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110PlusBlock11_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110PlusBlock12_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110PlusBlock13_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110PlusBlock14_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110PlusBlock15_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110PlusBlock16_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110PlusBlock17_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110PlusBlock18_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110PlusBlock19_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110PlusBlock20_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110PlusBlock21_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110PlusBlock22_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110PlusBlock23_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
  degreeZeroOrder110PlusBlock24_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda

/-! ## Blocked Plus expansions through order `110` -/

section DegreeZeroTowerScale810

variable {R : Type*} [CommRing R]


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock0_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock0_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block0_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock0_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock0_810, degreeZeroOrder103Block0_810, degreeZeroOrder104Block0_810, degreeZeroOrder105Block0_810, degreeZeroOrder106Block0_810, degreeZeroOrder107Block0_810, degreeZeroOrder108Block0_810, degreeZeroOrder109Block0_810, degreeZeroOrder110Block0_810, degreeZeroOrder110PlusBlock0_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock1_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock1_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block1_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock1_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock1_810, degreeZeroOrder103Block1_810, degreeZeroOrder104Block1_810, degreeZeroOrder105Block1_810, degreeZeroOrder106Block1_810, degreeZeroOrder107Block1_810, degreeZeroOrder108Block1_810, degreeZeroOrder109Block1_810, degreeZeroOrder110Block1_810, degreeZeroOrder110PlusBlock1_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock2_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock2_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block2_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock2_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock2_810, degreeZeroOrder103Block2_810, degreeZeroOrder104Block2_810, degreeZeroOrder105Block2_810, degreeZeroOrder106Block2_810, degreeZeroOrder107Block2_810, degreeZeroOrder108Block2_810, degreeZeroOrder109Block2_810, degreeZeroOrder110Block2_810, degreeZeroOrder110PlusBlock2_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock3_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock3_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block3_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock3_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock3_810, degreeZeroOrder103Block3_810, degreeZeroOrder104Block3_810, degreeZeroOrder105Block3_810, degreeZeroOrder106Block3_810, degreeZeroOrder107Block3_810, degreeZeroOrder108Block3_810, degreeZeroOrder109Block3_810, degreeZeroOrder110Block3_810, degreeZeroOrder110PlusBlock3_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock4_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock4_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block4_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock4_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock4_810, degreeZeroOrder103Block4_810, degreeZeroOrder104Block4_810, degreeZeroOrder105Block4_810, degreeZeroOrder106Block4_810, degreeZeroOrder107Block4_810, degreeZeroOrder108Block4_810, degreeZeroOrder109Block4_810, degreeZeroOrder110Block4_810, degreeZeroOrder110PlusBlock4_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock5_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock5_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block5_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock5_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock5_810, degreeZeroOrder103Block5_810, degreeZeroOrder104Block5_810, degreeZeroOrder105Block5_810, degreeZeroOrder106Block5_810, degreeZeroOrder107Block5_810, degreeZeroOrder108Block5_810, degreeZeroOrder109Block5_810, degreeZeroOrder110Block5_810, degreeZeroOrder110PlusBlock5_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock6_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock6_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block6_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock6_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock6_810, degreeZeroOrder103Block6_810, degreeZeroOrder104Block6_810, degreeZeroOrder105Block6_810, degreeZeroOrder106Block6_810, degreeZeroOrder107Block6_810, degreeZeroOrder108Block6_810, degreeZeroOrder109Block6_810, degreeZeroOrder110Block6_810, degreeZeroOrder110PlusBlock6_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock7_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock7_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block7_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock7_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock7_810, degreeZeroOrder103Block7_810, degreeZeroOrder104Block7_810, degreeZeroOrder105Block7_810, degreeZeroOrder106Block7_810, degreeZeroOrder107Block7_810, degreeZeroOrder108Block7_810, degreeZeroOrder109Block7_810, degreeZeroOrder110Block7_810, degreeZeroOrder110PlusBlock7_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock8_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock8_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block8_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock8_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock8_810, degreeZeroOrder103Block8_810, degreeZeroOrder104Block8_810, degreeZeroOrder105Block8_810, degreeZeroOrder106Block8_810, degreeZeroOrder107Block8_810, degreeZeroOrder108Block8_810, degreeZeroOrder109Block8_810, degreeZeroOrder110Block8_810, degreeZeroOrder110PlusBlock8_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock9_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock9_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block9_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock9_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock9_810, degreeZeroOrder103Block9_810, degreeZeroOrder104Block9_810, degreeZeroOrder105Block9_810, degreeZeroOrder106Block9_810, degreeZeroOrder107Block9_810, degreeZeroOrder108Block9_810, degreeZeroOrder109Block9_810, degreeZeroOrder110Block9_810, degreeZeroOrder110PlusBlock9_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock10_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock10_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block10_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock10_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock10_810, degreeZeroOrder103Block10_810, degreeZeroOrder104Block10_810, degreeZeroOrder105Block10_810, degreeZeroOrder106Block10_810, degreeZeroOrder107Block10_810, degreeZeroOrder108Block10_810, degreeZeroOrder109Block10_810, degreeZeroOrder110Block10_810, degreeZeroOrder110PlusBlock10_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock11_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock11_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block11_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock11_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock11_810, degreeZeroOrder103Block11_810, degreeZeroOrder104Block11_810, degreeZeroOrder105Block11_810, degreeZeroOrder106Block11_810, degreeZeroOrder107Block11_810, degreeZeroOrder108Block11_810, degreeZeroOrder109Block11_810, degreeZeroOrder110Block11_810, degreeZeroOrder110PlusBlock11_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock12_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock12_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block12_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock12_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock12_810, degreeZeroOrder103Block12_810, degreeZeroOrder104Block12_810, degreeZeroOrder105Block12_810, degreeZeroOrder106Block12_810, degreeZeroOrder107Block12_810, degreeZeroOrder108Block12_810, degreeZeroOrder109Block12_810, degreeZeroOrder110Block12_810, degreeZeroOrder110PlusBlock12_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock13_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock13_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block13_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock13_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock13_810, degreeZeroOrder103Block13_810, degreeZeroOrder104Block13_810, degreeZeroOrder105Block13_810, degreeZeroOrder106Block13_810, degreeZeroOrder107Block13_810, degreeZeroOrder108Block13_810, degreeZeroOrder109Block13_810, degreeZeroOrder110Block13_810, degreeZeroOrder110PlusBlock13_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock14_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock14_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block14_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock14_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock14_810, degreeZeroOrder103Block14_810, degreeZeroOrder104Block14_810, degreeZeroOrder105Block14_810, degreeZeroOrder106Block14_810, degreeZeroOrder107Block14_810, degreeZeroOrder108Block14_810, degreeZeroOrder109Block14_810, degreeZeroOrder110Block14_810, degreeZeroOrder110PlusBlock14_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock15_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock15_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block15_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock15_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock15_810, degreeZeroOrder103Block15_810, degreeZeroOrder104Block15_810, degreeZeroOrder105Block15_810, degreeZeroOrder106Block15_810, degreeZeroOrder107Block15_810, degreeZeroOrder108Block15_810, degreeZeroOrder109Block15_810, degreeZeroOrder110Block15_810, degreeZeroOrder110PlusBlock15_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock16_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock16_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block16_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock16_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock16_810, degreeZeroOrder103Block16_810, degreeZeroOrder104Block16_810, degreeZeroOrder105Block16_810, degreeZeroOrder106Block16_810, degreeZeroOrder107Block16_810, degreeZeroOrder108Block16_810, degreeZeroOrder109Block16_810, degreeZeroOrder110Block16_810, degreeZeroOrder110PlusBlock16_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock17_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock17_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block17_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock17_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock17_810, degreeZeroOrder103Block17_810, degreeZeroOrder104Block17_810, degreeZeroOrder105Block17_810, degreeZeroOrder106Block17_810, degreeZeroOrder107Block17_810, degreeZeroOrder108Block17_810, degreeZeroOrder109Block17_810, degreeZeroOrder110Block17_810, degreeZeroOrder110PlusBlock17_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock18_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock18_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block18_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock18_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock18_810, degreeZeroOrder103Block18_810, degreeZeroOrder104Block18_810, degreeZeroOrder105Block18_810, degreeZeroOrder106Block18_810, degreeZeroOrder107Block18_810, degreeZeroOrder108Block18_810, degreeZeroOrder109Block18_810, degreeZeroOrder110Block18_810, degreeZeroOrder110PlusBlock18_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock19_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock19_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block19_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock19_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock19_810, degreeZeroOrder103Block19_810, degreeZeroOrder104Block19_810, degreeZeroOrder105Block19_810, degreeZeroOrder106Block19_810, degreeZeroOrder107Block19_810, degreeZeroOrder108Block19_810, degreeZeroOrder109Block19_810, degreeZeroOrder110Block19_810, degreeZeroOrder110PlusBlock19_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock20_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock20_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block20_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock20_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock20_810, degreeZeroOrder103Block20_810, degreeZeroOrder104Block20_810, degreeZeroOrder105Block20_810, degreeZeroOrder106Block20_810, degreeZeroOrder107Block20_810, degreeZeroOrder108Block20_810, degreeZeroOrder109Block20_810, degreeZeroOrder110Block20_810, degreeZeroOrder110PlusBlock20_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock21_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock21_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block21_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock21_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock21_810, degreeZeroOrder103Block21_810, degreeZeroOrder104Block21_810, degreeZeroOrder105Block21_810, degreeZeroOrder106Block21_810, degreeZeroOrder107Block21_810, degreeZeroOrder108Block21_810, degreeZeroOrder109Block21_810, degreeZeroOrder110Block21_810, degreeZeroOrder110PlusBlock21_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock22_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock22_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block22_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock22_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock22_810, degreeZeroOrder103Block22_810, degreeZeroOrder104Block22_810, degreeZeroOrder105Block22_810, degreeZeroOrder106Block22_810, degreeZeroOrder107Block22_810, degreeZeroOrder108Block22_810, degreeZeroOrder109Block22_810, degreeZeroOrder110Block22_810, degreeZeroOrder110PlusBlock22_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock23_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock23_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block23_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock23_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock23_810, degreeZeroOrder103Block23_810, degreeZeroOrder104Block23_810, degreeZeroOrder105Block23_810, degreeZeroOrder106Block23_810, degreeZeroOrder107Block23_810, degreeZeroOrder108Block23_810, degreeZeroOrder109Block23_810, degreeZeroOrder110Block23_810, degreeZeroOrder110PlusBlock23_810]
  ring


set_option maxHeartbeats 200000000 in
private theorem degreeZeroSourceJetPlusBlock24_810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlusBlock24_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110Block24_810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110PlusBlock24_810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda := by
  simp only [degreeZeroSourceJetPlusBlock24_810, degreeZeroOrder103Block24_810, degreeZeroOrder104Block24_810, degreeZeroOrder105Block24_810, degreeZeroOrder106Block24_810, degreeZeroOrder107Block24_810, degreeZeroOrder108Block24_810, degreeZeroOrder109Block24_810, degreeZeroOrder110Block24_810, degreeZeroOrder110PlusBlock24_810]
  ring


set_option maxHeartbeats 800000000 in
/-- Plus remainder through order `110`. -/
theorem degreeZeroSourceJetPlus810_orders103to110
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h * degreeZeroOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 2 * degreeZeroOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 3 * degreeZeroOrder106810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 4 * degreeZeroOrder107810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 5 * degreeZeroOrder108810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 6 * degreeZeroOrder109810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 7 * degreeZeroOrder110810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda +
        h ^ 8 * degreeZeroOrder110Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda := by
  have hb0 := degreeZeroSourceJetPlusBlock0_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb1 := degreeZeroSourceJetPlusBlock1_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb2 := degreeZeroSourceJetPlusBlock2_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb3 := degreeZeroSourceJetPlusBlock3_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb4 := degreeZeroSourceJetPlusBlock4_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb5 := degreeZeroSourceJetPlusBlock5_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb6 := degreeZeroSourceJetPlusBlock6_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb7 := degreeZeroSourceJetPlusBlock7_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb8 := degreeZeroSourceJetPlusBlock8_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb9 := degreeZeroSourceJetPlusBlock9_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb10 := degreeZeroSourceJetPlusBlock10_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb11 := degreeZeroSourceJetPlusBlock11_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb12 := degreeZeroSourceJetPlusBlock12_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb13 := degreeZeroSourceJetPlusBlock13_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb14 := degreeZeroSourceJetPlusBlock14_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb15 := degreeZeroSourceJetPlusBlock15_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb16 := degreeZeroSourceJetPlusBlock16_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb17 := degreeZeroSourceJetPlusBlock17_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb18 := degreeZeroSourceJetPlusBlock18_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb19 := degreeZeroSourceJetPlusBlock19_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb20 := degreeZeroSourceJetPlusBlock20_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb21 := degreeZeroSourceJetPlusBlock21_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb22 := degreeZeroSourceJetPlusBlock22_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb23 := degreeZeroSourceJetPlusBlock23_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  have hb24 := degreeZeroSourceJetPlusBlock24_810_orders103to110
    h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda
  simp only [degreeZeroSourceJetPlus810]
  rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14,
    hb15, hb16, hb17, hb18, hb19, hb20, hb21, hb22, hb23, hb24]
  simp only [degreeZeroOrder103810, degreeZeroOrder104810, degreeZeroOrder105810, degreeZeroOrder106810, degreeZeroOrder107810, degreeZeroOrder108810, degreeZeroOrder109810, degreeZeroOrder110810, degreeZeroOrder110Plus810]
  ring

#print axioms degreeZeroSourceJetPlus810_orders103to110

theorem degreeZeroSourceJetPlus810_zero
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    degreeZeroSourceJetPlus810 0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda =
      degreeZeroOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda := by
  simpa using degreeZeroSourceJetPlus810_orders103to110
    0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda

#print axioms degreeZeroSourceJetPlus810_zero

set_option maxHeartbeats 800000000 in
/-- Quotient expansion through order `110`. -/
theorem degreeZeroSourceJetQuotient810_orders103to110
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
        h ^ 9 * degreeZeroOrder110Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda := by
  rw [degreeZeroSourceJetQuotient810_orderExpansion,
    degreeZeroSourceJetPlus810_orders103to110]
  ring

#print axioms degreeZeroSourceJetQuotient810_orders103to110

end DegreeZeroTowerScale810

/-! ## Ring maps and evaluation -/


section DegreeZeroTowerMap810


variable {R S : Type*} [CommRing R] [CommRing S]


set_option maxHeartbeats 800000000 in
theorem map_degreeZeroOrder103810
    (phi : R →+* S) (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (degreeZeroOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      degreeZeroOrder103810 (phi t0) (phi v1) (phi u1) (phi a4) (phi a3)
        (phi a2) (phi a1) (phi a0) (phi s1) (phi w1) (phi b62) (phi b5)
        (phi b4) (phi b3) (phi b2) (phi b1) (phi lambda) := by
  simp only [degreeZeroOrder103810, degreeZeroOrder103Block0_810, degreeZeroOrder103Block1_810, degreeZeroOrder103Block2_810, degreeZeroOrder103Block3_810, degreeZeroOrder103Block4_810, degreeZeroOrder103Block5_810, degreeZeroOrder103Block6_810, degreeZeroOrder103Block7_810, degreeZeroOrder103Block8_810, degreeZeroOrder103Block9_810, degreeZeroOrder103Block10_810, degreeZeroOrder103Block11_810, degreeZeroOrder103Block12_810, degreeZeroOrder103Block13_810, degreeZeroOrder103Block14_810, degreeZeroOrder103Block15_810, degreeZeroOrder103Block16_810, degreeZeroOrder103Block17_810, degreeZeroOrder103Block18_810, degreeZeroOrder103Block19_810, degreeZeroOrder103Block20_810, degreeZeroOrder103Block21_810, degreeZeroOrder103Block22_810, degreeZeroOrder103Block23_810, degreeZeroOrder103Block24_810, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, map_zero]


set_option maxHeartbeats 800000000 in
theorem map_degreeZeroOrder104810
    (phi : R →+* S) (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (degreeZeroOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      degreeZeroOrder104810 (phi t0) (phi v1) (phi u1) (phi a4) (phi a3)
        (phi a2) (phi a1) (phi a0) (phi s1) (phi w1) (phi b62) (phi b5)
        (phi b4) (phi b3) (phi b2) (phi b1) (phi lambda) := by
  simp only [degreeZeroOrder104810, degreeZeroOrder104Block0_810, degreeZeroOrder104Block1_810, degreeZeroOrder104Block2_810, degreeZeroOrder104Block3_810, degreeZeroOrder104Block4_810, degreeZeroOrder104Block5_810, degreeZeroOrder104Block6_810, degreeZeroOrder104Block7_810, degreeZeroOrder104Block8_810, degreeZeroOrder104Block9_810, degreeZeroOrder104Block10_810, degreeZeroOrder104Block11_810, degreeZeroOrder104Block12_810, degreeZeroOrder104Block13_810, degreeZeroOrder104Block14_810, degreeZeroOrder104Block15_810, degreeZeroOrder104Block16_810, degreeZeroOrder104Block17_810, degreeZeroOrder104Block18_810, degreeZeroOrder104Block19_810, degreeZeroOrder104Block20_810, degreeZeroOrder104Block21_810, degreeZeroOrder104Block22_810, degreeZeroOrder104Block23_810, degreeZeroOrder104Block24_810, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, map_zero]


set_option maxHeartbeats 800000000 in
theorem map_degreeZeroOrder105810
    (phi : R →+* S) (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (degreeZeroOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      degreeZeroOrder105810 (phi t0) (phi v1) (phi u1) (phi a4) (phi a3)
        (phi a2) (phi a1) (phi a0) (phi s1) (phi w1) (phi b62) (phi b5)
        (phi b4) (phi b3) (phi b2) (phi b1) (phi lambda) := by
  simp only [degreeZeroOrder105810, degreeZeroOrder105Block0_810, degreeZeroOrder105Block1_810, degreeZeroOrder105Block2_810, degreeZeroOrder105Block3_810, degreeZeroOrder105Block4_810, degreeZeroOrder105Block5_810, degreeZeroOrder105Block6_810, degreeZeroOrder105Block7_810, degreeZeroOrder105Block8_810, degreeZeroOrder105Block9_810, degreeZeroOrder105Block10_810, degreeZeroOrder105Block11_810, degreeZeroOrder105Block12_810, degreeZeroOrder105Block13_810, degreeZeroOrder105Block14_810, degreeZeroOrder105Block15_810, degreeZeroOrder105Block16_810, degreeZeroOrder105Block17_810, degreeZeroOrder105Block18_810, degreeZeroOrder105Block19_810, degreeZeroOrder105Block20_810, degreeZeroOrder105Block21_810, degreeZeroOrder105Block22_810, degreeZeroOrder105Block23_810, degreeZeroOrder105Block24_810, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, map_zero]


set_option maxHeartbeats 800000000 in
theorem map_degreeZeroOrder106810
    (phi : R →+* S) (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (degreeZeroOrder106810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      degreeZeroOrder106810 (phi t0) (phi v1) (phi u1) (phi a4) (phi a3)
        (phi a2) (phi a1) (phi a0) (phi s1) (phi w1) (phi b62) (phi b5)
        (phi b4) (phi b3) (phi b2) (phi b1) (phi lambda) := by
  simp only [degreeZeroOrder106810, degreeZeroOrder106Block0_810, degreeZeroOrder106Block1_810, degreeZeroOrder106Block2_810, degreeZeroOrder106Block3_810, degreeZeroOrder106Block4_810, degreeZeroOrder106Block5_810, degreeZeroOrder106Block6_810, degreeZeroOrder106Block7_810, degreeZeroOrder106Block8_810, degreeZeroOrder106Block9_810, degreeZeroOrder106Block10_810, degreeZeroOrder106Block11_810, degreeZeroOrder106Block12_810, degreeZeroOrder106Block13_810, degreeZeroOrder106Block14_810, degreeZeroOrder106Block15_810, degreeZeroOrder106Block16_810, degreeZeroOrder106Block17_810, degreeZeroOrder106Block18_810, degreeZeroOrder106Block19_810, degreeZeroOrder106Block20_810, degreeZeroOrder106Block21_810, degreeZeroOrder106Block22_810, degreeZeroOrder106Block23_810, degreeZeroOrder106Block24_810, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, map_zero]


set_option maxHeartbeats 800000000 in
theorem map_degreeZeroOrder107810
    (phi : R →+* S) (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (degreeZeroOrder107810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      degreeZeroOrder107810 (phi t0) (phi v1) (phi u1) (phi a4) (phi a3)
        (phi a2) (phi a1) (phi a0) (phi s1) (phi w1) (phi b62) (phi b5)
        (phi b4) (phi b3) (phi b2) (phi b1) (phi lambda) := by
  simp only [degreeZeroOrder107810, degreeZeroOrder107Block0_810, degreeZeroOrder107Block1_810, degreeZeroOrder107Block2_810, degreeZeroOrder107Block3_810, degreeZeroOrder107Block4_810, degreeZeroOrder107Block5_810, degreeZeroOrder107Block6_810, degreeZeroOrder107Block7_810, degreeZeroOrder107Block8_810, degreeZeroOrder107Block9_810, degreeZeroOrder107Block10_810, degreeZeroOrder107Block11_810, degreeZeroOrder107Block12_810, degreeZeroOrder107Block13_810, degreeZeroOrder107Block14_810, degreeZeroOrder107Block15_810, degreeZeroOrder107Block16_810, degreeZeroOrder107Block17_810, degreeZeroOrder107Block18_810, degreeZeroOrder107Block19_810, degreeZeroOrder107Block20_810, degreeZeroOrder107Block21_810, degreeZeroOrder107Block22_810, degreeZeroOrder107Block23_810, degreeZeroOrder107Block24_810, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, map_zero]


set_option maxHeartbeats 800000000 in
theorem map_degreeZeroOrder108810
    (phi : R →+* S) (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (degreeZeroOrder108810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      degreeZeroOrder108810 (phi t0) (phi v1) (phi u1) (phi a4) (phi a3)
        (phi a2) (phi a1) (phi a0) (phi s1) (phi w1) (phi b62) (phi b5)
        (phi b4) (phi b3) (phi b2) (phi b1) (phi lambda) := by
  simp only [degreeZeroOrder108810, degreeZeroOrder108Block0_810, degreeZeroOrder108Block1_810, degreeZeroOrder108Block2_810, degreeZeroOrder108Block3_810, degreeZeroOrder108Block4_810, degreeZeroOrder108Block5_810, degreeZeroOrder108Block6_810, degreeZeroOrder108Block7_810, degreeZeroOrder108Block8_810, degreeZeroOrder108Block9_810, degreeZeroOrder108Block10_810, degreeZeroOrder108Block11_810, degreeZeroOrder108Block12_810, degreeZeroOrder108Block13_810, degreeZeroOrder108Block14_810, degreeZeroOrder108Block15_810, degreeZeroOrder108Block16_810, degreeZeroOrder108Block17_810, degreeZeroOrder108Block18_810, degreeZeroOrder108Block19_810, degreeZeroOrder108Block20_810, degreeZeroOrder108Block21_810, degreeZeroOrder108Block22_810, degreeZeroOrder108Block23_810, degreeZeroOrder108Block24_810, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, map_zero]


set_option maxHeartbeats 800000000 in
theorem map_degreeZeroOrder109810
    (phi : R →+* S) (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (degreeZeroOrder109810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      degreeZeroOrder109810 (phi t0) (phi v1) (phi u1) (phi a4) (phi a3)
        (phi a2) (phi a1) (phi a0) (phi s1) (phi w1) (phi b62) (phi b5)
        (phi b4) (phi b3) (phi b2) (phi b1) (phi lambda) := by
  simp only [degreeZeroOrder109810, degreeZeroOrder109Block0_810, degreeZeroOrder109Block1_810, degreeZeroOrder109Block2_810, degreeZeroOrder109Block3_810, degreeZeroOrder109Block4_810, degreeZeroOrder109Block5_810, degreeZeroOrder109Block6_810, degreeZeroOrder109Block7_810, degreeZeroOrder109Block8_810, degreeZeroOrder109Block9_810, degreeZeroOrder109Block10_810, degreeZeroOrder109Block11_810, degreeZeroOrder109Block12_810, degreeZeroOrder109Block13_810, degreeZeroOrder109Block14_810, degreeZeroOrder109Block15_810, degreeZeroOrder109Block16_810, degreeZeroOrder109Block17_810, degreeZeroOrder109Block18_810, degreeZeroOrder109Block19_810, degreeZeroOrder109Block20_810, degreeZeroOrder109Block21_810, degreeZeroOrder109Block22_810, degreeZeroOrder109Block23_810, degreeZeroOrder109Block24_810, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, map_zero]


set_option maxHeartbeats 800000000 in
theorem map_degreeZeroOrder110810
    (phi : R →+* S) (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (degreeZeroOrder110810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 lambda) =
      degreeZeroOrder110810 (phi t0) (phi v1) (phi u1) (phi a4) (phi a3)
        (phi a2) (phi a1) (phi a0) (phi s1) (phi w1) (phi b62) (phi b5)
        (phi b4) (phi b3) (phi b2) (phi b1) (phi lambda) := by
  simp only [degreeZeroOrder110810, degreeZeroOrder110Block0_810, degreeZeroOrder110Block1_810, degreeZeroOrder110Block2_810, degreeZeroOrder110Block3_810, degreeZeroOrder110Block4_810, degreeZeroOrder110Block5_810, degreeZeroOrder110Block6_810, degreeZeroOrder110Block7_810, degreeZeroOrder110Block8_810, degreeZeroOrder110Block9_810, degreeZeroOrder110Block10_810, degreeZeroOrder110Block11_810, degreeZeroOrder110Block12_810, degreeZeroOrder110Block13_810, degreeZeroOrder110Block14_810, degreeZeroOrder110Block15_810, degreeZeroOrder110Block16_810, degreeZeroOrder110Block17_810, degreeZeroOrder110Block18_810, degreeZeroOrder110Block19_810, degreeZeroOrder110Block20_810, degreeZeroOrder110Block21_810, degreeZeroOrder110Block22_810, degreeZeroOrder110Block23_810, degreeZeroOrder110Block24_810, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, map_zero]


set_option maxHeartbeats 800000000 in
theorem map_degreeZeroOrder110Plus810
    (phi : R →+* S) (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda : R) :
    phi (degreeZeroOrder110Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 lambda) =
      degreeZeroOrder110Plus810 (phi h) (phi t0) (phi v1) (phi u1) (phi a4) (phi a3)
        (phi a2) (phi a1) (phi a0) (phi s1) (phi w1) (phi b62) (phi b5)
        (phi b4) (phi b3) (phi b2) (phi b1) (phi lambda) := by
  simp only [degreeZeroOrder110Plus810, degreeZeroOrder110PlusBlock0_810, degreeZeroOrder110PlusBlock1_810, degreeZeroOrder110PlusBlock2_810, degreeZeroOrder110PlusBlock3_810, degreeZeroOrder110PlusBlock4_810, degreeZeroOrder110PlusBlock5_810, degreeZeroOrder110PlusBlock6_810, degreeZeroOrder110PlusBlock7_810, degreeZeroOrder110PlusBlock8_810, degreeZeroOrder110PlusBlock9_810, degreeZeroOrder110PlusBlock10_810, degreeZeroOrder110PlusBlock11_810, degreeZeroOrder110PlusBlock12_810, degreeZeroOrder110PlusBlock13_810, degreeZeroOrder110PlusBlock14_810, degreeZeroOrder110PlusBlock15_810, degreeZeroOrder110PlusBlock16_810, degreeZeroOrder110PlusBlock17_810, degreeZeroOrder110PlusBlock18_810, degreeZeroOrder110PlusBlock19_810, degreeZeroOrder110PlusBlock20_810, degreeZeroOrder110PlusBlock21_810, degreeZeroOrder110PlusBlock22_810, degreeZeroOrder110PlusBlock23_810, degreeZeroOrder110PlusBlock24_810, map_add, map_sub, map_mul,
    map_pow, map_neg, map_ofNat, map_zero]

end DegreeZeroTowerMap810

section DegreeZeroTowerEval810

variable {k : Type*} [CommRing k]


theorem degreeZeroOrder103810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (degreeZeroOrder103810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      degreeZeroOrder103810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_degreeZeroOrder103810 (Polynomial.evalRingHom a)
      t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)


theorem degreeZeroOrder104810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (degreeZeroOrder104810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      degreeZeroOrder104810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_degreeZeroOrder104810 (Polynomial.evalRingHom a)
      t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)


theorem degreeZeroOrder105810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (degreeZeroOrder105810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      degreeZeroOrder105810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_degreeZeroOrder105810 (Polynomial.evalRingHom a)
      t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)


theorem degreeZeroOrder106810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (degreeZeroOrder106810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      degreeZeroOrder106810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_degreeZeroOrder106810 (Polynomial.evalRingHom a)
      t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)


theorem degreeZeroOrder107810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (degreeZeroOrder107810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      degreeZeroOrder107810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_degreeZeroOrder107810 (Polynomial.evalRingHom a)
      t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)


theorem degreeZeroOrder108810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (degreeZeroOrder108810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      degreeZeroOrder108810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_degreeZeroOrder108810 (Polynomial.evalRingHom a)
      t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)


theorem degreeZeroOrder109810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (degreeZeroOrder109810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      degreeZeroOrder109810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_degreeZeroOrder109810 (Polynomial.evalRingHom a)
      t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)


theorem degreeZeroOrder110810_eval
    (t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (degreeZeroOrder110810 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      degreeZeroOrder110810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_degreeZeroOrder110810 (Polynomial.evalRingHom a)
      t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)


theorem degreeZeroOrder110Plus810_eval
    (h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 : k[X])
    (lambda a : k) :
    (degreeZeroOrder110Plus810 h t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a =
      degreeZeroOrder110Plus810 (h.eval a) (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda := by
  simpa [Polynomial.eval_C] using
    map_degreeZeroOrder110Plus810 (Polynomial.evalRingHom a) h
      t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62
        b5 b4 b3 b2 b1 (Polynomial.C lambda)

#print axioms degreeZeroOrder103810_eval
#print axioms degreeZeroOrder110Plus810_eval

end DegreeZeroTowerEval810

/-! ## Pole obstruction and `h₀`-divisibility

Each named coefficient is the `h^{k-102}` term of
`degreeZeroSourceJetQuotient810`.  If the remaining numerator after
cancelling `h₀^{k-102}` evaluates to that named coefficient, the
remaining-pole obstruction forces it to vanish.  The parent order-`102`
head is the `m = 0` case.  The four scalar load solves are not inserted.
The clearing identity itself remains a hypothesis.
-/

section DegreeZeroTowerHeads810

variable {k : Type*} [Field k] [CharZero k]


/-- Named `h^1` coefficient of the order-`102` quotient, forced if
it is the remaining pole-`16` head after cancelling `h₀^1`. -/
theorem degreeZeroOrder103810_zero_of_remaining_pole
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
        h0 ^ 1 * Q)
    (hhead : Q.eval a = degreeZeroOrder103810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) :
    degreeZeroOrder103810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^ (1 + 16) *
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
    have hpow : degreeZeroEffectiveTowerLength810 = 1 + 16 := rfl
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
    j a (degreeZeroOrder103810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) 1 16 (by decide) hh0
    hdegree hroot hfact hhead hclear_mn hderiv

#print axioms degreeZeroOrder103810_zero_of_remaining_pole

/-- Named `h^2` coefficient of the order-`102` quotient, forced if
it is the remaining pole-`15` head after cancelling `h₀^2`. -/
theorem degreeZeroOrder104810_zero_of_remaining_pole
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
        h0 ^ 2 * Q)
    (hhead : Q.eval a = degreeZeroOrder104810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) :
    degreeZeroOrder104810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^ (2 + 15) *
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
    have hpow : degreeZeroEffectiveTowerLength810 = 2 + 15 := rfl
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
    j a (degreeZeroOrder104810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) 2 15 (by decide) hh0
    hdegree hroot hfact hhead hclear_mn hderiv

#print axioms degreeZeroOrder104810_zero_of_remaining_pole

/-- Named `h^3` coefficient of the order-`102` quotient, forced if
it is the remaining pole-`14` head after cancelling `h₀^3`. -/
theorem degreeZeroOrder105810_zero_of_remaining_pole
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
        h0 ^ 3 * Q)
    (hhead : Q.eval a = degreeZeroOrder105810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) :
    degreeZeroOrder105810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^ (3 + 14) *
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
    have hpow : degreeZeroEffectiveTowerLength810 = 3 + 14 := rfl
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
    j a (degreeZeroOrder105810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) 3 14 (by decide) hh0
    hdegree hroot hfact hhead hclear_mn hderiv

#print axioms degreeZeroOrder105810_zero_of_remaining_pole

/-- Named `h^4` coefficient of the order-`102` quotient, forced if
it is the remaining pole-`13` head after cancelling `h₀^4`. -/
theorem degreeZeroOrder106810_zero_of_remaining_pole
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
        h0 ^ 4 * Q)
    (hhead : Q.eval a = degreeZeroOrder106810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) :
    degreeZeroOrder106810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^ (4 + 13) *
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
    have hpow : degreeZeroEffectiveTowerLength810 = 4 + 13 := rfl
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
    j a (degreeZeroOrder106810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) 4 13 (by decide) hh0
    hdegree hroot hfact hhead hclear_mn hderiv

#print axioms degreeZeroOrder106810_zero_of_remaining_pole

/-- Named `h^5` coefficient of the order-`102` quotient, forced if
it is the remaining pole-`12` head after cancelling `h₀^5`. -/
theorem degreeZeroOrder107810_zero_of_remaining_pole
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
        h0 ^ 5 * Q)
    (hhead : Q.eval a = degreeZeroOrder107810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) :
    degreeZeroOrder107810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^ (5 + 12) *
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
    have hpow : degreeZeroEffectiveTowerLength810 = 5 + 12 := rfl
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
    j a (degreeZeroOrder107810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) 5 12 (by decide) hh0
    hdegree hroot hfact hhead hclear_mn hderiv

#print axioms degreeZeroOrder107810_zero_of_remaining_pole

/-- Named `h^6` coefficient of the order-`102` quotient, forced if
it is the remaining pole-`11` head after cancelling `h₀^6`. -/
theorem degreeZeroOrder108810_zero_of_remaining_pole
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
        h0 ^ 6 * Q)
    (hhead : Q.eval a = degreeZeroOrder108810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) :
    degreeZeroOrder108810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^ (6 + 11) *
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
    have hpow : degreeZeroEffectiveTowerLength810 = 6 + 11 := rfl
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
    j a (degreeZeroOrder108810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) 6 11 (by decide) hh0
    hdegree hroot hfact hhead hclear_mn hderiv

#print axioms degreeZeroOrder108810_zero_of_remaining_pole

/-- Named `h^7` coefficient of the order-`102` quotient, forced if
it is the remaining pole-`10` head after cancelling `h₀^7`. -/
theorem degreeZeroOrder109810_zero_of_remaining_pole
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
        h0 ^ 7 * Q)
    (hhead : Q.eval a = degreeZeroOrder109810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) :
    degreeZeroOrder109810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^ (7 + 10) *
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
    have hpow : degreeZeroEffectiveTowerLength810 = 7 + 10 := rfl
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
    j a (degreeZeroOrder109810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) 7 10 (by decide) hh0
    hdegree hroot hfact hhead hclear_mn hderiv

#print axioms degreeZeroOrder109810_zero_of_remaining_pole

/-- Named `h^8` coefficient of the order-`102` quotient, forced if
it is the remaining pole-`9` head after cancelling `h₀^8`. -/
theorem degreeZeroOrder110810_zero_of_remaining_pole
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
        h0 ^ 8 * Q)
    (hhead : Q.eval a = degreeZeroOrder110810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) :
    degreeZeroOrder110810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda = 0 := by
  have hclear_mn :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^ (8 + 9) *
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
    have hpow : degreeZeroEffectiveTowerLength810 = 8 + 9 := rfl
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
    j a (degreeZeroOrder110810 (t0.eval a) (v1.eval a) (u1.eval a)
        (a4.eval a) (a3.eval a) (a2.eval a) (a1.eval a) (a0.eval a)
        (s1.eval a) (w1.eval a) (b62.eval a) (b5.eval a) (b4.eval a)
        (b3.eval a) (b2.eval a) (b1.eval a) lambda) 8 9 (by decide) hh0
    hdegree hroot hfact hhead hclear_mn hderiv

#print axioms degreeZeroOrder110810_zero_of_remaining_pole

/-- The order-`102` quotient vanishes at the linear root once the
parent remaining-pole-`17` obstruction applies. -/
theorem degreeZeroSourceJetQuotient810_eval_zero_of_deriv_eq_simplePole
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
    (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a = 0 := by
  rw [degreeZeroSourceJetQuotient810_eval_root h0 t0 v1 u1 a4 a3 a2 a1
    a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda a hroot]
  exact degreeZeroSourceJetHead810_zero_of_deriv_eq_simplePole h0 t0 v1
    u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda j a hh0 hdegree
    hroot hclear hderiv

#print axioms degreeZeroSourceJetQuotient810_eval_zero_of_deriv_eq_simplePole

set_option maxHeartbeats 1600000000 in
/-- Remaining-numerator peels of orders `103` through `110`.  After
order `110` the remaining pole is `9`.  This is not a closure. -/
theorem degreeZero_orders103to110_remaining_dvd810
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
    ∃ Q103 Q104 Q105 Q106 Q107 Q108 Q109 Q110 : k[X],
      degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) =
        h0 * Q103 ∧ Q103.eval a = 0 ∧
      Q103 = h0 * Q104 ∧ Q104.eval a = 0 ∧
      Q104 = h0 * Q105 ∧ Q105.eval a = 0 ∧
      Q105 = h0 * Q106 ∧ Q106.eval a = 0 ∧
      Q106 = h0 * Q107 ∧ Q107.eval a = 0 ∧
      Q107 = h0 * Q108 ∧ Q108.eval a = 0 ∧
      Q108 = h0 * Q109 ∧ Q109.eval a = 0 ∧
      Q109 = h0 * Q110 ∧ Q110.eval a = 0 ∧
      h0 ∣ Q110 := by
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
  have hclear17' :
      algebraMap k[X] (RatFunc k)
          (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)) =
        (algebraMap k[X] (RatFunc k) h0) ^ (16 + 1) * rho :=
    hclear17
  have hderiv' :
      Differential.deriv rho =
        RatFunc.C j / algebraMap k[X] (RatFunc k) h0 :=
    hderiv
  have hQ0 :
      (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda)).eval a = 0 :=
    degreeZeroSourceJetQuotient810_eval_zero_of_deriv_eq_simplePole h0
      t0 v1 u1 a4 a3 a2 a1 a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda j a hh0
      hdegree hroot hclear hderiv
  obtain ⟨Q103, h103f, hclear16, h103z, _hdvd103⟩ :=
    degreeZero_remainingNumerator_succ_dvd810 h0
      (degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
        b62 b5 b4 b3 b2 b1 (Polynomial.C lambda))
      rho j a 16 (by decide) hh0 hdegree hroot hQ0 hclear17' hderiv'
  obtain ⟨Q104, h104f, hclear15, h104z, _hdvd104⟩ :=
    degreeZero_remainingNumerator_succ_dvd810 h0 Q103 rho j a 15
      (by decide) hh0 hdegree hroot h103z hclear16 hderiv'
  obtain ⟨Q105, h105f, hclear14, h105z, _hdvd105⟩ :=
    degreeZero_remainingNumerator_succ_dvd810 h0 Q104 rho j a 14
      (by decide) hh0 hdegree hroot h104z hclear15 hderiv'
  obtain ⟨Q106, h106f, hclear13, h106z, _hdvd106⟩ :=
    degreeZero_remainingNumerator_succ_dvd810 h0 Q105 rho j a 13
      (by decide) hh0 hdegree hroot h105z hclear14 hderiv'
  obtain ⟨Q107, h107f, hclear12, h107z, _hdvd107⟩ :=
    degreeZero_remainingNumerator_succ_dvd810 h0 Q106 rho j a 12
      (by decide) hh0 hdegree hroot h106z hclear13 hderiv'
  obtain ⟨Q108, h108f, hclear11, h108z, _hdvd108⟩ :=
    degreeZero_remainingNumerator_succ_dvd810 h0 Q107 rho j a 11
      (by decide) hh0 hdegree hroot h107z hclear12 hderiv'
  obtain ⟨Q109, h109f, hclear10, h109z, _hdvd109⟩ :=
    degreeZero_remainingNumerator_succ_dvd810 h0 Q108 rho j a 10
      (by decide) hh0 hdegree hroot h108z hclear11 hderiv'
  obtain ⟨Q110, h110f, hclear9, h110z, hdvd110⟩ :=
    degreeZero_remainingNumerator_succ_dvd810 h0 Q109 rho j a 9
      (by decide) hh0 hdegree hroot h109z hclear10 hderiv'
  exact ⟨Q103, Q104, Q105, Q106, Q107, Q108, Q109, Q110, h103f, h103z, h104f, h104z, h105f, h105z, h106f, h106z, h107f, h107z, h108f, h108z, h109f, h109z, h110f, h110z, hdvd110⟩

#print axioms degreeZero_orders103to110_remaining_dvd810

/-- Batch `h₀^8`-divisibility of the order-`102` quotient through order
`110`.  Remaining pole `9`; next unused compact-numerator order `111`. -/
theorem degreeZero_orders103to110_pow_dvd810
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
    h0 ^ degreeZeroTowerBatchDivisibility810 ∣
      degreeZeroSourceJetQuotient810 h0 t0 v1 u1 a4 a3 a2 a1 a0 s1 w1
            b62 b5 b4 b3 b2 b1 (Polynomial.C lambda) := by
  obtain ⟨Q103, Q104, Q105, Q106, Q107, Q108, Q109, Q110, h103f, _h103z, h104f, _h104z, h105f, _h105z,
      h106f, _h106z, h107f, _h107z, h108f, _h108z, h109f, _h109z,
      h110f, _h110z, _hdvd110⟩ :=
    degreeZero_orders103to110_remaining_dvd810 h0 t0 v1 u1 a4 a3 a2 a1
      a0 s1 w1 b62 b5 b4 b3 b2 b1 lambda j a hh0 hdegree hroot hclear
      hderiv
  refine ⟨Q110, ?_⟩
  simp only [degreeZeroTowerBatchDivisibility810, h103f, h104f, h105f,
    h106f, h107f, h108f, h109f, h110f]
  ring

#print axioms degreeZero_orders103to110_pow_dvd810

end DegreeZeroTowerHeads810

end Max11DegreeRoutes
