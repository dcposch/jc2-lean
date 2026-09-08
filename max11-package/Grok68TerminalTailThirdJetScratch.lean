import Grok68TerminalTailFalseScratch

/-! # Third-jet I4/I3 on the `(6,8)` terminal-tail residual

Untracked working note. No tracked file was edited.

Parent residual `FiveToSixTerminalTailOpenResidual68`: an aligned
beyond-wall cusp at `7n-2g+60k`, or the original at-wall large terminal
all-nonzero cusp.  Groebner of the leading cusp together with the I4/I3
faces is nonempty (the kernel `b e + c d = 0` on `a b^2 + 3 c^2 = 0`),
matching the parent report.  CAS `derive_68_terminal_tail_third_jet.py`
consumes the third-jet pair at `9n-2g-s-120` / `10n-2g-s-120`: the
`(d₃, e₃)` block is the same singular face matrix, so the third jet is a
compatibility on lower jets, not an `e^4` certificate.  A nonzero sample
on the kernel with free second jets survives.  Closed neighbours died
from extra row-two/row-one tops `J` and `Y` that do not meet the I4 face
in this chamber.

The missing `120 < n` source `d = 0` descent with nonconstant `B` is
`False`.  I4 forces `e = B^2/9 - (3/4) epsilon` and `i4 = 0`; I3 then
forces `c = -(3/8) gamma` (constant).  The resulting row zero is
`(-4/243) A A' B^3` plus strictly lower `gamma` terms, which cannot be a
nonzero constant once `deg A ≥ 2` and `deg B ≥ 1`.  Together with the
parent `B = 0` and constant-`B` children this kills source `d = 0` for
every `B`.  On a `60`-aligned large packet the beyond-wall iterator's
zero child therefore collapses to source `d = 0` and is empty: the
terminal-zero packet is exactly an honest beyond-wall cusp.

Exact gain: third-jet I4/I3 convolutions (including the `B^3` /
`B^2 c` extras when they attain); third-jet compatibility scalar;
source `d = 0` for nonconstant `B`; source `d = 0` for every `B`;
aligned large terminal-zero packet reduces to a beyond-wall cusp.
Next unused row: fourth-jet I4/I3 pair at `9n-2g-s-180` /
`10n-2g-s-180`, or the row-two coefficient at `max(11n-3g, 2g-3n)-1`
(monomial jets are nonzero there; lower `d,e` jets at offset `≥ 180`
are not constrained by the third jet).
Residual: `FiveToSixTerminalTailOpenResidual68` (both cusps remain;
the source `d = 0` child is closed).
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section FiveToSixTerminalTailThirdJet68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Source `d = 0`, nonconstant `B`: I4 forces `e` -/

/-- I4 with residual `d = 0` is `(8/3) B` times the discrepancy of `e`
from `B^2/9 - (3/4) epsilon`. -/
theorem fiveToSix_I4_dZero_e_remainder68 (gamma epsilon : k)
    (A B c e : k[X]) :
    cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B)) e =
      (8 / 3 : k) •
        (B * (e - (1 / 9 : k) • B ^ 2 +
          C ((3 / 4 : k) * epsilon))) := by
  have hform := fiveToSix_I4_of_d_zero68 gamma epsilon A B c e
  rw [hform]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
    map_neg, map_zero, RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

/-- A non-constant `B` and a constant I4 force
`e = B^2/9 - (3/4) epsilon`. -/
theorem fiveToSix_dZero_B_nonconstant_forces_e68
    (gamma epsilon i4 : k) (A B c e : k[X])
    (hB : 1 ≤ B.natDegree)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B)) e = C i4) :
    e = (1 / 9 : k) • B ^ 2 - C ((3 / 4 : k) * epsilon) := by
  have hform := fiveToSix_I4_dZero_e_remainder68 gamma epsilon A B c e
  rw [hform] at hi4
  set rem : k[X] :=
    e - (1 / 9 : k) • B ^ 2 + C ((3 / 4 : k) * epsilon)
  have hprod : (8 / 3 : k) • (B * rem) = C i4 := by
    simpa [rem] using hi4
  have hBne : B ≠ 0 := fun hB0 => by
    have : B.natDegree = 0 := by simp [hB0]
    omega
  have hrem0 : rem = 0 := by
    by_contra hrem
    have hdeg : (B * rem).natDegree = B.natDegree + rem.natDegree :=
      natDegree_mul hBne hrem
    have hsc : ((8 / 3 : k) • (B * rem)).natDegree = (B * rem).natDegree := by
      rw [smul_eq_C_mul, natDegree_C_mul (by norm_num : (8 / 3 : k) ≠ 0)]
    rw [hprod, natDegree_C] at hsc
    omega
  have : e - (1 / 9 : k) • B ^ 2 + C ((3 / 4 : k) * epsilon) = 0 := hrem0
  linear_combination this

/-! ## I3 forces constant `c = -(3/8) gamma` -/

/-- I3 on the I4-forced `e`, with residual `d = 0`. -/
theorem fiveToSix_I3_dZero_forced_e68 (gamma epsilon : k)
    (A B c : k[X]) :
    cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B))
        ((1 / 9 : k) • B ^ 2 - C ((3 / 4 : k) * epsilon)) =
      (-16 / 27 : k) •
        ((c + C ((3 / 8 : k) * gamma)) * B ^ 2) -
        C ((3 : k) * gamma * epsilon) := by
  have hD : (1 / 3 : k) • (A * B) = (1 / 3 : k) • (A * B) + (0 : k[X]) :=
    (add_zero _).symm
  rw [hD, cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates]
  simp only [zero_smul, add_zero]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [secondaryResidualInvariantThreePolynomial68,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_neg,
    map_zero, RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

/-- A non-constant `B` and a constant I3 force `c = -(3/8) gamma`. -/
theorem fiveToSix_dZero_B_nonconstant_forces_c68
    (gamma epsilon i3 : k) (A B c : k[X])
    (hB : 1 ≤ B.natDegree)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B))
      ((1 / 9 : k) • B ^ 2 - C ((3 / 4 : k) * epsilon)) = C i3) :
    c = C (-(3 / 8 : k) * gamma) := by
  have hform := fiveToSix_I3_dZero_forced_e68 gamma epsilon A B c
  rw [hform] at hi3
  set q : k[X] := c + C ((3 / 8 : k) * gamma)
  have hprod : (-16 / 27 : k) • (q * B ^ 2) -
      C ((3 : k) * gamma * epsilon) = C i3 := by
    simpa [q] using hi3
  have hq0 : q = 0 := by
    have hconst : (-16 / 27 : k) • (q * B ^ 2) =
        C (i3 + (3 : k) * gamma * epsilon) := by
      have h := hprod
      rw [sub_eq_iff_eq_add] at h
      rw [h, ← map_add]
    by_contra hq
    have hBne : B ≠ 0 := fun hB0 => by
      have : B.natDegree = 0 := by simp [hB0]
      omega
    have hB2 : B ^ 2 ≠ 0 := pow_ne_zero 2 hBne
    have hdeg : (q * B ^ 2).natDegree =
        q.natDegree + (B ^ 2).natDegree := natDegree_mul hq hB2
    have hB2deg : (B ^ 2).natDegree = 2 * B.natDegree := by
      rw [pow_two, natDegree_mul hBne hBne]
      ring
    have hsc : ((-16 / 27 : k) • (q * B ^ 2)).natDegree =
        (q * B ^ 2).natDegree := by
      rw [smul_eq_C_mul,
        natDegree_C_mul (by norm_num : (-16 / 27 : k) ≠ 0)]
    have hC : (C (i3 + (3 : k) * gamma * epsilon)).natDegree = 0 :=
      natDegree_C _
    rw [hconst, hC] at hsc
    omega
  have : c + C ((3 / 8 : k) * gamma) = 0 := hq0
  have hcneg : c = -C ((3 / 8 : k) * gamma) :=
    eq_neg_of_add_eq_zero_left this
  have hneg : -C ((3 / 8 : k) * gamma) =
      C (-(3 / 8 : k) * gamma) := by
    simp
  rw [hcneg, hneg]

/-! ## Row zero on the forced `(e, c)` locus -/

set_option maxHeartbeats 40000000 in
/-- Homogeneous residual row zero on the forced locus. -/
theorem fiveToSix_dZero_forced_residual_rowZero68
    (gamma epsilon : k) (A B : k[X]) :
    let c := C (-(3 / 8 : k) * gamma)
    let e := (1 / 9 : k) • B ^ 2 - C ((3 / 4 : k) * epsilon)
    secondaryResidualRowZeroPolynomial68 A B c 0 e =
      (-4 / 243 : k) • (A * derivative A * B ^ 3) +
        ((1 / 9 : k) * epsilon) • (A * derivative A * B) +
        ((1 / 48 : k) * gamma ^ 2) • (derivative A * B) -
        ((1 / 27 : k) * gamma) • (B ^ 2 * derivative B) := by
  intro c e
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [c, e, secondaryResidualRowZeroPolynomial68, zero_mul, mul_zero,
    add_zero, zero_add, sub_zero, smul_zero, zero_smul, derivative_add,
    derivative_sub, derivative_mul, derivative_pow, derivative_smul,
    derivative_C, one_mul, Polynomial.smul_eq_C_mul, map_add, map_sub,
    map_mul, map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  ring

set_option maxHeartbeats 40000000 in
/-- Load row zero on the forced locus; `alpha` and `eta` cancel. -/
theorem fiveToSix_dZero_forced_load_rowZero68
    (alpha gamma epsilon eta : k) (A B : k[X]) :
    let c := C (-(3 / 8 : k) * gamma)
    let e := (1 / 9 : k) • B ^ 2 - C ((3 / 4 : k) * epsilon)
    cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B)) e =
      ((2 / 9 : k) * gamma) • (derivative A * B * c) +
        ((4 / 27 : k) * gamma) • (B ^ 2 * derivative B) -
        ((1 / 9 : k) * epsilon) • (A * derivative A * B) := by
  intro c e
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [c, e, cubicLoadRowZeroPolynomial68, cubicLoadUPolynomial68,
    cubicLoadVPolynomial68, zero_mul, mul_zero, add_zero, zero_add, sub_zero,
    smul_zero, zero_smul, derivative_add, derivative_sub, derivative_mul,
    derivative_pow, derivative_smul, derivative_C, one_mul,
    Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow, map_neg,
    map_zero, RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast,
    map_one]
  ring

set_option maxHeartbeats 20000000 in
/-- Combined row zero on the forced locus. -/
theorem fiveToSix_dZero_forced_rowZero68
    (alpha gamma epsilon eta : k) (A B : k[X]) :
    let c := C (-(3 / 8 : k) * gamma)
    let e := (1 / 9 : k) • B ^ 2 - C ((3 / 4 : k) * epsilon)
    secondaryResidualRowZeroPolynomial68 A B c 0 e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B)) e =
      (-4 / 243 : k) • (A * derivative A * B ^ 3) -
        ((1 / 16 : k) * gamma ^ 2) • (derivative A * B) +
        ((1 / 9 : k) * gamma) • (B ^ 2 * derivative B) := by
  intro c e
  have hr := fiveToSix_dZero_forced_residual_rowZero68 gamma epsilon A B
  have hl := fiveToSix_dZero_forced_load_rowZero68 alpha gamma epsilon eta A B
  rw [hr, hl]
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul, map_pow,
    map_neg, map_zero, RatFunc.algebraMap_C, map_div₀, map_ofNat, map_one]
  ring

/-- Coefficient of `A A' B^3` at its top index. -/
theorem coeff_A_derivativeA_B3_top68 (A B : k[X])
    (hA : 1 ≤ A.natDegree) (hB : 1 ≤ B.natDegree) :
    (A * derivative A * B ^ 3).coeff
        (2 * A.natDegree + 3 * B.natDegree - 1) =
      (A.natDegree : k) * A.coeff A.natDegree ^ 2 *
        B.coeff B.natDegree ^ 3 := by
  have hAne : A ≠ 0 := fun hA0 => by
    have : A.natDegree = 0 := by simp [hA0]
    omega
  have hBne : B ≠ 0 := fun hB0 => by
    have : B.natDegree = 0 := by simp [hB0]
    omega
  have hder : (derivative A).coeff (A.natDegree - 1) =
      (A.natDegree : k) * A.coeff A.natDegree := by
    rw [coeff_derivative]
    have hidx : A.natDegree - 1 + 1 = A.natDegree := by omega
    rw [hidx]
    have hcast : (A.natDegree - 1 : ℕ) + (1 : k) = (A.natDegree : k) :=
      (by exact_mod_cast hidx)
    rw [hcast]
    ring
  have hder_le : (derivative A).natDegree ≤ A.natDegree - 1 :=
    natDegree_derivative_le A
  have hB3 : (B ^ 3).natDegree = 3 * B.natDegree := by
    rw [natDegree_pow (p := B) (n := 3)]
  have hB3c : (B ^ 3).coeff (3 * B.natDegree) = B.coeff B.natDegree ^ 3 := by
    rw [← hB3, coeff_natDegree, leadingCoeff_pow, coeff_natDegree]
  have hsum : A.natDegree + (A.natDegree - 1) + 3 * B.natDegree =
      2 * A.natDegree + 3 * B.natDegree - 1 := by omega
  have h := coeff_mul_mul_at_bounds68 A (derivative A) (B ^ 3)
    A.natDegree (A.natDegree - 1) (3 * B.natDegree) le_rfl hder_le
    hB3.le
  rw [hsum] at h
  rw [h, hder, hB3c]
  ring

/-- The two `gamma` companions sit strictly below `A A' B^3`. -/
theorem fiveToSix_dZero_forced_rowZero_gamma_below68
    (gamma : k) (A B : k[X])
    (hA : 2 ≤ A.natDegree) (hB : 1 ≤ B.natDegree) :
    (((1 / 16 : k) * gamma ^ 2) • (derivative A * B)).natDegree <
        2 * A.natDegree + 3 * B.natDegree - 1 ∧
      (((1 / 9 : k) * gamma) • (B ^ 2 * derivative B)).natDegree <
        2 * A.natDegree + 3 * B.natDegree - 1 := by
  constructor
  · have h1 : (derivative A * B).natDegree ≤
        (A.natDegree - 1) + B.natDegree :=
      (natDegree_mul_le).trans
        (Nat.add_le_add (natDegree_derivative_le A) le_rfl)
    have h2 : (((1 / 16 : k) * gamma ^ 2) •
        (derivative A * B)).natDegree ≤
        (A.natDegree - 1) + B.natDegree :=
      (natDegree_smul_le _ _).trans h1
    omega
  · have hderB : (derivative B).natDegree ≤ B.natDegree - 1 :=
      natDegree_derivative_le B
    have h1 : (B ^ 2 * derivative B).natDegree ≤
        2 * B.natDegree + (B.natDegree - 1) := by
      have hB2 : (B ^ 2).natDegree ≤ 2 * B.natDegree := by
        have h := (natDegree_mul_le : (B * B).natDegree ≤
          B.natDegree + B.natDegree)
        simpa [pow_two, two_mul] using h
      exact (natDegree_mul_le).trans (Nat.add_le_add hB2 hderB)
    have h2 : (((1 / 9 : k) * gamma) •
        (B ^ 2 * derivative B)).natDegree ≤
        2 * B.natDegree + (B.natDegree - 1) :=
      (natDegree_smul_le _ _).trans h1
    omega

/-- Row zero on the forced locus cannot be a nonzero constant. -/
theorem fiveToSix_dZero_forced_rowZero_impossible68
    (alpha gamma epsilon eta terminal : k) (A B : k[X])
    (hterminal : terminal ≠ 0)
    (hA : 2 ≤ A.natDegree) (hB : 1 ≤ B.natDegree)
    (hrow0 : secondaryResidualRowZeroPolynomial68 A B
        (C (-(3 / 8 : k) * gamma)) 0
        ((1 / 9 : k) • B ^ 2 - C ((3 / 4 : k) * epsilon)) +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B (C (-(3 / 8 : k) * gamma)) ((1 / 3 : k) • (A * B))
        ((1 / 9 : k) • B ^ 2 - C ((3 / 4 : k) * epsilon)) =
      C terminal) : False := by
  have hform := fiveToSix_dZero_forced_rowZero68 alpha gamma epsilon eta A B
  rw [hform] at hrow0
  have hAne : A ≠ 0 := fun hA0 => by
    have : A.natDegree = 0 := by simp [hA0]
    omega
  have hBne : B ≠ 0 := fun hB0 => by
    have : B.natDegree = 0 := by simp [hB0]
    omega
  have htop := coeff_A_derivativeA_B3_top68 A B (by omega) hB
  have hnA : (A.natDegree : k) ≠ 0 := by
    exact_mod_cast (by omega : A.natDegree ≠ 0)
  have ha : A.coeff A.natDegree ≠ 0 := by
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hAne
  have hb : B.coeff B.natDegree ≠ 0 := by
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hBne
  have hcore_coeff :
      ((-4 / 243 : k) • (A * derivative A * B ^ 3)).coeff
          (2 * A.natDegree + 3 * B.natDegree - 1) ≠ 0 := by
    rw [coeff_smul, smul_eq_mul, htop]
    exact mul_ne_zero (by norm_num : (-4 / 243 : k) ≠ 0)
      (mul_ne_zero (mul_ne_zero hnA (pow_ne_zero 2 ha)) (pow_ne_zero 3 hb))
  have hidx : 1 ≤ 2 * A.natDegree + 3 * B.natDegree - 1 := by omega
  have hgamma :=
    fiveToSix_dZero_forced_rowZero_gamma_below68 gamma A B hA hB
  have hcore_deg :
      ((-4 / 243 : k) • (A * derivative A * B ^ 3)).natDegree =
        2 * A.natDegree + 3 * B.natDegree - 1 :=
    le_antisymm
      (by
        have : (A * derivative A * B ^ 3).natDegree ≤
            2 * A.natDegree + 3 * B.natDegree - 1 := by
          have h1 : (A * derivative A).natDegree ≤
              A.natDegree + (A.natDegree - 1) :=
            (natDegree_mul_le).trans
              (Nat.add_le_add le_rfl (natDegree_derivative_le A))
          have h2 : (B ^ 3).natDegree ≤ 3 * B.natDegree := by
            exact (natDegree_pow (p := B) (n := 3)).le
          have := (natDegree_mul_le
              (p := A * derivative A) (q := B ^ 3)).trans
            (Nat.add_le_add h1 h2)
          have : A.natDegree + (A.natDegree - 1) + 3 * B.natDegree =
              2 * A.natDegree + 3 * B.natDegree - 1 := by omega
          omega
        exact (natDegree_smul_le _ _).trans this)
      (le_natDegree_of_ne_zero hcore_coeff)
  have hsum_deg :
      ((-4 / 243 : k) • (A * derivative A * B ^ 3) -
          ((1 / 16 : k) * gamma ^ 2) • (derivative A * B) +
          ((1 / 9 : k) * gamma) • (B ^ 2 * derivative B)).natDegree =
        2 * A.natDegree + 3 * B.natDegree - 1 := by
    have hlt1 := hgamma.1
    have hlt2 := hgamma.2
    have hleft :
        ((-4 / 243 : k) • (A * derivative A * B ^ 3) -
            ((1 / 16 : k) * gamma ^ 2) • (derivative A * B)).natDegree =
          2 * A.natDegree + 3 * B.natDegree - 1 := by
      rw [← hcore_deg]
      exact natDegree_sub_eq_left_of_natDegree_lt (hcore_deg ▸ hlt1)
    rw [← hleft]
    exact natDegree_add_eq_left_of_natDegree_lt (hleft ▸ hlt2)
  have hC : (C terminal).natDegree = 0 := natDegree_C terminal
  have : (C terminal).natDegree =
      2 * A.natDegree + 3 * B.natDegree - 1 := by
    rw [← hrow0, hsum_deg]
  omega

/-- Source `d = 0` with non-constant `B` is `False` once `deg A ≥ 2`. -/
theorem fiveToSix_dZero_B_nonconstant_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hl : l = 0) (hbeta : beta = 0) (hdelta : delta = 0)
    (hzeta : zeta = 0)
    (hd : secondaryDDefectPolynomial68 A B D = 0)
    (hB : 1 ≤ B.natDegree) (hA : 2 ≤ A.natDegree) : False := by
  have hDrec : D = (1 / 3 : k) • (A * B) := by
    have h := secondaryDDefectPolynomial68_reconstruct A B D
    rw [hd, add_zero] at h
    exact h
  have hCrec : C0 = (1 / 3 : k) • A ^ 2 + cubicCDefectPolynomial68 A C0 :=
    cubicCDefectPolynomial68_reconstruct A C0
  let c := cubicCDefectPolynomial68 A C0
  let e := cubicEDefectPolynomial68 A C0 E
  have hErec : E = (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e := by
    simpa only [c, e] using
      cubicEDefectPolynomial68_eq_cubicCoordinates A C0 E
  obtain ⟨i4, hi4raw⟩ := hsys.firstFour
  have hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B)) e = C i4 := by
    have h := hi4raw
    rw [hl, hbeta, hdelta, hzeta, hCrec] at h
    rw [hErec, firstIntegralFourPolynomial68_cubicCoordinates, hDrec] at h
    simpa [c, e] using h
  have heq : e = (1 / 9 : k) • B ^ 2 - C ((3 / 4 : k) * epsilon) :=
    fiveToSix_dZero_B_nonconstant_forces_e68 gamma epsilon i4 A B c e hB hi4
  obtain ⟨i3, hi3raw⟩ := hsys.firstThree
  have hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B)) e = C i3 := by
    have h := hi3raw
    rw [hl, hbeta, hdelta, hzeta, hCrec] at h
    rw [hErec, firstIntegralThreePolynomial68_cubicCoordinates, hDrec] at h
    simpa [c, e] using h
  rw [heq] at hi3
  have hceq : c = C (-(3 / 8 : k) * gamma) :=
    fiveToSix_dZero_B_nonconstant_forces_c68 gamma epsilon i3 A B c hB hi3
  have hDrec0 : D = (1 / 3 : k) • (A * B) + (0 : k[X]) := by
    rw [add_zero]
    exact hDrec
  have hrow0 := hsys.rowZero
  rw [hCrec, hDrec0, hErec, cubicRowZeroPolynomial68_residualSplit,
    hl, hbeta, hdelta, hzeta] at hrow0
  rw [show cubicCDefectPolynomial68 A C0 = c from rfl] at hrow0
  rw [heq, hceq, add_zero] at hrow0
  exact fiveToSix_dZero_forced_rowZero_impossible68
    alpha gamma epsilon eta terminal A B hterminal hA hB hrow0

/-- Source `d = 0` is empty for every `B`, once `deg A ≥ 2`. -/
theorem fiveToSix_source_dZero_impossible68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hl : l = 0) (hbeta : beta = 0) (hdelta : delta = 0)
    (hzeta : zeta = 0)
    (hd : secondaryDDefectPolynomial68 A B D = 0)
    (hA : 2 ≤ A.natDegree) : False := by
  by_cases hB0 : B = 0
  · have hDrec : D = (1 / 3 : k) • (A * B) := by
      have h := secondaryDDefectPolynomial68_reconstruct A B D
      rw [hd, add_zero] at h
      exact h
    have hD0 : D = 0 := by
      rw [hDrec, hB0, mul_zero, smul_zero]
    have hrow0 := hsys.rowZero
    rw [hl, hbeta, hdelta, hzeta, hB0, hD0] at hrow0
    exact fiveToSix_deZero_B_zero_terminal_impossible68 alpha gamma epsilon
      eta terminal A C0 E hterminal hrow0
  · by_cases hBpos : 1 ≤ B.natDegree
    · exact fiveToSix_dZero_B_nonconstant_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys hl hbeta hdelta hzeta hd hBpos hA
    · have hB : B.natDegree ≤ 0 := by omega
      exact fiveToSix_dZero_B_constant_impossible68
        l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
        hterminal hsys hl hbeta hdelta hzeta hd hB hA

/-! ## Third-jet lattice convolution -/

/-- Two lattice strides below a product of separate degree bounds:
when the left factor is supported on the `60`-lattice and its bound is
aligned, only the three aligned decompositions survive. -/
theorem coeff_mul_offset_oneTwenty_left_lattice68 (p q : k[X]) (u v : ℕ)
    (hu : 120 ≤ u) (hv : 120 ≤ v) (hdvd : 60 ∣ u)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (hsupp : ∀ i : ℕ, ¬ (60 ∣ i) → p.coeff i = 0) :
    (p * q).coeff (u + v - 120) =
      p.coeff (u - 120) * q.coeff v +
        p.coeff (u - 60) * q.coeff (v - 60) +
        p.coeff u * q.coeff (v - 120) := by
  have hmem1 : u - 120 ∈ Finset.range (u + v - 120 + 1) :=
    Finset.mem_range.mpr (by omega)
  have hmem2 : u - 60 ∈ (Finset.range (u + v - 120 + 1)).erase (u - 120) :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
  have hmem3 : u ∈
      ((Finset.range (u + v - 120 + 1)).erase (u - 120)).erase (u - 60) :=
    Finset.mem_erase.mpr ⟨by omega,
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩⟩
  have hzero : ∀ i ∈
      (((Finset.range (u + v - 120 + 1)).erase (u - 120)).erase
        (u - 60)).erase u,
      p.coeff i * q.coeff (u + v - 120 - i) = 0 := by
    intro i hi
    have hi1 := Finset.mem_erase.mp hi
    have hi2 := Finset.mem_erase.mp hi1.2
    have hi3 := Finset.mem_erase.mp hi2.2
    have hi4 := Finset.mem_range.mp hi3.2
    by_cases hgt : u < i
    · rw [coeff_eq_zero_of_natDegree_lt (hp.trans_lt hgt), zero_mul]
    · by_cases hlt : i < u - 120
      · rw [coeff_eq_zero_of_natDegree_lt (hq.trans_lt (by omega)),
          mul_zero]
      · rw [hsupp i (by omega), zero_mul]
  have h4 : (p * q).coeff (u + v - 120) =
      ∑ i ∈ Finset.range (u + v - 120 + 1),
        p.coeff i * q.coeff (u + v - 120 - i) := by
    rw [coeff_mul]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ _
  have h1 := Finset.add_sum_erase (Finset.range (u + v - 120 + 1))
    (fun i => p.coeff i * q.coeff (u + v - 120 - i)) hmem1
  have h2 := Finset.add_sum_erase
    ((Finset.range (u + v - 120 + 1)).erase (u - 120))
    (fun i => p.coeff i * q.coeff (u + v - 120 - i)) hmem2
  have h3 := Finset.add_sum_erase
    (((Finset.range (u + v - 120 + 1)).erase (u - 120)).erase (u - 60))
    (fun i => p.coeff i * q.coeff (u + v - 120 - i)) hmem3
  have h5 : ∑ i ∈
      (((Finset.range (u + v - 120 + 1)).erase (u - 120)).erase
        (u - 60)).erase u,
      p.coeff i * q.coeff (u + v - 120 - i) = 0 :=
    Finset.sum_eq_zero hzero
  rw [h4, ← h1, ← h2, ← h3, h5, add_zero]
  show p.coeff (u - 120) * q.coeff (u + v - 120 - (u - 120)) +
      (p.coeff (u - 60) * q.coeff (u + v - 120 - (u - 60)) +
        p.coeff u * q.coeff (u + v - 120 - u)) =
    p.coeff (u - 120) * q.coeff v +
      p.coeff (u - 60) * q.coeff (v - 60) +
      p.coeff u * q.coeff (v - 120)
  rw [show u + v - 120 - (u - 120) = v from by omega,
    show u + v - 120 - (u - 60) = v - 60 from by omega,
    show u + v - 120 - u = v - 120 from by omega]
  ac_rfl

/-- Phase-safe third jet of `B`. -/
def uniformCuspThirdJetB68 (B : k[X]) (n g : ℕ) : k :=
  if 120 ≤ 3 * n - g then B.coeff (3 * n - g - 120) else 0

theorem uniformCuspThirdJetB68_of_le (B : k[X]) (n g : ℕ)
    (h : 120 ≤ 3 * n - g) :
    uniformCuspThirdJetB68 B n g = B.coeff (3 * n - g - 120) := ite_eq_left h

theorem uniformCuspThirdJetB68_of_lt (B : k[X]) (n g : ℕ)
    (h : 3 * n - g < 120) :
    uniformCuspThirdJetB68 B n g = 0 := ite_eq_right (by omega)

/-- On the aligned large wall, `B^3` lies strictly below the I4 third jet. -/
theorem fiveToSix_B3_lt_I4_thirdJet_wall68 (n g : ℕ)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hn : 120 < n) (hn60 : 60 ∣ n) (hg60 : 60 ∣ g) :
    3 * (3 * n - g) < 2 * n - 120 := by
  obtain ⟨N, hN⟩ := hn60
  obtain ⟨G, hG⟩ := hg60
  subst n
  subst g
  have hN : 2 < N := by omega
  have hwin : 5 * N < 2 * G ∧ 2 * G ≤ 6 * N := by
    constructor <;> omega
  have h2G : 5 * N + 1 ≤ 2 * G := by omega
  have h6G : 15 * N + 3 ≤ 6 * G := by omega
  have hwant : 14 * N + 5 ≤ 6 * G := by omega
  omega

/-- Homogeneous I4 third jet one lattice stride below the second jet,
when `B` itself has room for a third jet.  The cubic `B^3` is kept
literal (it attains on some beyond-wall cells). -/
theorem secondaryResidualInvariantFourPolynomial68_coeff_thirdJet_fiveToSix
    (B c d e : k[X]) (n g s : ℕ)
    (hn120 : 120 ≤ n) (hs : 0 < s)
    (hwindow : 5 * n < 2 * g ∧ 2 * g ≤ 6 * n)
    (hload3 : s + 120 ≤ 7 * n - 2 * g)
    (hdn : 60 ∣ n) (hdg : 60 ∣ g)
    (hB120 : 120 ≤ 3 * n - g)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - g - s)
    (he : e.natDegree ≤ 6 * n - g - s)
    (hBsupp : ∀ i : ℕ, ¬ (60 ∣ i) → B.coeff i = 0)
    (hcsupp : ∀ i : ℕ, ¬ (60 ∣ i) → c.coeff i = 0) :
    (secondaryResidualInvariantFourPolynomial68 B c d e).coeff
        (9 * n - 2 * g - s - 120) =
      (8 / 3 : k) *
        (uniformCuspThirdJetB68 B n g * e.coeff (6 * n - g - s) +
          uniformCuspSecondJetB68 B n g * e.coeff (6 * n - g - s - 60) +
          B.coeff (3 * n - g) * e.coeff (6 * n - g - s - 120) +
          c.coeff (4 * n - g - 120) * d.coeff (5 * n - g - s) +
          c.coeff (4 * n - g - 60) * d.coeff (5 * n - g - s - 60) +
          c.coeff (4 * n - g) * d.coeff (5 * n - g - s - 120)) +
      (-8 / 27 : k) * (B ^ 3).coeff (9 * n - 2 * g - s - 120) := by
  have hBe := coeff_mul_offset_oneTwenty_left_lattice68 B e
    (3 * n - g) (6 * n - g - s) hB120 (by omega) (by omega) hB he hBsupp
  rw [show 3 * n - g + (6 * n - g - s) - 120 =
    9 * n - 2 * g - s - 120 from by omega] at hBe
  have hcd := coeff_mul_offset_oneTwenty_left_lattice68 c d
    (4 * n - g) (5 * n - g - s) (by omega) (by omega) (by omega)
    hc hd hcsupp
  rw [show 4 * n - g + (5 * n - g - s) - 120 =
    9 * n - 2 * g - s - 120 from by omega] at hcd
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, hBe, hcd,
    uniformCuspThirdJetB68_of_le B n g hB120,
    uniformCuspSecondJetB68_of_le B n g (by omega)]
  ring

/-- Cokernel of the singular third-jet system (same left kernel as the
face).  The `(d₃, e₃)` block cancels on the cusp; the remainder is the
compatibility scalar in the second- and third-level jets together with
the literal `B^3` / `d^2` extras. -/
theorem fiveToSix_uniformCusp_thirdJet_compatibility_scalar68
    (a b c ds es b2 c2 a2 b3 c3 a3 d2 e2 d3 e3 qB3 qce : k)
    (hcusp : a * b ^ 2 + 3 * c ^ 2 = 0)
    (hR4 : b * e3 + b2 * e2 + b3 * es +
        c * d3 + c2 * d2 + c3 * ds + qB3 = 0)
    (hR3 : -a * b * d3 + 3 * c * e3 -
        (a * b2 * d2 + a * b3 * ds + a2 * b * d2 + a2 * b2 * ds +
          a3 * b * ds) + 3 * c2 * e2 + 3 * c3 * es + qce = 0) :
    a * b * (b2 * e2 + b3 * es + c2 * d2 + c3 * ds + qB3) +
      c * (-(a * b2 * d2 + a * b3 * ds + a2 * b * d2 + a2 * b2 * ds +
        a3 * b * ds) + 3 * c2 * e2 + 3 * c3 * es + qce) = 0 := by
  linear_combination (a * b) * hR4 + c * hR3 - e3 * hcusp

#print axioms fiveToSix_I4_dZero_e_remainder68
#print axioms fiveToSix_dZero_B_nonconstant_forces_e68
#print axioms fiveToSix_I3_dZero_forced_e68
#print axioms fiveToSix_dZero_B_nonconstant_forces_c68
#print axioms fiveToSix_dZero_forced_residual_rowZero68
#print axioms fiveToSix_dZero_forced_load_rowZero68
#print axioms fiveToSix_dZero_forced_rowZero68
#print axioms coeff_A_derivativeA_B3_top68
#print axioms fiveToSix_dZero_forced_rowZero_gamma_below68
#print axioms fiveToSix_dZero_forced_rowZero_impossible68
#print axioms fiveToSix_dZero_B_nonconstant_impossible68
#print axioms fiveToSix_source_dZero_impossible68
#print axioms coeff_mul_offset_oneTwenty_left_lattice68
#print axioms uniformCuspThirdJetB68_of_le
#print axioms uniformCuspThirdJetB68_of_lt
#print axioms fiveToSix_B3_lt_I4_thirdJet_wall68
#print axioms secondaryResidualInvariantFourPolynomial68_coeff_thirdJet_fiveToSix
#print axioms fiveToSix_uniformCusp_thirdJet_compatibility_scalar68

end FiveToSixTerminalTailThirdJet68

end Max11DegreeRoutes
