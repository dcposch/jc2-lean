import LowScale68ScaleTwoAlignedNonsquareDivisibility

/-! # Degree-`10` Keller coefficient after `p₅ = g H` on aligned
nonsquare `(6,8)`

The unused source row after the aligned second defect is the degree-`10`
Jacobian coefficient.  It mixes `p₃,q₅` with the jet `p₅ = g H`.  This
file extracts that row on the aligned substitutions and evaluates it at
simple roots of `H`.

The exact implication `H³ ∣ 9 q₆ - 7 g²` (equivalently
`H⁵ ∣ evenClearedA68`) does not follow.  The strongest exact H-adic
consequence is first-order vanishing: at every simple root of `H` one
has `g = q₆ = 0`, hence `H ∣ g`, `H ∣ q₆`, and `H ∣ 9 q₆ - 7 g²`,
therefore `H³ ∣ evenClearedA68`.  The next power
`H² ∣ 9 q₆ - 7 g²` is equivalent to `H ∣ p₄`.  That last relation is
not forced by the degree-`10` row.

Degree-specific `(4,6)` residuals, twice-prime arguments, and
total-degree arguments are not used.  The nonsquare hypothesis is
required: a square core makes `H'` vanish at the root and the
degree-`10` evaluation is `0 = 0`.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

section DegreeTenRowAlgebra68

variable {k : Type*} [Field k] [CharZero k]

theorem eval_pow_of_isRoot {H : k[X]} {a : k} {n : ℕ}
    (hn : n ≠ 0) (ha : H.eval a = 0) :
    (H ^ n).eval a = 0 := by
  rw [eval_pow, ha, zero_pow hn]

theorem eval_derivative_pow_of_isRoot {H : k[X]} {a : k} {n : ℕ}
    (hn : 2 ≤ n) (ha : H.eval a = 0) :
    (H ^ n).derivative.eval a = 0 := by
  have hn1 : n - 1 ≠ 0 :=
    Nat.sub_ne_zero_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hn)
  rw [derivative_pow, eval_mul, eval_mul, eval_C, eval_pow, ha, zero_pow hn1]
  simp

theorem eval_derivative_mul_of_left_root {H g : k[X]} {a : k}
    (ha : H.eval a = 0) :
    (H * g).derivative.eval a = H.derivative.eval a * g.eval a := by
  rw [derivative_mul, eval_add, eval_mul, eval_mul, ha, zero_mul, add_zero]

theorem eval_C_mul_g_H_pow_two {c : k} {g H : k[X]} {a : k}
    (ha : H.eval a = 0) :
    (C c * g * H ^ 2).eval a = 0 := by
  rw [eval_mul, eval_mul, eval_C, eval_pow, ha]
  simp

theorem eval_derivative_C_mul_g_H_pow_two {c : k} {g H : k[X]} {a : k}
    (ha : H.eval a = 0) :
    (C c * g * H ^ 2).derivative.eval a = 0 := by
  have hH2 : (H ^ 2).eval a = 0 := eval_pow_of_isRoot (by decide) ha
  have hH2' : (H ^ 2).derivative.eval a = 0 :=
    eval_derivative_pow_of_isRoot (by decide) ha
  rw [mul_assoc, derivative_mul, derivative_C, zero_mul, zero_add,
    eval_mul, eval_C, derivative_mul, eval_add, eval_mul, eval_mul,
    hH2, hH2']
  ring

/-- After the aligned substitutions `p₆ = H³`, `q₈ = H⁴`, `p₅ = g H`,
and `q₇ = (4/3) g H²`, the degree-`10` row evaluates at a root of `H`
to `6 H' g q₆`.  The `p₃` and `q₅` summands are killed by `H³` and
`H⁴`. -/
theorem thirdCoefficientJacobianRow_eval_root_68 {p q : k[X][Y]} {j : k}
    {H g : k[X]} {a : k}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = C (C j))
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (hg : p.coeff 5 = H * g)
    (hq7 : q.coeff 7 = C (4 / 3 : k) * g * H ^ 2)
    (ha : H.eval a = 0) :
    (6 : k) * H.derivative.eval a * g.eval a * (q.coeff 6).eval a = 0 := by
  have hrow := thirdCoefficientJacobianRow_68 hp hq hjac
  have hH3 : (H ^ 3).eval a = 0 := eval_pow_of_isRoot (by decide) ha
  have hH3' : (H ^ 3).derivative.eval a = 0 :=
    eval_derivative_pow_of_isRoot (by decide) ha
  have hH4 : (H ^ 4).eval a = 0 := eval_pow_of_isRoot (by decide) ha
  have hH4' : (H ^ 4).derivative.eval a = 0 :=
    eval_derivative_pow_of_isRoot (by decide) ha
  have hp5 : (H * g).eval a = 0 := by simp [eval_mul, ha]
  have hp5' : (H * g).derivative.eval a =
      H.derivative.eval a * g.eval a :=
    eval_derivative_mul_of_left_root (g := g) ha
  have hq7e : (q.coeff 7).eval a = 0 := by
    simpa [hq7] using eval_C_mul_g_H_pow_two (c := (4 / 3 : k)) (g := g) ha
  have hq7' : (q.coeff 7).derivative.eval a = 0 := by
    simpa [hq7] using
      eval_derivative_C_mul_g_H_pow_two (c := (4 / 3 : k)) (g := g) ha
  have heval := congrArg (fun f : k[X] => f.eval a) hrow
  simp only [eval_add, eval_sub, eval_mul, eval_C, hp6, hq8, hg] at heval
  simp only [hH3, hH3', hH4, hH4', hp5, hp5', hq7e, hq7'] at heval
  simp only [zero_mul, mul_zero, add_zero, zero_add, sub_zero, ha,
    eval_zero] at heval
  have hgoal :
      (6 : k) * H.derivative.eval a * g.eval a * (q.coeff 6).eval a =
        H.derivative.eval a * g.eval a * ((q.coeff 6).eval a * 6) := by
    ring
  rw [hgoal]
  convert heval using 1

/-- Clearing `H²` from the second defect after `p₅ = g H`. -/
theorem nine_q6_sub_two_g_sq_of_secondDefect
    (H a4 a5 b6 g : k[X]) (κ : k) (hH : H ≠ 0)
    (hM : alignedSecondDefect68 H a4 a5 b6 = C κ * H ^ 5)
    (hg : a5 = H * g) :
    (9 : k[X]) * b6 - (2 : k[X]) * g ^ 2 =
      (12 : k[X]) * a4 * H + C κ * H ^ 3 := by
  have hM' :
      (9 : k[X]) * b6 * H ^ 2 - (12 : k[X]) * a4 * H ^ 3 -
          (2 : k[X]) * (H * g) ^ 2 =
        C κ * H ^ 5 := by
    simpa [alignedSecondDefect68, hg] using hM
  have hfac :
      (9 : k[X]) * b6 * H ^ 2 - (12 : k[X]) * a4 * H ^ 3 -
          (2 : k[X]) * (H * g) ^ 2 - C κ * H ^ 5 =
        H ^ 2 *
          ((9 : k[X]) * b6 - (2 : k[X]) * g ^ 2 -
            (12 : k[X]) * a4 * H - C κ * H ^ 3) := by
    ring
  have hzero :
      H ^ 2 *
          ((9 : k[X]) * b6 - (2 : k[X]) * g ^ 2 -
            (12 : k[X]) * a4 * H - C κ * H ^ 3) = 0 := by
    rw [← hfac]
    linear_combination hM'
  have hinner :
      (9 : k[X]) * b6 - (2 : k[X]) * g ^ 2 -
          (12 : k[X]) * a4 * H - C κ * H ^ 3 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 2 hH)
  linear_combination hinner

theorem nine_q6_sub_seven_g_sq_of_secondDefect
    (H a4 a5 b6 g : k[X]) (κ : k) (hH : H ≠ 0)
    (hM : alignedSecondDefect68 H a4 a5 b6 = C κ * H ^ 5)
    (hg : a5 = H * g) :
    (9 : k[X]) * b6 - (7 : k[X]) * g ^ 2 =
      (12 : k[X]) * a4 * H - (5 : k[X]) * g ^ 2 + C κ * H ^ 3 := by
  have h2 := nine_q6_sub_two_g_sq_of_secondDefect H a4 a5 b6 g κ hH hM hg
  linear_combination h2

/-- At a root of `H`, the second defect is `9 q₆ = 2 g²`. -/
theorem nine_q6_eq_two_g_sq_eval_root
    (H a4 a5 b6 g : k[X]) (κ : k) {a : k} (hH : H ≠ 0)
    (hM : alignedSecondDefect68 H a4 a5 b6 = C κ * H ^ 5)
    (hg : a5 = H * g) (ha : H.eval a = 0) :
    (9 : k) * b6.eval a = (2 : k) * (g.eval a) ^ 2 := by
  have hid := nine_q6_sub_two_g_sq_of_secondDefect H a4 a5 b6 g κ hH hM hg
  have heval := congrArg (fun f : k[X] => f.eval a) hid
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_ofNat,
    ha, mul_zero, zero_mul, add_zero, zero_add, sub_zero] at heval
  rw [zero_pow (by decide : (3 : ℕ) ≠ 0), mul_zero] at heval
  exact sub_eq_zero.mp heval

/-- Simple-root evaluation of the degree-`10` row together with the
second defect forces `g(a) = q₆(a) = 0`. -/
theorem degreeTen_simpleRoot_vanishing_68 {p q : k[X][Y]} {j κ : k}
    {H g : k[X]} {a : k}
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = C (C j))
    (hH : H ≠ 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (hg : p.coeff 5 = H * g)
    (hq7 : q.coeff 7 = C (4 / 3 : k) * g * H ^ 2)
    (hM :
      alignedSecondDefect68 H (p.coeff 4) (p.coeff 5) (q.coeff 6) =
        C κ * H ^ 5)
    (ha : H.eval a = 0) (hH' : H.derivative.eval a ≠ 0) :
    g.eval a = 0 ∧ (q.coeff 6).eval a = 0 := by
  have hrow :=
    thirdCoefficientJacobianRow_eval_root_68 hp hq hjac hp6 hq8 hg hq7 ha
  have h6 : (6 : k) ≠ 0 := by norm_num
  have hprod : g.eval a * (q.coeff 6).eval a = 0 := by
    have hscale :
        (6 : k) *
          (H.derivative.eval a * (g.eval a * (q.coeff 6).eval a)) =
            0 := by
      convert hrow using 1
      ring
    have hmid :
        H.derivative.eval a * (g.eval a * (q.coeff 6).eval a) = 0 :=
      (mul_eq_zero.mp hscale).resolve_left h6
    exact (mul_eq_zero.mp hmid).resolve_left hH'
  have hdef :=
    nine_q6_eq_two_g_sq_eval_root H (p.coeff 4) (p.coeff 5) (q.coeff 6) g
      κ hH hM hg ha
  have hg0 : g.eval a = 0 := by
    rcases mul_eq_zero.mp hprod with hg0 | hq0
    · exact hg0
    · have : (2 : k) * (g.eval a) ^ 2 = 0 := by
        rw [← hdef, hq0, mul_zero]
      have h2 : (2 : k) ≠ 0 := by norm_num
      have hsq : g.eval a * g.eval a = 0 := by
        have := (mul_eq_zero.mp this).resolve_left h2
        simpa [pow_two] using this
      exact mul_self_eq_zero.mp hsq
  refine ⟨hg0, ?_⟩
  have : (9 : k) * (q.coeff 6).eval a = 0 := by
    rw [hdef, hg0]
    ring
  have h9 : (9 : k) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp this).resolve_left h9

/-- The source remainder `9 q₆ - 7 g²` after the second defect. -/
theorem nine_q6_sub_seven_g_sq_eval_root
    (H a4 a5 b6 g : k[X]) (κ : k) {a : k} (hH : H ≠ 0)
    (hM : alignedSecondDefect68 H a4 a5 b6 = C κ * H ^ 5)
    (hg : a5 = H * g) (ha : H.eval a = 0) (hg0 : g.eval a = 0) :
    ((9 : k[X]) * b6 - (7 : k[X]) * g ^ 2).eval a = 0 := by
  have hid :=
    nine_q6_sub_seven_g_sq_of_secondDefect H a4 a5 b6 g κ hH hM hg
  rw [hid]
  simp [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_ofNat, ha,
    hg0]

/-- Next-order jet of `9 q₆ - 7 g²` at a root where `g` already vanishes.
The derivative is `12 H' p₄`, so the next H-power is exactly `p₄(a) = 0`. -/
theorem nine_q6_sub_seven_g_sq_derivative_eval_root
    (H a4 a5 b6 g : k[X]) (κ : k) {a : k} (hH : H ≠ 0)
    (hM : alignedSecondDefect68 H a4 a5 b6 = C κ * H ^ 5)
    (hg : a5 = H * g) (ha : H.eval a = 0) (hg0 : g.eval a = 0) :
    ((9 : k[X]) * b6 - (7 : k[X]) * g ^ 2).derivative.eval a =
      (12 : k) * H.derivative.eval a * a4.eval a := by
  have hid :=
    nine_q6_sub_seven_g_sq_of_secondDefect H a4 a5 b6 g κ hH hM hg
  have hder :=
    congrArg (fun f : k[X] => f.derivative.eval a) hid
  have hrhs :
      ((12 : k[X]) * a4 * H - (5 : k[X]) * g ^ 2 +
          C κ * H ^ 3).derivative.eval a =
        (12 : k) * H.derivative.eval a * a4.eval a := by
    simp [derivative_add, derivative_sub, derivative_mul, derivative_sq,
      derivative_pow, derivative_C, C_ofNat_poly, eval_add, eval_sub,
      eval_mul, eval_pow, eval_C, eval_ofNat, ha, hg0]
    ring
  exact hder.trans hrhs

/-- `H³ ∣ evenClearedA68` from the first-order source relation
`H ∣ 9 q₆ - 7 g²`. -/
theorem evenClearedA68_pow3_of_source
    (H a4 a5 b6 g : k[X]) (κ : k) (hH : H ≠ 0)
    (hM : alignedSecondDefect68 H a4 a5 b6 = C κ * H ^ 5)
    (hg : a5 = H * g)
    (hsrc : H ∣ (9 : k[X]) * b6 - (7 : k[X]) * g ^ 2) :
    H ^ 3 ∣ evenClearedA68 H a5 a4 := by
  have hshape := evenClearedA68_of_secondDefect_p5 H a4 a5 b6 g κ hM hg
  have h12unit : IsUnit (C (1 / 12 : k) : k[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by norm_num))
  have hκ : H ∣ C κ * H ^ 3 := ⟨C κ * H ^ 2, by ring⟩
  have hsum :
      H ∣
        ((9 : k[X]) * b6 - (7 : k[X]) * g ^ 2 - C κ * H ^ 3) :=
    dvd_sub hsrc hκ
  have hmid :
      H ∣
        C (1 / 12 : k) *
          ((9 : k[X]) * b6 - (7 : k[X]) * g ^ 2 - C κ * H ^ 3) :=
    (h12unit.dvd_mul_left).mpr hsum
  have hprod :
      H ^ 2 * H ∣
        H ^ 2 *
          (C (1 / 12 : k) *
            ((9 : k[X]) * b6 - (7 : k[X]) * g ^ 2 - C κ * H ^ 3)) :=
    mul_dvd_mul_left _ hmid
  have hpow : H ^ 3 = H ^ 2 * H := by ring
  rw [hpow, hshape]
  exact hprod

end DegreeTenRowAlgebra68

section NonsquareDegreeTwoSimple68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

set_option maxHeartbeats 400000

/-- A degree-`2` nonsquare over an algebraically closed field of
characteristic zero has simple roots.  A double root would make `H` a
polynomial square. -/
theorem nonsquare_natDegree_two_derivative_ne_zero
    {H : k[X]} (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2) {a : k}
    (ha : H.eval a = 0) :
    H.derivative.eval a ≠ 0 := by
  intro hH'
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hmult : 1 < H.rootMultiplicity a :=
    (one_lt_rootMultiplicity_iff_isRoot hH).mpr ⟨ha, hH'⟩
  have hdiv : (X - C a) ^ 2 ∣ H :=
    ((pow_dvd_pow (X - C a)
        (Nat.succ_le_of_lt hmult)).trans (pow_rootMultiplicity_dvd H a))
  obtain ⟨Q, hQ⟩ := hdiv
  have hXne : (X - C a) ^ 2 ≠ 0 :=
    pow_ne_zero _ (X_sub_C_ne_zero a)
  have hQne : Q ≠ 0 := by
    intro hQ0
    exact hH (by simp [hQ, hQ0])
  have hQdeg : Q.natDegree = 0 := by
    have hmul := natDegree_mul hXne hQne
    rw [← hQ, hdeg, natDegree_pow, natDegree_X_sub_C] at hmul
    omega
  rw [eq_C_of_natDegree_eq_zero hQdeg] at hQ
  have hc : Q.coeff 0 ≠ 0 := by
    intro hc0
    have : Q = 0 := by
      rw [eq_C_of_natDegree_eq_zero hQdeg, hc0, C_0]
    exact hQne this
  have hfdeg : ((X : k[X]) ^ 2 - C (Q.coeff 0)).degree ≠ 0 := by
    rw [degree_X_pow_sub_C (by decide : 0 < 2)]
    decide
  obtain ⟨s, hs⟩ :=
    IsAlgClosed.exists_root (X ^ 2 - C (Q.coeff 0)) hfdeg
  have hsq : s ^ 2 = Q.coeff 0 := by
    simpa [sub_eq_zero] using hs
  apply hnsq (C s * (X - C a))
  calc
    H = (X - C a) ^ 2 * C (Q.coeff 0) := hQ
    _ = C (Q.coeff 0) * (X - C a) ^ 2 := by ring
    _ = C (s ^ 2) * (X - C a) ^ 2 := by rw [hsq]
    _ = (C s) ^ 2 * (X - C a) ^ 2 := by rw [map_pow]
    _ = (C s * (X - C a)) ^ 2 := by ring

theorem dvd_of_eval_eq_zero_of_simple_natDegree_two
    {H g : k[X]} (hdeg : H.natDegree = 2)
    (hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0)
    (hg : ∀ a : k, H.eval a = 0 → g.eval a = 0) :
    H ∣ g := by
  classical
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hdeg
  by_cases hg0 : g = 0
  · simp [hg0]
  · refine (IsAlgClosed.splits H).dvd_of_roots_le_roots hH ?_
    refine Multiset.le_iff_count.mpr fun a => ?_
    simp only [count_roots]
    by_cases ha : H.eval a = 0
    · have hpos : 0 < H.rootMultiplicity a :=
        (rootMultiplicity_pos hH).mpr ha
      have hnot : ¬ 1 < H.rootMultiplicity a := by
        intro hlt
        have hboth := (one_lt_rootMultiplicity_iff_isRoot hH).mp hlt
        exact hsimple a ha (IsRoot.eq_zero hboth.2)
      have h1 : H.rootMultiplicity a = 1 := by omega
      have hge : 1 ≤ g.rootMultiplicity a :=
        (rootMultiplicity_pos hg0).mpr (hg a ha)
      simp [h1, hge]
    · have hz : H.rootMultiplicity a = 0 :=
        rootMultiplicity_eq_zero ha
      simp [hz]

/-- After the degree-`10` row, a degree-`2` nonsquare core divides both
`g` and `q₆`. -/
theorem alignedDegreeTen_dvd_g_q6_68 {p q : k[X][Y]} {j : k}
    {H g : k[X]} (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = C (C j))
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (hg : p.coeff 5 = H * g)
    (hq7 : q.coeff 7 = C (4 / 3 : k) * g * H ^ 2)
    {κ : k}
    (hM :
      alignedSecondDefect68 H (p.coeff 4) (p.coeff 5) (q.coeff 6) =
        C κ * H ^ 5) :
    H ∣ g ∧ H ∣ q.coeff 6 := by
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha =>
      nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hvanish : ∀ a : k, H.eval a = 0 →
      g.eval a = 0 ∧ (q.coeff 6).eval a = 0 :=
    fun a ha =>
      degreeTen_simpleRoot_vanishing_68 hp hq hjac hH hp6 hq8 hg hq7 hM
        ha (hsimple a ha)
  exact ⟨
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
      (fun a ha => (hvanish a ha).1),
    dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple
      (fun a ha => (hvanish a ha).2)⟩

theorem alignedDegreeTen_dvd_nine_q6_sub_seven_g_sq_68
    {p q : k[X][Y]} {j : k} {H g : k[X]} (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = C (C j))
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (hg : p.coeff 5 = H * g)
    (hq7 : q.coeff 7 = C (4 / 3 : k) * g * H ^ 2)
    {κ : k}
    (hM :
      alignedSecondDefect68 H (p.coeff 4) (p.coeff 5) (q.coeff 6) =
        C κ * H ^ 5) :
    H ∣ (9 : k[X]) * q.coeff 6 - (7 : k[X]) * g ^ 2 := by
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hdeg
  have ⟨hgdvd, hq6⟩ :=
    alignedDegreeTen_dvd_g_q6_68 hdeg hnsq hp hq hjac hp6 hq8 hg hq7 hM
  have h2 :=
    nine_q6_sub_two_g_sq_of_secondDefect H (p.coeff 4) (p.coeff 5)
      (q.coeff 6) g κ hH hM hg
  have h12H : H ∣ (12 : k[X]) * p.coeff 4 * H :=
    dvd_mul_of_dvd_right dvd_rfl _
  have hκ : H ∣ C κ * H ^ 3 := ⟨C κ * H ^ 2, by ring⟩
  have hleft : H ∣ (9 : k[X]) * q.coeff 6 - (2 : k[X]) * g ^ 2 := by
    rw [h2]
    exact dvd_add h12H hκ
  have hg2 : H ∣ g ^ 2 := dvd_pow hgdvd (by decide : (2 : ℕ) ≠ 0)
  have h5 : H ∣ (5 : k[X]) * g ^ 2 := dvd_mul_of_dvd_right hg2 _
  have hrew :
      (9 : k[X]) * q.coeff 6 - (7 : k[X]) * g ^ 2 =
        ((9 : k[X]) * q.coeff 6 - (2 : k[X]) * g ^ 2) -
          (5 : k[X]) * g ^ 2 := by
    ring
  rw [hrew]
  exact dvd_sub hleft h5

/-- Square-free degree-`2` criterion: `H² ∣ f` if and only if `H`
divides both `f` and `f'`. -/
theorem pow_two_dvd_iff_dvd_derivative_of_simple_natDegree_two
    {H f : k[X]} (hdeg : H.natDegree = 2)
    (hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0) :
    H ^ 2 ∣ f ↔ H ∣ f ∧ H ∣ f.derivative := by
  classical
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hdeg
  constructor
  · intro hpow
    refine ⟨dvd_trans (dvd_pow_self _ (by decide)) hpow, ?_⟩
    obtain ⟨q, hq⟩ := hpow
    refine ⟨(2 : k[X]) * H.derivative * q + H * q.derivative, ?_⟩
    rw [hq, derivative_mul, derivative_sq, C_ofNat_poly]
    ring
  · rintro ⟨hf, hf'⟩
    by_cases hf0 : f = 0
    · simp [hf0]
    · refine (IsAlgClosed.splits (H ^ 2)).dvd_of_roots_le_roots
        (pow_ne_zero 2 hH) ?_
      refine Multiset.le_iff_count.mpr fun a => ?_
      have hcount :
          ((2 : ℕ) • H.roots).count a = 2 * H.roots.count a := by
        rw [two_nsmul, Multiset.count_add, two_mul]
      simp only [count_roots, roots_pow]
      rw [hcount]
      by_cases ha : H.eval a = 0
      · have hpos : 0 < H.rootMultiplicity a :=
          (rootMultiplicity_pos hH).mpr ha
        have hnot : ¬ 1 < H.rootMultiplicity a := by
          intro hlt
          have hboth := (one_lt_rootMultiplicity_iff_isRoot hH).mp hlt
          exact hsimple a ha (IsRoot.eq_zero hboth.2)
        have h1 : H.rootMultiplicity a = 1 := by omega
        have hfroot : f.eval a = 0 := eval_eq_zero_of_dvd_of_eval_eq_zero hf ha
        have hf'dvd := eval_eq_zero_of_dvd_of_eval_eq_zero hf' ha
        have hge : 1 < f.rootMultiplicity a :=
          (one_lt_rootMultiplicity_iff_isRoot hf0).mpr ⟨hfroot, hf'dvd⟩
        simp [h1]
        exact Nat.succ_le_of_lt hge
      · have hz : H.rootMultiplicity a = 0 :=
          rootMultiplicity_eq_zero ha
        simp [hz]

/-- Sharp remaining split: after the degree-`10` first-order vanishing,
`H² ∣ 9 q₆ - 7 g²` if and only if `H ∣ p₄`.  The exact target
`H³ ∣ 9 q₆ - 7 g²` is not reached. -/
theorem alignedDegreeTen_pow2_source_iff_dvd_p4_68
    {p q : k[X][Y]} {j : k} {H g : k[X]} (hdeg : H.natDegree = 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hjac : bivariateJacobian p q = C (C j))
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (hg : p.coeff 5 = H * g)
    (hq7 : q.coeff 7 = C (4 / 3 : k) * g * H ^ 2)
    {κ : k}
    (hM :
      alignedSecondDefect68 H (p.coeff 4) (p.coeff 5) (q.coeff 6) =
        C κ * H ^ 5) :
    H ^ 2 ∣ (9 : k[X]) * q.coeff 6 - (7 : k[X]) * g ^ 2 ↔
      H ∣ p.coeff 4 := by
  have hH : H ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hsimple : ∀ a : k, H.eval a = 0 → H.derivative.eval a ≠ 0 :=
    fun a ha =>
      nonsquare_natDegree_two_derivative_ne_zero hdeg hnsq ha
  have hsrc :=
    alignedDegreeTen_dvd_nine_q6_sub_seven_g_sq_68 hdeg hnsq hp hq hjac
      hp6 hq8 hg hq7 hM
  have ⟨hgdvd, _hq6⟩ :=
    alignedDegreeTen_dvd_g_q6_68 hdeg hnsq hp hq hjac hp6 hq8 hg hq7 hM
  have hiff :=
    pow_two_dvd_iff_dvd_derivative_of_simple_natDegree_two (f :=
        (9 : k[X]) * q.coeff 6 - (7 : k[X]) * g ^ 2)
      hdeg hsimple
  constructor
  · intro hpow
    have hf' : H ∣
        ((9 : k[X]) * q.coeff 6 - (7 : k[X]) * g ^ 2).derivative :=
      (hiff.mp hpow).2
    refine dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple ?_
    intro a ha
    have hg0 : g.eval a = 0 := eval_eq_zero_of_dvd_of_eval_eq_zero hgdvd ha
    have hder :=
      nine_q6_sub_seven_g_sq_derivative_eval_root H (p.coeff 4)
        (p.coeff 5) (q.coeff 6) g κ hH hM hg ha hg0
    have hf'a := eval_eq_zero_of_dvd_of_eval_eq_zero hf' ha
    have h12 : (12 : k) ≠ 0 := by norm_num
    have hscale :
        (12 : k) * (H.derivative.eval a * (p.coeff 4).eval a) = 0 := by
      rw [hder] at hf'a
      convert hf'a using 1
      ring
    have hmid : H.derivative.eval a * (p.coeff 4).eval a = 0 :=
      (mul_eq_zero.mp hscale).resolve_left h12
    exact (mul_eq_zero.mp hmid).resolve_left (hsimple a ha)
  · intro hp4
    refine hiff.mpr ⟨hsrc, ?_⟩
    refine dvd_of_eval_eq_zero_of_simple_natDegree_two hdeg hsimple ?_
    intro a ha
    have hg0 : g.eval a = 0 := eval_eq_zero_of_dvd_of_eval_eq_zero hgdvd ha
    have hder :=
      nine_q6_sub_seven_g_sq_derivative_eval_root H (p.coeff 4)
        (p.coeff 5) (q.coeff 6) g κ hH hM hg ha hg0
    have hp4a := eval_eq_zero_of_dvd_of_eval_eq_zero hp4 ha
    rw [hder, hp4a]
    ring

end NonsquareDegreeTwoSimple68

section QuadraticDegreeTen68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  (H : k[X]) [NonsquarePolynomial46 H]

/-- Source-facing degree-`10` packet: first-order H-adic gain
`H ∣ g`, `H ∣ q₆`, `H ∣ 9 q₆ - 7 g²`, and `H³ ∣ evenClearedA68`.
The remaining A-divisibility `H⁵ ∣ evenClearedA68` is still exactly
`H³ ∣ 9 q₆ - 7 g²`, of which the next (unforced) step is `H ∣ p₄`. -/
theorem NonsquareAlignedSourceCurveData68.degreeTenEvenClearedDvd
    {p q : k[X][X]} {j : k}
    (_S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) :
    ∃ (κ : k) (g : k[X]),
      p.coeff 5 = H * g ∧
        q.coeff 7 = C (4 / 3 : k) * g * H ^ 2 ∧
        alignedSecondDefect68 H (p.coeff 4) (p.coeff 5) (q.coeff 6) =
          C κ * H ^ 5 ∧
        H ∣ g ∧
        H ∣ q.coeff 6 ∧
        H ∣ (9 : k[X]) * q.coeff 6 - (7 : k[X]) * g ^ 2 ∧
        H ^ 3 ∣ evenClearedA68 H (p.coeff 5) (p.coeff 4) ∧
        (H ^ 2 ∣
            (9 : k[X]) * q.coeff 6 - (7 : k[X]) * g ^ 2 ↔
          H ∣ p.coeff 4) ∧
        (H ^ 5 ∣ evenClearedA68 H (p.coeff 5) (p.coeff 4) ↔
          H ^ 3 ∣
            (9 : k[X]) * q.coeff 6 - (7 : k[X]) * g ^ 2) := by
  have hH : H ≠ 0 := H_ne_zero_of_nonsquare68 (H := H)
  have hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2 := NonsquarePolynomial46.not_sq
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_68 hp hq hjac hH hp6 hq8 haligned
  obtain ⟨g, hg⟩ :=
    alignedSecondDefect_dvd_p5_68 hp hq hjac hH hp6 hq8 haligned
  have h3eq :
      (3 : k[X]) * q.coeff 7 = (4 : k[X]) * g * H ^ 2 := by
    have hN : (3 : k[X]) * q.coeff 7 = (4 : k[X]) * p.coeff 5 * H := by
      linear_combination -haligned
    calc
      (3 : k[X]) * q.coeff 7 = (4 : k[X]) * p.coeff 5 * H := hN
      _ = (4 : k[X]) * (H * g) * H := by rw [hg]
      _ = (4 : k[X]) * g * H ^ 2 := by ring
  have h3ne : (3 : k[X]) ≠ 0 := by
    rw [← C_ofNat_poly]
    exact Polynomial.C_ne_zero.mpr (by norm_num)
  have h3scale : (3 : k[X]) * C (4 / 3 : k) = (4 : k[X]) := by
    rw [← C_ofNat_poly (n := 3), ← C_ofNat_poly (n := 4), ← C_mul]
    norm_num
  have hq7 : q.coeff 7 = C (4 / 3 : k) * g * H ^ 2 := by
    apply mul_left_cancel₀ h3ne
    calc
      (3 : k[X]) * q.coeff 7 = (4 : k[X]) * g * H ^ 2 := h3eq
      _ = ((3 : k[X]) * C (4 / 3 : k)) * g * H ^ 2 := by rw [h3scale]
      _ = (3 : k[X]) * (C (4 / 3 : k) * g * H ^ 2) := by ring
  have hgdvd :=
    alignedDegreeTen_dvd_g_q6_68 hdeg hnsq hp hq hjac hp6 hq8 hg hq7 hM
  have hsrc :=
    alignedDegreeTen_dvd_nine_q6_sub_seven_g_sq_68 hdeg hnsq hp hq hjac
      hp6 hq8 hg hq7 hM
  have hA3 :=
    evenClearedA68_pow3_of_source H (p.coeff 4) (p.coeff 5) (q.coeff 6) g
      κ hH hM hg hsrc
  have hiffp4 :=
    alignedDegreeTen_pow2_source_iff_dvd_p4_68 hdeg hnsq hp hq hjac hp6
      hq8 hg hq7 hM
  have hiffA :=
    evenClearedA68_pow5_iff_source H (p.coeff 4) (p.coeff 5) (q.coeff 6)
      g κ hH hM hg
  exact ⟨κ, g, hg, hq7, hM, hgdvd.1, hgdvd.2, hsrc, hA3, hiffp4, hiffA⟩

/-- Residual packet after the degree-`10` row.  The three full
even-cleared divisibilities are not claimed.  Mixed `W ≠ 0` is
untouched. -/
theorem NonsquareAlignedSourceCurveData68.degreeTenPacket
    {p q : k[X][X]} {j : k}
    (S : NonsquareAlignedSourceCurveData68 H p q j)
    (hdeg : H.natDegree = 2)
    (hp : p.natDegree = 6) (hq : q.natDegree = 8)
    (hp6 : p.coeff 6 = H ^ 3) (hq8 : q.coeff 8 = H ^ 4)
    (haligned :
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0)
    (hjac : bivariateJacobian p q = C (C j)) :
    (∃ (κ : k) (g : k[X]),
        p.coeff 5 = H * g ∧
          H ∣ g ∧
          H ∣ q.coeff 6 ∧
          H ∣ (9 : k[X]) * q.coeff 6 - (7 : k[X]) * g ^ 2 ∧
          H ^ 3 ∣ evenClearedA68 H (p.coeff 5) (p.coeff 4) ∧
          (H ^ 2 ∣
              (9 : k[X]) * q.coeff 6 - (7 : k[X]) * g ^ 2 ↔
            H ∣ p.coeff 4) ∧
          (H ^ 5 ∣ evenClearedA68 H (p.coeff 5) (p.coeff 4) ↔
            H ^ 3 ∣
              (9 : k[X]) * q.coeff 6 - (7 : k[X]) * g ^ 2)) := by
  obtain ⟨κ, g, hg, _hq7, _hM, hgdvd, hq6, hsrc, hA3, hiffp4, hiffA⟩ :=
    S.degreeTenEvenClearedDvd (H := H) hdeg hp hq hp6 hq8 haligned hjac
  exact ⟨κ, g, hg, hgdvd, hq6, hsrc, hA3, hiffp4, hiffA⟩

end QuadraticDegreeTen68

section NormalizedDegreeTen68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- Source transport of the degree-`10` first-order jet from a
normalized aligned nonsquare scale-two `(6,8)` source. -/
theorem normalized68ScaleTwo_alignedNonsquare_degreeTenPacket
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized68LeadingCoreSource P Q H 2)
    (hnsq : ∀ h0 : k[X], H ≠ h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (4 : k[X]) * p.coeff 5 * H - (3 : k[X]) * q.coeff 7 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    ∃ (κ : k) (g : k[X]),
      p.coeff 5 = H * g ∧
        H ∣ g ∧
        H ∣ q.coeff 6 ∧
        H ∣ (9 : k[X]) * q.coeff 6 - (7 : k[X]) * g ^ 2 ∧
        H ^ 3 ∣ evenClearedA68 H (p.coeff 5) (p.coeff 4) ∧
        (H ^ 2 ∣ (9 : k[X]) * q.coeff 6 - (7 : k[X]) * g ^ 2 ↔
          H ∣ p.coeff 4) := by
  dsimp only at haligned ⊢
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp6, hq8, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 8 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq8' : q.coeff 8 = H ^ 4 := by simpa only [q] using hq8
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_68 hp hq hjac hH hp6' hq8' haligned
  obtain ⟨g, hg⟩ :=
    alignedSecondDefect_dvd_p5_68 hp hq hjac hH hp6' hq8' haligned
  have h3eq :
      (3 : k[X]) * q.coeff 7 = (4 : k[X]) * g * H ^ 2 := by
    have hN : (3 : k[X]) * q.coeff 7 = (4 : k[X]) * p.coeff 5 * H := by
      linear_combination -haligned
    calc
      (3 : k[X]) * q.coeff 7 = (4 : k[X]) * p.coeff 5 * H := hN
      _ = (4 : k[X]) * (H * g) * H := by rw [hg]
      _ = (4 : k[X]) * g * H ^ 2 := by ring
  have h3ne : (3 : k[X]) ≠ 0 := by
    rw [← C_ofNat_poly]
    exact Polynomial.C_ne_zero.mpr (by norm_num)
  have h3scale : (3 : k[X]) * C (4 / 3 : k) = (4 : k[X]) := by
    rw [← C_ofNat_poly (n := 3), ← C_ofNat_poly (n := 4), ← C_mul]
    norm_num
  have hq7 : q.coeff 7 = C (4 / 3 : k) * g * H ^ 2 := by
    apply mul_left_cancel₀ h3ne
    calc
      (3 : k[X]) * q.coeff 7 = (4 : k[X]) * g * H ^ 2 := h3eq
      _ = ((3 : k[X]) * C (4 / 3 : k)) * g * H ^ 2 := by rw [h3scale]
      _ = (3 : k[X]) * (C (4 / 3 : k) * g * H ^ 2) := by ring
  have hgdvd :=
    alignedDegreeTen_dvd_g_q6_68 hHdegree hnsq hp hq hjac hp6' hq8' hg
      hq7 hM
  have hsrc :=
    alignedDegreeTen_dvd_nine_q6_sub_seven_g_sq_68 hHdegree hnsq hp hq
      hjac hp6' hq8' hg hq7 hM
  have hA3 :=
    evenClearedA68_pow3_of_source H (p.coeff 4) (p.coeff 5) (q.coeff 6) g
      κ hH hM hg hsrc
  have hiffp4 :=
    alignedDegreeTen_pow2_source_iff_dvd_p4_68 hHdegree hnsq hp hq hjac
      hp6' hq8' hg hq7 hM
  exact ⟨κ, g, hg, hgdvd.1, hgdvd.2, hsrc, hA3, hiffp4⟩

end NormalizedDegreeTen68

#print axioms thirdCoefficientJacobianRow_eval_root_68
#print axioms degreeTen_simpleRoot_vanishing_68
#print axioms evenClearedA68_pow3_of_source
#print axioms nonsquare_natDegree_two_derivative_ne_zero
#print axioms alignedDegreeTen_dvd_g_q6_68
#print axioms alignedDegreeTen_dvd_nine_q6_sub_seven_g_sq_68
#print axioms alignedDegreeTen_pow2_source_iff_dvd_p4_68
#print axioms NonsquareAlignedSourceCurveData68.degreeTenEvenClearedDvd
#print axioms NonsquareAlignedSourceCurveData68.degreeTenPacket
#print axioms normalized68ScaleTwo_alignedNonsquare_degreeTenPacket

end Max11DegreeRoutes
